use std::cmp::min;
use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;
use std::str;

use errors::Error;

pub struct FileContents {
    data: String,
    filenames: Vec<(usize, String)>,
    newlines: Vec<(usize, usize)>,
}

fn mark_newlines(offset: usize, newlines_list: &mut Vec<(usize, usize)>, data: &str) {
    newlines_list.push((offset, 1));
    let mut index = 1;
    for (i, _) in data.match_indices('\n') {
        index += 1;
        newlines_list.push((offset + i + 1, index));
    }
}

impl FileContents {
    pub fn new_from_data(preamble: &str, user_data: &str, filename: &str) -> FileContents {
        let mut newlines = Vec::new();
        let mut contents = String::from(preamble);
        mark_newlines(0, &mut newlines, &contents);
        contents.push_str(user_data);
        mark_newlines(preamble.len(), &mut newlines, contents.split_at(preamble.len()).1);
        let filenames = vec!(
            (0, String::from("<builtin>")),
            (preamble.len(), String::from(filename))
        );
        FileContents {
            data: contents,
            filenames: filenames,
            newlines: newlines,
        }
    }
    pub fn new_from_file_with_preamble(preamble: &str, path: &Path) -> Result<FileContents, Error> {
        let file = File::open(path)?;
        let mut file_reader = BufReader::new(file);
        let filename = path.file_name().map(|x| x.to_string_lossy().into_owned()).unwrap_or(String::from("<unknown>"));
        let mut file_bytes = Vec::new();
        file_reader.read_to_end(&mut file_bytes)?;
        match str::from_utf8(&file_bytes) {
            Ok(_) => {},
            Err(_) => {
                warn!("input file {} is not valid UTF-8", filename);
            },
        };
        Ok(FileContents::new_from_data(preamble, &String::from_utf8_lossy(&file_bytes), &filename))
    }

    pub fn new_from_file(path: &Path) -> Result<FileContents, Error> {
        FileContents::new_from_file_with_preamble("\n", path)
    }

    pub fn data(&self) -> &str { &self.data }

    pub fn filename(&self, index: usize) -> &str {
        let index = match self.filenames.binary_search_by_key(&index, |ref x| x.0) {
            Ok(x) => x,
            Err(x) => x - 1
        };
        &self.filenames[index].1
    }

    pub fn line_number_and_bounds(&self, index: usize) -> (usize, usize, usize) {
        let index = match self.newlines.binary_search_by_key(&index, |ref x| x.0) {
            Ok(x) => x,
            Err(x) => x - 1
        };
        let next_line_loc = if index == self.newlines.len() - 1 { self.data.len() } else { self.newlines[index + 1].0 };
        let cur_line = self.newlines[index];
        (cur_line.1, cur_line.0, next_line_loc)
    }

    pub fn line(&self, index: usize) -> usize {
        self.line_number_and_bounds(index).1
    }

    pub fn file_and_line(&self, index: usize) -> String {
        let filename = self.filename(index);
        let line = self.line(index);
        format!("{}:{}", filename, line)
    }

    pub fn range(&self, start: usize, end: usize) -> String {
        let filename = self.filename(start);
        let start_line = self.line(start);
        let end_line = self.line(end);
        if start_line == end_line {
            format!("{}:{}", filename, start_line)
        } else {
            format!("{}:{}-{}", filename, start_line, end_line)
        }
    }

    pub fn show_region(&self, start: usize, end: usize) -> String {
        let end = min(end, self.data.len().saturating_sub(1));
        let start = min(start, end);
        let filename = self.filename(start);
        let (begin_line_no, begin_loc, _) = self.line_number_and_bounds(start);
        let (end_line_no, begin_last_line, end_loc) = self.line_number_and_bounds(end);
        let end_loc = min(end_loc, self.data.len().saturating_sub(1));

        debug!("range is {}-{}", begin_loc, end_loc);

        let begin_line_offset = start - begin_loc;
        let end_line_offset = end - begin_last_line;

        let segment = &self.data[begin_loc..end_loc];
        let mut result = String::new();
        // FIXME: variable width line count
        // FIXME: ascii art!
        // FIXME: color?
        result.push_str(&format!("     -> {}:{}\n", filename, begin_line_no));
        result.push_str(         "     |\n");
        let mut number = begin_line_no;
        debug!("segment : {:?}", segment);
        for line in segment.lines() {
            let this_start = if number == begin_line_no { begin_line_offset } else { 0 };
            let this_end = if number == end_line_no { end_line_offset } else { line.len() };
            result.push_str(&format!("{:>4} | {}\n", number, line));
            result.push_str(&format!("     | {}{}\n",
                " ".repeat(this_start),
                "^".repeat(this_end - this_start)));
            number += 1;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::tests::init_logger;

    #[test]
    fn show_region_1() {
        init_logger();
        let test_file =
"This is the first line.
This is the second line.
This is the third line.";
        let contents = FileContents::new_from_data("\n", test_file, "example.name");
        let first_loc = contents.data().find("first").unwrap();
        let line_loc = contents.data().find(".").unwrap();
        assert_eq!(&contents.data()[first_loc..line_loc], "first line");

        let reference =
"     -> example.name:1
     |
   1 | This is the first line.
     |             ^^^^^^^^^^
";
        let actual = contents.show_region(first_loc, line_loc);
        debug!("reference:\n{}actual:\n{}", reference, actual);
        assert_eq!(actual, reference);
    }

    #[test]
    fn show_region_2() {
        init_logger();
        let test_file =
"This is the first line.
This is the second line.
This is the third line.";
        let contents = FileContents::new_from_data("\n", test_file, "example.name");
        let first_loc = contents.data().find("second").unwrap();
        let line_loc = contents.data().find("second line.").unwrap() + 11;

        let reference =
"     -> example.name:2
     |
   2 | This is the second line.
     |             ^^^^^^^^^^^
";
        let actual = contents.show_region(first_loc, line_loc);
        debug!("reference:\n{}actual:\n{}", reference, actual);
        assert_eq!(actual, reference);
    }
}
