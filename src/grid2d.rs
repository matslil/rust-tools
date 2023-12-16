#[derive(PartialEq, Eq, Debug)]
pub struct Grid2D<T> {
    grid: Vec<Vec<T>>,
}

impl<T> Grid2D<T> {
    pub fn new(
        lines: &mut dyn Iterator<Item=&str>,
        translations: std::collections::HashMap<char, T>) -> Self
        where T: Clone + std::fmt::Display {
            Self{ grid: lines.take_while(|s| *s != "").map(|s| {
                s.chars().map(|c| translations[&c].clone()).collect::<Vec<T>>()
            })
            .collect::<Vec<Vec<T>>>()
            }
    }

    pub fn rows(&self) -> usize {
        self.grid.len()
    }

    pub fn cols(&self) -> usize {
        if let Some(col) = self.grid.get(0) {
            col.len()
        } else {
            0
        }
    }
}

impl<T: std::fmt::Display> std::fmt::Display for Grid2D<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if f.alternate() {
            let row_digits: usize = (self.rows().checked_ilog10().unwrap_or(0) + 1) as usize;
            for (row_idx, row) in self.grid.iter().enumerate() {
                for cell in row {
                    write!(f, "{0:1$} {2}", row_idx, row_digits, *cell)?;
                }
                write!(f, "\n")?;
            }
        } else {
            for row in self.grid.iter() {
                for cell in row {
                    write!(f, "{}", *cell)?;
                }
                write!(f, "\n")?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod grid2d {
    use super::*;
    const TEST_MAP: &str = concat!(
        "...X...X\n",
        "..X..X..\n",
        ".X..X..X\n",
        "X..X..X.\n",
        "..X..X..\n",
        ".X..X..X\n");

    #[derive(PartialEq, Eq, Clone)]
    enum TestCell {
        occupied,
        not_occupied,
    }

    impl std::fmt::Display for TestCell {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", match self {
                TestCell::occupied => '#',
                TestCell::not_occupied => '.',
            })
        }
    }

    #[test]
    fn new() {
        let sut = Grid2D::new(&mut TEST_MAP.lines(),
            std::collections::HashMap::from([
                ('.', false),
                ('X', true)
            ]));
        let correct_answer: Vec<Vec<bool>> = vec![
            [false, false, false, true, false, false, false, true].to_vec(),
            [false, false, true, false, false, true, false, false].to_vec(),
            [false, true, false, false, true, false, false,  true].to_vec(),
            [true, false, false, true, false, false, true, false].to_vec(),
            [false, false, true, false, false, true, false, false].to_vec(),
            [false, true, false, false, true, false, false, true].to_vec(),
        ];
        println!("{}", sut);
        for (y, rows) in std::iter::zip(correct_answer.iter(), sut.grid.iter()).enumerate() {
            for (x, cells) in std::iter::zip(rows.0.iter(), rows.1.iter()).enumerate() {
                assert!(cells.0 == cells.1, "Mismatch at ({}, {})", x, y);
            }
        }
    }

    #[test]
    fn display() {
        let grid = [
            [TestCell::occupied, TestCell::not_occupied, TestCell::occupied ],
            [TestCell::not_occupied, TestCell::not_occupied, TestCell::not_occupied],
            [TestCell::occupied, TestCell::occupied, TestCell::not_occupied],
        ];
        let correct_answer = concat!(
            "#.#\n",
            "...\n",
            "##.\n",
        );
        let correct_alternate_answer = concat!(
            "0 #.#\n",
            "1 ...\n",
            "2 ##.\n",
        );
        let sut = Grid2D::new(
                &mut correct_answer.lines(),
                std::collections::HashMap::from([
                    ('#', TestCell::occupied),
                    ('.', TestCell::not_occupied),
                ]));

        let sut_display = format!("{}", sut);
        assert!(correct_answer == sut_display,
            "Expected: \n{}\nGot:\n{}", correct_answer, sut_display);
        let sut_alternate_display = format!("{:#}", sut);
        assert!(correct_answer == sut_display,
            "Expected: \n{}\nGot:\n{}", correct_alternate_answer, sut_alternate_display);
    }
}

