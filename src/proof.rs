#[derive(Debug, PartialEq, Eq)]
pub enum Proof {
    Plain(Vec<String>),
    Compressed(Vec<String>, String),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Step<'s> {
    Label(&'s str),
    ToHeap,
    FromHeap(usize),
}

impl Proof {
    pub fn plain<'s>(
        &'s self,
        mandatory_hypotheses: &'s [&'s str],
    ) -> Box<dyn Iterator<Item = Step<'s>> + 's> {
        let (labels, digits) = match self {
            Proof::Plain(items) => {
                return Box::new(items.iter().map(|s| s.as_str()).map(Step::Label))
            }
            Proof::Compressed(labels, digits) => (labels, digits),
        };

        let items = mandatory_hypotheses
            .into_iter()
            .map(|s| *s)
            .chain(labels.iter().map(|s| s.as_str()))
            .collect::<Vec<_>>();

        Box::new(digits.chars().map(move |c| {
            if c == 'Z' {
                return Step::ToHeap;
            }

            let index = c as usize - 'A' as usize;

            if index < items.len() {
                Step::Label(items[index])
            } else {
                Step::FromHeap(index - items.len())
            }
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod compressed {
        use super::*;

        fn compressed<L: AsRef<str>>(
            labels: impl IntoIterator<Item = L>,
            digits: impl AsRef<str>,
        ) -> Proof {
            Proof::Compressed(
                labels.into_iter().map(|s| s.as_ref().to_string()).collect(),
                digits.as_ref().to_string(),
            )
        }

        #[test]
        fn empty() {
            let proof = compressed::<&str>([], "");
            let mut iter = proof.plain(&[]);
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn extracts_first_label() {
            let proof = compressed(["foo"], "A");
            let mut iter = proof.plain(&[]);
            assert_eq!(iter.next(), Some(Step::Label("foo")));
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn extracts_only_second_label() {
            let proof = compressed(["foo", "bar"], "B");
            let mut iter = proof.plain(&[]);
            assert_eq!(iter.next(), Some(Step::Label("bar")));
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn extracts_from_hypotheses() {
            let proof = compressed(["foo", "bar"], "A");
            let mut iter = proof.plain(&["hypo"]);
            assert_eq!(iter.next(), Some(Step::Label("hypo")));
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn to_heap() {
            let proof = compressed(["foo", "bar"], "AZ");
            let mut iter = proof.plain(&[]);
            assert_eq!(iter.next(), Some(Step::Label("foo")));
            assert_eq!(iter.next(), Some(Step::ToHeap));
            assert_eq!(iter.next(), None);
        }

        #[test]
        fn from_heap() {
            let proof = compressed(["foo", "bar"], "AZC");
            let mut iter = proof.plain(&[]);
            assert_eq!(iter.next(), Some(Step::Label("foo")));
            assert_eq!(iter.next(), Some(Step::ToHeap));
            assert_eq!(iter.next(), Some(Step::FromHeap(0)));
            assert_eq!(iter.next(), None);
        }
    }
}
