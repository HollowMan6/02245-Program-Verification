#![feature(box_patterns)] // experimental convenience feature

use prusti_contracts::*;

struct Node {
    elem: i32,
    next: List,
}

enum List {
    Empty,
    More(Box<Node>),
}

impl List {
    #[pure]
    #[ensures(result >= 0)]
    fn len(&self) -> usize {
        match self {
            List::Empty => 0,
            List::More(box node) => 1 + node.next.len(),
        }
    }

    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        match self {
            List::Empty => unreachable!(),
            List::More(box node) => {
                if index == 0 {
                    node.elem
                } else {
                    node.next.lookup(index - 1)
                }
            },
        }
    }

    #[ensures(result.len() == self.len())]
    #[ensures(forall(|i: usize| (0 <= i && i < result.len()) ==>
                result.lookup(i) == self.lookup(i)))]
    pub fn cloneList(&self) -> List {
        match self {
            List::Empty => List::Empty,
            List::More(box node) => {
                let new_node = Box::new(Node {
                    elem: node.elem,
                    next: node.next.cloneList(),
                });
                List::More(new_node)
            }
        }       
    }

    #[ensures(result.len() == self.len() + that.len())]
    pub fn zip(&self, that: &List) -> List {
        match self {
            List::Empty => that.cloneList(),
            List::More(box node) => {
                let new_node = Box::new(Node {
                    elem: node.elem,
                    next: that.zip(&node.next),
                });
                List::More(new_node)
            }
        }  
    }
}

#[ensures(l.len() == old(l.len()))]
fn client(l: List) {
    let z = l.zip(&l);
    assert!(z.len() == 2*l.len());
}