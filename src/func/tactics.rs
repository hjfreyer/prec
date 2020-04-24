use super::actions::*;
use super::*;
use crate::base;
use crate::base::Action as _;

impl base::Tactic<Action> for Action {
    fn react(&self, func: &Func) -> Option<base::ActionChain<Action>> {
        let rewritten = self.act(func.clone()).ok()?;
        Some(base::ActionChain {
            start: rewritten,
            actions: im::vector![Action::Inverse(func.clone(), Box::new(self.clone()))],
        })
    }
}
