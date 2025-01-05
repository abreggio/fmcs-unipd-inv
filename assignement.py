import pynusmv
import sys
from pynusmv.dd import State, Inputs

def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def check_explain_inv_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ennding with a state. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    str_trace = None
    model = pynusmv.glob.prop_database().master.bddFsm
    bdd_inv = spec_to_bdd(model, spec)
    reach = compute_reach(model)
    res = bdd_inv >= reach
    if not res:
        tail_head = reach - bdd_inv
        trace = compute_trace(model, tail_head)
        str_trace = [State.get_str_values(x) if not y & 1 else Inputs.get_str_values(x) for x,y in zip(trace, range(len(trace)))]
    
    return res, str_trace

def compute_reach(model):
    reach = model.init
    n = reach

    empty = pynusmv.dd.BDD.false(model)

    while not (n == empty):
        n = model.post(n) - reach
        reach += n

    return reach

def compute_trace(model, tail_head):
    tail_list = [model.init] + recur_tail(model, model.init, model.init, tail_head)
    tail = build_tail(model, tail_list, tail_list[-1])
    return tail

def build_tail(model, tail_list, head):
    if model.init >= head:
        return []
    else:
        pre_list = tail_list[:-1]
        pre_states = pre_list[-1]
        tail_head = model.pick_one_state(head)
        pre_states = pre_states & model.pre(tail_head)
        pre_state = model.pick_one_state(pre_states)
        inputs = model.get_inputs_between_states(pre_state, tail_head)
        if not model.init >= pre_state:
            return build_tail(model, pre_list, pre_state) + [model.pick_one_inputs(inputs), tail_head]
        else:
            return [pre_state, model.pick_one_inputs(inputs), tail_head]

def recur_tail(model, reach, frontier, tail_head):
    frontier_next = model.post(frontier) - reach
    reach_next = reach + frontier_next
    head = frontier_next & tail_head
    if head.is_false():
        return [frontier_next] + recur_tail(model, reach_next, frontier_next, tail_head)
    else:
        return [head]



if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
    pynusmv.glob.compute_model()
    invtype = pynusmv.prop.propTypes['Invariant']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        if prop.type == invtype:
            print("Property", spec, "is an INVARSPEC.")
            res, trace = check_explain_inv_spec(spec)
            if res == True:
                print("Invariant is respected")
            else:
                print("Invariant is not respected")
                print(trace)
        else:
            print("Property", spec, "is not an INVARSPEC, skipped.")

    pynusmv.init.deinit_nusmv()
