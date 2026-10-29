(** Limits that the tests lower from the environment. A lower limit can only make the checker do
    more work or give up sooner, never accept what it would refuse: the work budget turns accepts
    into declines, the cache limit empties the caches more often, the two size limits of the
    arithmetic shortcuts (WARRANT_MAX_POW, WARRANT_MAX_BITS) refuse more, and the hash mask makes
    the hash-consing tables collide more often (so that the equality tests that tell colliding terms
    apart are what decides, not luck). A value that is not a natural number is ignored, and a value
    above the default is cut to it. *)

let limit name default =
  match Option.bind (Sys.getenv_opt name) int_of_string_opt with
  | Some n when n >= 0 -> min n default
  | _ -> default
