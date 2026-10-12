type rotor = {
  wiring : string;
  turnover : char;
}

type oriented_rotor = {
  rotor : rotor;
  top_letter : char;
}

type config = {
  refl : string;
  rotors : oriented_rotor list;
  plugboard : (char * char) list;
}

(** [wrap n] is [n] reduced into the range [0] through [25]. Unlike
    [n mod 26], it is never negative. *)
let wrap n = ((n mod 26) + 26) mod 26

let index c = Char.code c - Char.code 'A'

(** [letter_of_index i] is the uppercase letter at position [i] of the
    alphabet. Requires: [i] is in [0] through [25]. *)
let letter_of_index i = Char.chr (i + Char.code 'A')

(** [next_letter c] is the letter following [c], wrapping ['Z'] around
    to ['A']. Requires: [c] is an uppercase letter. *)
let next_letter c = letter_of_index (wrap (index c + 1))

let map_r_to_l wiring top_letter input_pos =
  let offset = index top_letter in
  let contact = wrap (input_pos + offset) in
  let wired_contact = index wiring.[contact] in
  wrap (wired_contact - offset)

let map_l_to_r wiring top_letter input_pos =
  let offset = index top_letter in
  let contact = wrap (input_pos + offset) in
  let wired_contact = String.index wiring (letter_of_index contact) in
  wrap (wired_contact - offset)

let map_refl wiring input_pos = map_r_to_l wiring 'A' input_pos

let rec map_plug plugs c =
  match plugs with
  | [] -> c
  | (a, b) :: rest ->
      if c = a then b else if c = b then a else map_plug rest c

(** [through_rotors map rotors pos] sends [pos] through [rotors] in the
    order given, applying [map wiring top_letter pos] at each rotor. *)
let rec through_rotors map rotors pos =
  match rotors with
  | [] -> pos
  | { rotor; top_letter } :: rest ->
      through_rotors map rest (map rotor.wiring top_letter pos)

(** [map_rotors_r_to_l rotors pos] is the position after current enters
    the rightmost rotor of [rotors] at [pos] and leaves the leftmost.
    [rotors] is listed from left to right, so it is traversed from
    the end. *)
let map_rotors_r_to_l rotors pos =
  through_rotors map_r_to_l (List.rev rotors) pos

(** [map_rotors_l_to_r rotors pos] is the position after current enters
    the leftmost rotor of [rotors] at [pos] and leaves the rightmost. *)
let map_rotors_l_to_r rotors pos = through_rotors map_l_to_r rotors pos

let cipher_char config c =
  c
  |> map_plug config.plugboard
  |> index
  |> map_rotors_r_to_l config.rotors
  |> map_refl config.refl
  |> map_rotors_l_to_r config.rotors
  |> letter_of_index
  |> map_plug config.plugboard

(** [advance oriented] is [oriented] with its rotor turned by one
    position. *)
let advance oriented =
  { oriented with top_letter = next_letter oriented.top_letter }

(** [at_turnover oriented] is [true] iff [oriented] currently shows its
    turnover letter. *)
let at_turnover { rotor; top_letter } = top_letter = rotor.turnover

(** [step_rotors is_leftmost rotors] is [rotors] after one stepping
    event. [rotors] is listed from left to right, and [is_leftmost] says
    whether its first element is the leftmost rotor of the machine.
    The last rotor always steps. Any other rotor steps if the rotor to
    its right shows its turnover letter, or if it is not the leftmost
    and shows its own turnover letter. Each rotor steps at most once. *)
let rec step_rotors is_leftmost rotors =
  match rotors with
  | [] -> []
  | [ last ] -> [ advance last ]
  | rotor :: (right :: _ as rest) ->
      let steps =
        at_turnover right || ((not is_leftmost) && at_turnover rotor)
      in
      (if steps then advance rotor else rotor)
      :: step_rotors false rest

let step config = { config with rotors = step_rotors true config.rotors }

(** [cipher_chars config chars] enciphers [chars], stepping [config]
    before each character. *)
let rec cipher_chars config chars =
  match chars with
  | [] -> []
  | c :: rest ->
      let stepped = step config in
      cipher_char stepped c :: cipher_chars stepped rest

let cipher config s =
  s |> String.to_seq |> List.of_seq |> cipher_chars config
  |> List.to_seq |> String.of_seq

let hours_worked = 5
