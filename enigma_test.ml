open OUnit2
open Enigma

(* ---------- Historical data used by the tests ---------- *)

let identity = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let swap_ab = "BACDEFGHIJKLMNOPQRSTUVWXYZ"
let wiring_i = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let wiring_ii = "AJDKSIRUXBLHWTMCQGZNPYFVOE"
let wiring_iii = "BDFHJLCPRTXVZNYEIWGAKMUSQO"
let reflector_b = "YRUHQSLDPXNGOKMIEBFZCWVJAT"
let reflector_c = "FVPJIAOYEDRZXWGCTKUQSBNMHL"

let rotor_i = { wiring = wiring_i; turnover = 'Q' }
let rotor_ii = { wiring = wiring_ii; turnover = 'E' }
let rotor_iii = { wiring = wiring_iii; turnover = 'V' }

(* ---------- Helpers to build configurations ---------- *)

(** [oriented rotor top_letter] is [rotor] turned to show [top_letter]. *)
let oriented rotor top_letter = { rotor; top_letter }

(** [config refl rotors plugboard] builds a configuration. *)
let config refl rotors plugboard = { refl; rotors; plugboard }

(** [standard tops plugboard] is reflector B with rotors I, II, III
    (left to right) showing the three letters of [tops]. *)
let standard tops plugboard =
  config reflector_b
    [
      oriented rotor_i tops.[0];
      oriented rotor_ii tops.[1];
      oriented rotor_iii tops.[2];
    ]
    plugboard

(** [reversed tops] is reflector B with rotors III, II, I (left to right)
    showing the three letters of [tops], as in the stepping examples. *)
let reversed tops =
  config reflector_b
    [
      oriented rotor_iii tops.[0];
      oriented rotor_ii tops.[1];
      oriented rotor_i tops.[2];
    ]
    []

(** [tops_of config] is the string of top letters of [config]'s rotors,
    from left to right. *)
let tops_of config =
  config.rotors
  |> List.map (fun oriented -> oriented.top_letter)
  |> List.to_seq |> String.of_seq

(* ---------- Test builders ---------- *)

let index_test name input expected =
  name >:: fun _ -> assert_equal ~printer:string_of_int expected (index input)

let r_to_l_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
  assert_equal ~printer:string_of_int expected
    (map_r_to_l wiring top_letter input_pos)

let l_to_r_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
  assert_equal ~printer:string_of_int expected
    (map_l_to_r wiring top_letter input_pos)

let refl_test name wiring input_pos expected =
  name >:: fun _ ->
  assert_equal ~printer:string_of_int expected (map_refl wiring input_pos)

let plug_test name plugs input expected =
  name >:: fun _ ->
  assert_equal ~printer:Char.escaped expected (map_plug plugs input)

let cipher_char_test name config input expected =
  name >:: fun _ ->
  assert_equal ~printer:Char.escaped expected (cipher_char config input)

let step_test name config expected_tops =
  name >:: fun _ ->
  assert_equal ~printer:(fun s -> s) expected_tops (tops_of (step config))

let cipher_test name config input expected =
  name >:: fun _ ->
  assert_equal ~printer:(fun s -> s) expected (cipher config input)

(** [steps_test name config n expected_tops] steps [config] [n] times. *)
let repeated_step_test name config n expected_tops =
  let rec repeat k c = if k = 0 then c else repeat (k - 1) (step c) in
  name >:: fun _ ->
  assert_equal ~printer:(fun s -> s) expected_tops (tops_of (repeat n config))

(** [roundtrip_test name config plaintext] checks that enciphering the
    ciphertext from the same initial [config] gives back [plaintext]. *)
let roundtrip_test name config plaintext =
  name >:: fun _ ->
  assert_equal ~printer:(fun s -> s) plaintext
    (cipher config (cipher config plaintext))

(* ---------- Machines reused across tests ---------- *)

let empty_machine = config identity [] []
let machine_aaa = standard "AAA" []
let all_letters = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

(** [cipher_each config] is every letter of the alphabet passed through
    [cipher_char config]. *)
let cipher_each config =
  all_letters |> String.to_seq |> List.of_seq
  |> List.map (cipher_char config)
  |> List.to_seq |> String.of_seq

let cipher_each_test name config expected =
  name >:: fun _ ->
  assert_equal ~printer:(fun s -> s) expected (cipher_each config)

(* ---------- Test suites ---------- *)

let index_tests =
  [
    index_test "index of A is 0" 'A' 0;
    index_test "index of B is 1" 'B' 1;
    index_test "index of M is 12" 'M' 12;
    index_test "index of N is 13" 'N' 13;
    index_test "index of Z is 25" 'Z' 25;
  ]

let r_to_l_tests =
  [
    r_to_l_test "identity wiring, top A, position 0 stays 0" identity 'A' 0 0;
    r_to_l_test "identity wiring ignores rotation at position 5" identity 'C'
      5 5;
    r_to_l_test "swap AB wiring, top A, position 0 goes to 1" swap_ab 'A' 0 1;
    r_to_l_test "swap AB wiring, top B, position 0 wraps around to 25" swap_ab
      'B' 0 25;
    r_to_l_test "swap AB wiring, top C, position 0 stays 0" swap_ab 'C' 0 0;
    r_to_l_test "rotor I, top A, position 0 goes to 4" wiring_i 'A' 0 4;
    r_to_l_test "rotor I, top B, position 0 goes to 9" wiring_i 'B' 0 9;
    r_to_l_test "rotor I, top Z, position 25 goes to 3" wiring_i 'Z' 25 3;
    r_to_l_test "rotor II, top M, position 7 goes to 1" wiring_ii 'M' 7 1;
    r_to_l_test "rotor III, top A, position 25 goes to 14" wiring_iii 'A' 25 14;
    r_to_l_test "rotor III, top O, position 14 goes to 17" wiring_iii 'O' 14 17;
  ]

let l_to_r_tests =
  [
    l_to_r_test "identity wiring, top A, position 0 stays 0" identity 'A' 0 0;
    l_to_r_test "identity wiring ignores rotation at position 5" identity 'C'
      5 5;
    l_to_r_test "swap AB wiring is its own inverse at position 0" swap_ab 'A'
      0 1;
    l_to_r_test "swap AB wiring, top B, position 0 wraps around to 25" swap_ab
      'B' 0 25;
    l_to_r_test "rotor I, top A, position 0 goes to 20" wiring_i 'A' 0 20;
    l_to_r_test "rotor I, top B, position 0 goes to 21" wiring_i 'B' 0 21;
    l_to_r_test "rotor I, top Z, position 25 goes to 15" wiring_i 'Z' 25 15;
    l_to_r_test "rotor I, top F, position 10 goes to 14" wiring_i 'F' 10 14;
    l_to_r_test "rotor III, top A, position 25 goes to 12" wiring_iii 'A' 25 12;
    "left-to-right undoes right-to-left for every position"
    >:: (fun _ ->
    let positions = List.init 26 (fun i -> i) in
    let round_trip pos =
      map_l_to_r wiring_ii 'K' (map_r_to_l wiring_ii 'K' pos)
    in
    assert_equal positions (List.map round_trip positions));
  ]

let refl_tests =
  [
    refl_test "identity reflector maps 0 to 0" identity 0 0;
    refl_test "identity reflector maps 1 to 1" identity 1 1;
    refl_test "identity reflector maps 25 to 25" identity 25 25;
    refl_test "reflector B maps A to Y" reflector_b 0 24;
    refl_test "reflector B maps Y to A" reflector_b 24 0;
    refl_test "reflector B maps B to R" reflector_b 1 17;
    refl_test "reflector C maps A to F" reflector_c 0 5;
    refl_test "reflector C maps Z to L" reflector_c 25 11;
    "reflector B is symmetric"
    >:: (fun _ ->
    let positions = List.init 26 (fun i -> i) in
    let twice pos = map_refl reflector_b (map_refl reflector_b pos) in
    assert_equal positions (List.map twice positions));
  ]

let plug_tests =
  [
    plug_test "empty plugboard leaves M unchanged" [] 'M' 'M';
    plug_test "plugboard AZ maps A to Z" [ ('A', 'Z') ] 'A' 'Z';
    plug_test "plugboard AZ maps Z to A" [ ('A', 'Z') ] 'Z' 'A';
    plug_test "plugboard AZ leaves M unchanged" [ ('A', 'Z') ] 'M' 'M';
    plug_test "two cables map X to Y" [ ('A', 'Z'); ('X', 'Y') ] 'X' 'Y';
    plug_test "two cables map Y to X" [ ('A', 'Z'); ('X', 'Y') ] 'Y' 'X';
    plug_test "two cables map A to Z" [ ('A', 'Z'); ('X', 'Y') ] 'A' 'Z';
    plug_test "two cables leave Q unchanged" [ ('A', 'Z'); ('X', 'Y') ] 'Q' 'Q';
    plug_test "reversed pair order gives the same mapping"
      [ ('Y', 'X'); ('Z', 'A') ]
      'A' 'Z';
    plug_test "reversed cable order gives the same mapping"
      [ ('Y', 'X'); ('Z', 'A') ]
      'Y' 'X';
  ]

let cipher_char_tests =
  [
    cipher_char_test "no rotors and identity reflector maps A to A"
      empty_machine 'A' 'A';
    cipher_char_test "no rotors and identity reflector maps Z to Z"
      empty_machine 'Z' 'Z';
    cipher_char_test "reflector B alone maps A to Y"
      (config reflector_b [] [])
      'A' 'Y';
    cipher_char_test "rotors I II III at AAA map G to P" machine_aaa 'G' 'P';
    cipher_char_test "rotors I II III at AAA map A to U" machine_aaa 'A' 'U';
    cipher_char_test "rotors I II III at AAA map Z to H" machine_aaa 'Z' 'H';
    cipher_char_test "plugboard AZ and XY change A at AAA"
      (standard "AAA" [ ('A', 'Z'); ('X', 'Y') ])
      'A' 'H';
    cipher_char_test "plugboard GQ changes G at AAA"
      (standard "AAA" [ ('G', 'Q') ])
      'G' 'V';
    cipher_char_test "different top letters give a different result"
      (standard "CDE" [])
      'Z' 'H';
    cipher_char_test "single rotor III at Z maps M to X"
      (config reflector_b [ oriented rotor_iii 'Z' ] [])
      'M' 'X';
    cipher_each_test "rotors I II III at AAA give the full alphabet mapping"
      machine_aaa "UEJOBTPZWCNSRKDGVMLFAQIYXH";
    "cipher_char does not change the configuration"
    >:: (fun _ ->
    let before = machine_aaa in
    let _ = cipher_char before 'G' in
    assert_equal "AAA" (tops_of before));
  ]

let step_tests =
  [
    step_test "rightmost rotor steps every character" (reversed "AAA") "AAB";
    step_test "rightmost rotor wraps from Z to A" (reversed "AAZ") "AAA";
    step_test "no turnover leaves the left rotors alone" (reversed "KDO")
      "KDP";
    step_test "rightmost rotor at turnover steps the middle rotor too"
      (reversed "KDQ") "KER";
    step_test "middle rotor at turnover steps itself and the left rotor"
      (reversed "KER") "LFS";
    step_test "leftmost rotor at turnover does not step extra"
      (reversed "VAA") "VAB";
    step_test "left rotor steps only once when two rotors are at turnover"
      (reversed "AEQ") "BFR";
    repeated_step_test "KDO steps through KDP KDQ KER to LFS"
      (reversed "KDO") 4 "LFS";
    repeated_step_test "KDO reaches LFU after six steps" (reversed "KDO") 6
      "LFU";
    repeated_step_test "VDP reaches WFT after four steps" (reversed "VDP") 4
      "WFT";
    "step does not change the original configuration"
    >:: (fun _ ->
    let original = reversed "AAA" in
    let _ = step original in
    assert_equal "AAA" (tops_of original));
    "step keeps the reflector, plugboard and wiring"
    >:: (fun _ ->
    let before = standard "AAA" [ ('A', 'Z') ] in
    let after = step before in
    assert_equal true
      (after.refl = before.refl
      && after.plugboard = before.plugboard
      && List.map (fun o -> o.rotor) after.rotors
         = List.map (fun o -> o.rotor) before.rotors));
  ]

let cipher_tests =
  [
    cipher_test "empty string stays empty" machine_aaa "" "";
    cipher_test "steps before enciphering the first letter" machine_aaa "G"
      "X";
    cipher_test "five repeated letters give different letters" machine_aaa
      "AAAAA" "BDZGO";
    cipher_test "rotors FUN with plugboard AZ spell a language"
      (standard "FUN" [ ('A', 'Z') ])
      "YNGXQ" "OCAML";
    cipher_test "HELLO with plugboard AZ XY and rotors MCK"
      (standard "MCK" [ ('A', 'Z'); ('X', 'Y') ])
      "HELLO" "DLTBB";
    cipher_test "two rotors with reflector C"
      (config reflector_c
         [ oriented rotor_ii 'Q'; oriented rotor_i 'E' ]
         [])
      "ENIGMA" "DSFQTP";
    roundtrip_test "enciphering twice restores HELLO"
      (standard "MCK" [ ('A', 'Z'); ('X', 'Y') ])
      "HELLO";
    roundtrip_test "enciphering twice restores a long message across turnovers"
      (standard "ADU" [ ('B', 'Q') ])
      "THEQUICKBROWNFOXJUMPSOVERTHELAZYDOGTHEQUICKBROWNFOXJUMPSOVERTHELAZYDOG";
    roundtrip_test "enciphering twice restores a message with no plugboard"
      (standard "AAA" []) "ATTACKATDAWN";
    "a letter is never enciphered to itself"
    >:: (fun _ ->
    let message = String.make 60 'E' in
    let output = cipher (standard "QEV" []) message in
    let chars s = s |> String.to_seq |> List.of_seq in
    assert_bool "some letter was enciphered to itself"
      (List.for_all2 ( <> ) (chars message) (chars output)));
  ]

let suite =
  "Enigma test suite"
  >::: List.concat
         [
           index_tests;
           r_to_l_tests;
           l_to_r_tests;
           refl_tests;
           plug_tests;
           cipher_char_tests;
           step_tests;
           cipher_tests;
         ]

let () = run_test_tt_main suite
