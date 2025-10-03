open BinNums
open Byte

(** val of_N : coq_N -> byte option **)

let of_N = function
| N0 -> Some Coq_x00
| Npos p ->
  (match p with
   | Coq_xI p0 ->
     (match p0 with
      | Coq_xI p1 ->
        (match p1 with
         | Coq_xI p2 ->
           (match p2 with
            | Coq_xI p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xff
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xbf
                        | _ -> None)
                     | Coq_xH -> Some Coq_x7f)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xdf
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x9f
                        | _ -> None)
                     | Coq_xH -> Some Coq_x5f)
                  | Coq_xH -> Some Coq_x3f)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xef
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xaf
                        | _ -> None)
                     | Coq_xH -> Some Coq_x6f)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xcf
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x8f
                        | _ -> None)
                     | Coq_xH -> Some Coq_x4f)
                  | Coq_xH -> Some Coq_x2f)
               | Coq_xH -> Some Coq_x1f)
            | Coq_xO p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf7
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb7
                        | _ -> None)
                     | Coq_xH -> Some Coq_x77)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd7
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x97
                        | _ -> None)
                     | Coq_xH -> Some Coq_x57)
                  | Coq_xH -> Some Coq_x37)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe7
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa7
                        | _ -> None)
                     | Coq_xH -> Some Coq_x67)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc7
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x87
                        | _ -> None)
                     | Coq_xH -> Some Coq_x47)
                  | Coq_xH -> Some Coq_x27)
               | Coq_xH -> Some Coq_x17)
            | Coq_xH -> Some Coq_x0f)
         | Coq_xO p2 ->
           (match p2 with
            | Coq_xI p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xfb
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xbb
                        | _ -> None)
                     | Coq_xH -> Some Coq_x7b)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xdb
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x9b
                        | _ -> None)
                     | Coq_xH -> Some Coq_x5b)
                  | Coq_xH -> Some Coq_x3b)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xeb
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xab
                        | _ -> None)
                     | Coq_xH -> Some Coq_x6b)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xcb
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x8b
                        | _ -> None)
                     | Coq_xH -> Some Coq_x4b)
                  | Coq_xH -> Some Coq_x2b)
               | Coq_xH -> Some Coq_x1b)
            | Coq_xO p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf3
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb3
                        | _ -> None)
                     | Coq_xH -> Some Coq_x73)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd3
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x93
                        | _ -> None)
                     | Coq_xH -> Some Coq_x53)
                  | Coq_xH -> Some Coq_x33)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe3
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa3
                        | _ -> None)
                     | Coq_xH -> Some Coq_x63)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc3
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x83
                        | _ -> None)
                     | Coq_xH -> Some Coq_x43)
                  | Coq_xH -> Some Coq_x23)
               | Coq_xH -> Some Coq_x13)
            | Coq_xH -> Some Coq_x0b)
         | Coq_xH -> Some Coq_x07)
      | Coq_xO p1 ->
        (match p1 with
         | Coq_xI p2 ->
           (match p2 with
            | Coq_xI p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xfd
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xbd
                        | _ -> None)
                     | Coq_xH -> Some Coq_x7d)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xdd
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x9d
                        | _ -> None)
                     | Coq_xH -> Some Coq_x5d)
                  | Coq_xH -> Some Coq_x3d)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xed
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xad
                        | _ -> None)
                     | Coq_xH -> Some Coq_x6d)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xcd
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x8d
                        | _ -> None)
                     | Coq_xH -> Some Coq_x4d)
                  | Coq_xH -> Some Coq_x2d)
               | Coq_xH -> Some Coq_x1d)
            | Coq_xO p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf5
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb5
                        | _ -> None)
                     | Coq_xH -> Some Coq_x75)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd5
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x95
                        | _ -> None)
                     | Coq_xH -> Some Coq_x55)
                  | Coq_xH -> Some Coq_x35)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe5
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa5
                        | _ -> None)
                     | Coq_xH -> Some Coq_x65)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc5
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x85
                        | _ -> None)
                     | Coq_xH -> Some Coq_x45)
                  | Coq_xH -> Some Coq_x25)
               | Coq_xH -> Some Coq_x15)
            | Coq_xH -> Some Coq_x0d)
         | Coq_xO p2 ->
           (match p2 with
            | Coq_xI p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf9
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb9
                        | _ -> None)
                     | Coq_xH -> Some Coq_x79)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd9
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x99
                        | _ -> None)
                     | Coq_xH -> Some Coq_x59)
                  | Coq_xH -> Some Coq_x39)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe9
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa9
                        | _ -> None)
                     | Coq_xH -> Some Coq_x69)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc9
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x89
                        | _ -> None)
                     | Coq_xH -> Some Coq_x49)
                  | Coq_xH -> Some Coq_x29)
               | Coq_xH -> Some Coq_x19)
            | Coq_xO p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf1
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb1
                        | _ -> None)
                     | Coq_xH -> Some Coq_x71)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd1
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x91
                        | _ -> None)
                     | Coq_xH -> Some Coq_x51)
                  | Coq_xH -> Some Coq_x31)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe1
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa1
                        | _ -> None)
                     | Coq_xH -> Some Coq_x61)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc1
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x81
                        | _ -> None)
                     | Coq_xH -> Some Coq_x41)
                  | Coq_xH -> Some Coq_x21)
               | Coq_xH -> Some Coq_x11)
            | Coq_xH -> Some Coq_x09)
         | Coq_xH -> Some Coq_x05)
      | Coq_xH -> Some Coq_x03)
   | Coq_xO p0 ->
     (match p0 with
      | Coq_xI p1 ->
        (match p1 with
         | Coq_xI p2 ->
           (match p2 with
            | Coq_xI p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xfe
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xbe
                        | _ -> None)
                     | Coq_xH -> Some Coq_x7e)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xde
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x9e
                        | _ -> None)
                     | Coq_xH -> Some Coq_x5e)
                  | Coq_xH -> Some Coq_x3e)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xee
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xae
                        | _ -> None)
                     | Coq_xH -> Some Coq_x6e)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xce
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x8e
                        | _ -> None)
                     | Coq_xH -> Some Coq_x4e)
                  | Coq_xH -> Some Coq_x2e)
               | Coq_xH -> Some Coq_x1e)
            | Coq_xO p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf6
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb6
                        | _ -> None)
                     | Coq_xH -> Some Coq_x76)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd6
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x96
                        | _ -> None)
                     | Coq_xH -> Some Coq_x56)
                  | Coq_xH -> Some Coq_x36)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe6
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa6
                        | _ -> None)
                     | Coq_xH -> Some Coq_x66)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc6
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x86
                        | _ -> None)
                     | Coq_xH -> Some Coq_x46)
                  | Coq_xH -> Some Coq_x26)
               | Coq_xH -> Some Coq_x16)
            | Coq_xH -> Some Coq_x0e)
         | Coq_xO p2 ->
           (match p2 with
            | Coq_xI p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xfa
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xba
                        | _ -> None)
                     | Coq_xH -> Some Coq_x7a)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xda
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x9a
                        | _ -> None)
                     | Coq_xH -> Some Coq_x5a)
                  | Coq_xH -> Some Coq_x3a)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xea
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xaa
                        | _ -> None)
                     | Coq_xH -> Some Coq_x6a)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xca
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x8a
                        | _ -> None)
                     | Coq_xH -> Some Coq_x4a)
                  | Coq_xH -> Some Coq_x2a)
               | Coq_xH -> Some Coq_x1a)
            | Coq_xO p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf2
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb2
                        | _ -> None)
                     | Coq_xH -> Some Coq_x72)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd2
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x92
                        | _ -> None)
                     | Coq_xH -> Some Coq_x52)
                  | Coq_xH -> Some Coq_x32)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe2
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa2
                        | _ -> None)
                     | Coq_xH -> Some Coq_x62)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc2
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x82
                        | _ -> None)
                     | Coq_xH -> Some Coq_x42)
                  | Coq_xH -> Some Coq_x22)
               | Coq_xH -> Some Coq_x12)
            | Coq_xH -> Some Coq_x0a)
         | Coq_xH -> Some Coq_x06)
      | Coq_xO p1 ->
        (match p1 with
         | Coq_xI p2 ->
           (match p2 with
            | Coq_xI p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xfc
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xbc
                        | _ -> None)
                     | Coq_xH -> Some Coq_x7c)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xdc
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x9c
                        | _ -> None)
                     | Coq_xH -> Some Coq_x5c)
                  | Coq_xH -> Some Coq_x3c)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xec
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xac
                        | _ -> None)
                     | Coq_xH -> Some Coq_x6c)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xcc
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x8c
                        | _ -> None)
                     | Coq_xH -> Some Coq_x4c)
                  | Coq_xH -> Some Coq_x2c)
               | Coq_xH -> Some Coq_x1c)
            | Coq_xO p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf4
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb4
                        | _ -> None)
                     | Coq_xH -> Some Coq_x74)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd4
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x94
                        | _ -> None)
                     | Coq_xH -> Some Coq_x54)
                  | Coq_xH -> Some Coq_x34)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe4
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa4
                        | _ -> None)
                     | Coq_xH -> Some Coq_x64)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc4
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x84
                        | _ -> None)
                     | Coq_xH -> Some Coq_x44)
                  | Coq_xH -> Some Coq_x24)
               | Coq_xH -> Some Coq_x14)
            | Coq_xH -> Some Coq_x0c)
         | Coq_xO p2 ->
           (match p2 with
            | Coq_xI p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf8
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb8
                        | _ -> None)
                     | Coq_xH -> Some Coq_x78)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd8
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x98
                        | _ -> None)
                     | Coq_xH -> Some Coq_x58)
                  | Coq_xH -> Some Coq_x38)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe8
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa8
                        | _ -> None)
                     | Coq_xH -> Some Coq_x68)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc8
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x88
                        | _ -> None)
                     | Coq_xH -> Some Coq_x48)
                  | Coq_xH -> Some Coq_x28)
               | Coq_xH -> Some Coq_x18)
            | Coq_xO p3 ->
              (match p3 with
               | Coq_xI p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xf0
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xb0
                        | _ -> None)
                     | Coq_xH -> Some Coq_x70)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xd0
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x90
                        | _ -> None)
                     | Coq_xH -> Some Coq_x50)
                  | Coq_xH -> Some Coq_x30)
               | Coq_xO p4 ->
                 (match p4 with
                  | Coq_xI p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xe0
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xa0
                        | _ -> None)
                     | Coq_xH -> Some Coq_x60)
                  | Coq_xO p5 ->
                    (match p5 with
                     | Coq_xI p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_xc0
                        | _ -> None)
                     | Coq_xO p6 ->
                       (match p6 with
                        | Coq_xH -> Some Coq_x80
                        | _ -> None)
                     | Coq_xH -> Some Coq_x40)
                  | Coq_xH -> Some Coq_x20)
               | Coq_xH -> Some Coq_x10)
            | Coq_xH -> Some Coq_x08)
         | Coq_xH -> Some Coq_x04)
      | Coq_xH -> Some Coq_x02)
   | Coq_xH -> Some Coq_x01)
