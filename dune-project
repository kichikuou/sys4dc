(lang dune 3.0)

(name sys4dc)
(version 0.0.1)

(generate_opam_files true)

(source
 (github kichikuou/sys4dc))

(authors "kichikuou <KichikuouChrome@gmail.com>")

(maintainers "kichikuou <KichikuouChrome@gmail.com>")

(license GPL-2.0-or-later)

(documentation https://github.com/kichikuou/sys4dc)

(package
 (name sys4dc)
 (synopsis "System4 decompiler")
 (description "A decompiler for AliceSoft's System4 AIN files.")
 (depends
  ocaml
  base
  core
  core_unix
  ppx_deriving
  camlzip
  yojson
  dune))
