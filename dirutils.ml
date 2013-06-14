open FilePath
open FileUtil

module P = BatPathGen.OfString

let mkdir_p bpath =
  let fpath = P.to_string bpath in
  mkdir ~parent:true fpath

let rm_rf bpath =
  let fpath = P.to_string bpath in
  rm ~force:Force ~recurse:true [fpath]
