import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Limits (pullback)

namespace GlobalTheory.FlagBaseChange

variable {B Y B' : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B)

def bcIso (E : B.Modules) :
    (Scheme.Modules.pullback (pullback.fst π g)).obj ((Scheme.Modules.pullback π).obj E) ≅
      (Scheme.Modules.pullback (pullback.snd π g)).obj ((Scheme.Modules.pullback g).obj E) :=
  (Scheme.Modules.pullbackComp (pullback.fst π g) π).app E ≪≫
    (Scheme.Modules.pullbackCongr pullback.condition).app E ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd π g) g).app E).symm

def pullFlag {E : B.Modules} {n : ℕ} (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n) :
    Vert.Flag ((Scheme.Modules.pullback (pullback.snd π g)).obj ((Scheme.Modules.pullback g).obj E)) n :=
  (fl.pull (pullback.fst π g)).ofIso (bcIso π g E)

end GlobalTheory.FlagBaseChange
