import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnisoClauseOfFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ResAniso

variable (D : D7) (n : ℕ)

def hermN : AddSubgroup (Mx D n n) where
  carrier := {b | adj b = b}
  add_mem' := by
    intro a b ha hb
    change adj _ = _ at ha hb ⊢
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply] at h1 h2 ⊢
    rw [map_add, h1, h2]
  zero_mem' := by simp [adj]
  neg_mem' := by
    intro a ha
    change adj _ = _ at ha ⊢
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply] at h1 ⊢
    rw [map_neg, h1]

variable {D n}

def nElt (b : hermN D n) : StdUnn.G D n := ((StdUnn.Model.exists_unip b.1).2 b.2).choose

theorem mat_nElt (b : hermN D n) : StdUnn.mat (nElt b) = StdUnn.blk4 1 b.1 0 1 :=
  ((StdUnn.Model.exists_unip b.1).2 b.2).choose_spec

variable (D n)

def wElt : StdUnn.G D n := (StdUnn.Model.exists_weyl (D := D) (n := n)).choose

theorem mat_wElt : StdUnn.mat (wElt D n) = StdUnn.blk4 0 1 (-1) 0 :=
  (StdUnn.Model.exists_weyl (D := D) (n := n)).choose_spec

variable {D n}

def intw (db : Measure (hermN D n)) (f : ℂ → StdUnn.G D n → ℂ) (s : ℂ) (g : StdUnn.G D n) : ℂ :=
  ∫ b, f s (wElt D n * nElt b * g) ∂db

def eisOf (H : StdUnn.G D n → ℝ≥0) (s₁ : ℂ) (r : StdUnn.G D n → ℂ) (g : StdUnn.G D n) : ℂ → ℂ :=
  fun s => cosetSum (StdUnn.P D n) (StdUnn.GF D n) (fun x => npow (H x) (s - s₁) * r x) g

end GlobalTheory.ResAniso
end
