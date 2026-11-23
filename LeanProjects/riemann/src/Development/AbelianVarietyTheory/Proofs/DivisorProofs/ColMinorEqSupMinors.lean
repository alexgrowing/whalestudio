import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

namespace GlobalTheory.ConstLat

theorem colMinor_filter_lt_eq_iSup_minorAt : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ) {n g : ℕ} (M : Matrix (Fin n) (Fin g) K) (k : ℕ) (hk : k ≤ g), colMinor w M (Finset.univ.filter fun l : Fin g => (l : ℕ) < k) = ⨆ τ : Fin k → Fin n, w (minorAt M k hk τ) := by
  intro K _ w n g M k hk
  let e : Fin k ≃ ↥(Finset.univ.filter fun l : Fin g => (l : ℕ) < k) :=
    { toFun := fun l => ⟨Fin.castLE hk l, by simp⟩
      invFun := fun l => ⟨(l.1 : ℕ), (Finset.mem_filter.1 l.2).2⟩
      left_inv := fun l => rfl
      right_inv := fun l => rfl }
  unfold colMinor minorAt
  rw [← Equiv.iSup_comp (Equiv.arrowCongr e (Equiv.refl (Fin n)))]
  refine iSup_congr fun τ => ?_
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 2

end GlobalTheory.ConstLat
