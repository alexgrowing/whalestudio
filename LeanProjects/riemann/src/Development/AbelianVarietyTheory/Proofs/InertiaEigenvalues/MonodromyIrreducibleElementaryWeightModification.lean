import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueIndepOfNotReducibleOverUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepOfFrobeniusFixedFrameChangeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem modStep_holds : ModStep := by
  intro l _ P AI T n _ _ K r ρ w x y hxy hR hF hS
  choose U hU hUe using hF
  obtain ⟨hfield, -, -, -, hval, hmul, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  haveI : Nontrivial P.R.BdR := ⟨hfield.exists_pair_ne⟩
  have hsum : ∀ (s : Finset n) (f : n → P.R.BdR), (∀ k ∈ s, f k ∈ Fil P 1) → ∑ k ∈ s, f k ∈ Fil P 1 := by
    intro s f hf
    unfold Fil at *
    exact sum_mem hf
  have h1 : (1 : P.R.BdR) ∉ Fil P 1 := by
    intro h
    obtain ⟨a, ha, ha'⟩ := hval 1 one_ne_zero
    exact ha' (by simpa using hmul a 1 1 1 ha h)
  have hcol : ∃ i, (U x.1 : Matrix n n P.R.BdR) i x.2 ∉ Fil P 1 := by
    by_contra hc
    push_neg at hc
    have hinv : (((U x.1)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) * (U x.1 : Matrix n n P.R.BdR) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have he := congrFun (congrFun hinv x.2) x.2
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at he
    apply h1
    rw [← he]
    apply hsum
    intro k _
    simpa using hmul 0 1 _ _ ((hU x.1).2 x.2 k) (hc k)
  have heig : ∀ g : ↥(GK K), (matD P ρ (x.1 : ℕ) g).mulVec
      (fun i => P.actQdR (g : GQ l) ((U x.1 : Matrix n n P.R.BdR) i x.2)) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w x.1 x.2 : ℚ_[l]ˣ) : ℚ_[l]) •
        (fun i => (U x.1 : Matrix n n P.R.BdR) i x.2) := by
    intro g
    funext i
    have h := congrFun (congrFun (hUe x.1 g) i) x.2
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
    simp only [Matrix.map_apply] at h
    rw [Matrix.mulVec, dotProduct, h, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hind := GlobalTheory.T.residue_indep_of_not_reducibleOverUnramified l P AI T n K r ρ (x.1 : ℕ) (fun i => (U x.1 : Matrix n n P.R.BdR) i x.2) (w x.1 x.2)
    hR hS (fun i => (hU x.1).1 i x.2) hcol heig
  obtain ⟨A, hA, hW⟩ := GlobalTheory.T.fundamentalLemmaLatticeFrobFixed_forall_degree r l P AI T n U x y hxy (fun m => hU m) hind
  exact GlobalTheory.T.exists_rep_of_frobeniusFixed_frame_change l P AI T n K r ρ w (fun m j => eps x y (m, j)) U A hR hUe hA hW

end GlobalTheory.PMon

end
