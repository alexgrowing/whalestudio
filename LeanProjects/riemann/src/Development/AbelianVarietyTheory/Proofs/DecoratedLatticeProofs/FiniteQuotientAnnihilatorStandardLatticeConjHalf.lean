import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsIdemSumConjOfIsIdemSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulAnnihilatorHalfMemStandardHomStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairFiniteAdeleZeroMulPairFiniteAdeleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddSubgroupFiniteQuotOfCommensurable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.AnnConjHalf

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x u v : WO S T) :
    symplO S T x (u + v) = symplO S T x u + symplO S T x v := by
  simp only [symplO, hO, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_neg_right' (S T : HSp D) (x u : WO S T) :
    symplO S T x (-u) = -symplO S T x u := by
  simp only [symplO, hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp only [symplO, hO, Matrix.zero_apply, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

def annHalf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (E₂ : AE D) : AddSubgroup (WO S T) where
  carrier := {u | IsHalf (cA D E₂) u ∧ ∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1}
  zero_mem' := ⟨fun i j => by simp, fun x _ _ => by rw [symplO_zero_right', AddChar.map_zero_eq_one]⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨fun i j => by rw [Matrix.add_apply, mul_add, hu i j, hv i j], fun x hx hxh => ?_⟩
    rw [symplO_add_right', AddChar.map_add_eq_mul, hu' x hx hxh, hv' x hx hxh, mul_one]
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨fun i j => by rw [Matrix.neg_apply, mul_neg, hu i j], fun x hx hxh => ?_⟩
    rw [symplO_neg_right', AddChar.map_neg_eq_inv, hu' x hx hxh, inv_one]

def stdHalf (S T : HSp D) (f : AE D) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ stdHom S T ∧ IsHalf f u}
  zero_mem' := ⟨zero_mem _, fun i j => by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨add_mem hu hv, fun i j => by rw [Matrix.add_apply, mul_add, hu' i j, hv' i j]⟩
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    exact ⟨neg_mem hu, fun i j => by rw [Matrix.neg_apply, mul_neg, hu' i j]⟩

theorem half_nsmul {m n : ℕ} {f : AE D} {u : Mx D m n} (hu : IsHalf f u) (N : ℕ) : IsHalf f (N • u) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem nsmul_eq_zero_WO (S T : HSp D) {N : ℕ} (hN : 0 < N) (v : WO S T) (h : N • v = 0) : v = 0 := by
  ext i j
  have hij : N • v i j = 0 := by
    have := congrFun (congrFun h i) j
    rwa [Matrix.smul_apply] at this
  have hF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hu : IsUnit ((N : ℕ) : AE D) := by
    have := (isUnit_iff_ne_zero.2 hF).map (algebraMap D.host.F (AE D))
    rwa [map_natCast] at this
  rw [nsmul_eq_mul] at hij
  rw [Matrix.zero_apply]
  exact (hu.mul_right_eq_zero).1 hij

theorem ann_conj_half_finite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → ∃ r ∈ R, ∃ v : WO S T, IsHalf (cA D E₂) v ∧ (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x v) = 1) ∧ u = r + k • v := by
  intro D ψ hψ S T Q E₂ hE k hk
  obtain ⟨N, hN, hup⟩ := GlobalTheory.T.exists_nsmul_annihilator_half_mem_standardHom D ψ hψ S T Q E₂ hE
  obtain ⟨M, hM, hlow⟩ := GlobalTheory.StdHomOrth.exists_nsmul_orth D ψ hψ S T
  obtain ⟨Q', hQ'⟩ := GlobalTheory.T.exists_isIdemSum_conj_of_isIdemSum D Q E₂ hE
  have hAL : ∀ a ∈ annHalf ψ S T E₂, N • a ∈ stdHalf S T (cA D E₂) := fun a ha =>
    ⟨hup a ha.1 ha.2, half_nsmul ha.1 N⟩
  have hLA : ∀ l ∈ stdHalf S T (cA D E₂), M • l ∈ annHalf ψ S T E₂ := fun l hl =>
    ⟨half_nsmul hl.2 M, fun x hx _ => hlow x hx l hl.1⟩
  have hfin : ∀ j : ℕ, 0 < j → ∃ R : Finset (WO S T), ∀ u ∈ stdHalf S T (cA D E₂), ∃ r ∈ R,
      ∃ v ∈ stdHalf S T (cA D E₂), u = r + j • v := by
    intro j hj
    obtain ⟨R, hR⟩ := GlobalTheory.HalfStdFin.exists_reps_half_stdHom D S T Q' (cA D E₂) hQ' j hj
    refine ⟨R, fun u hu => ?_⟩
    obtain ⟨r, hr, v, hv, hvh, huv⟩ := hR u hu.1 hu.2
    exact ⟨r, hr, v, ⟨hv, hvh⟩, huv⟩
  obtain ⟨R, hR⟩ := GlobalTheory.addSubgroup_finite_quot_of_commensurable (WO S T) (annHalf ψ S T E₂) (stdHalf S T (cA D E₂))
    N M hN hM (nsmul_eq_zero_WO S T hN) hAL hLA hfin k hk
  refine ⟨R, fun u hu hann => ?_⟩
  obtain ⟨r, hr, v, hv, huv⟩ := hR u ⟨hu, hann⟩
  exact ⟨r, hr, v, hv.1, hv.2, huv⟩

end GlobalTheory.AnnConjHalf

end
