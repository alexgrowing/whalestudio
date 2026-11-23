import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR

namespace GlobalTheory.UnramValue

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct IsLocalRing Polynomial

theorem exists_pow_card_eq {S : Type*} [CommRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S] [Fintype (ResidueField S)] (x : S) :
    ∃ t : S, t ^ Fintype.card (ResidueField S) = t ∧ t - x ∈ maximalIdeal S := by
  have h1 : 1 < Fintype.card (ResidueField S) := Fintype.one_lt_card
  have hm : (X ^ Fintype.card (ResidueField S) - X : S[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  obtain ⟨t, ht, htx⟩ := (IsAdicComplete.henselianRing S (maximalIdeal S)).is_henselian _ hm x
    (by
      rw [← residue_eq_zero_iff]
      simp [FiniteField.pow_card])
    (by
      change IsUnit (residue S _)
      rw [derivative_sub, derivative_X_pow]
      simp)
  refine ⟨t, ?_, htx⟩
  simpa [sub_eq_zero] using ht

variable {l : ℕ} [Fact l.Prime]

theorem norm_natCast_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]

theorem integral_mem (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] L]
    (h : ∀ x ∈ L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) (x : integralClosure ℤ_[l] L) :
    ((x : L) : Om l) ∈ MaximalUnramifiedExtension l := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : L) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hmax : ∀ y : integralClosure ℤ_[l] L,
      y ∈ maximalIdeal (integralClosure ℤ_[l] L) ↔ ‖((y : L) : Om l)‖ < 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm, GlobalTheory.DiscEval.intEmb_apply,
      GlobalTheory.DiscEval.fieldEmb_apply, PadicComplex.norm_extends]
  have hint : ∀ y : L, y ∈ integralClosure ℤ_[l] L ↔ ‖(y : Om l)‖ ≤ 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_integralClosure_iff_norm, GlobalTheory.DiscEval.fieldEmb_apply,
      PadicComplex.norm_extends]
  let N : Submodule ℤ_[l] (integralClosure ℤ_[l] L) :=
    { carrier := {y | ((y : L) : Om l) ∈ MaximalUnramifiedExtension l}
      add_mem' := fun ha hb => (MaximalUnramifiedExtension l).add_mem ha hb
      zero_mem' := (MaximalUnramifiedExtension l).zero_mem
      smul_mem' := fun c y hy => (MaximalUnramifiedExtension l).smul_mem (x := (c : ℚ_[l])) hy }
  have := GlobalTheory.DiscEval.isAdicComplete_integralClosure L
  have := GlobalTheory.DiscEval.finite_residueField_integralClosure L
  let _ := Fintype.ofFinite (ResidueField (integralClosure ℤ_[l] L))
  have hle : (⊤ : Submodule ℤ_[l] (integralClosure ℤ_[l] L)) ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal ℤ_[l])
      Module.Finite.fg_top (maximalIdeal_le_jacobson _) fun y _ => ?_
    obtain ⟨t, ht, hty⟩ := exists_pow_card_eq y
    have htN : t ∈ N := by
      change ((t : L) : Om l) ∈ MaximalUnramifiedExtension l
      by_cases h0 : ((t : L) : Om l) = 0
      · rw [h0]; exact zero_mem _
      have h1 : 1 < Fintype.card (ResidueField (integralClosure ℤ_[l] L)) := Fintype.one_lt_card
      refine IntermediateField.subset_adjoin _ _
        ⟨Fintype.card (ResidueField (integralClosure ℤ_[l] L)) - 1, by omega, ?_, ?_⟩
      · rintro ⟨c, hc⟩
        have h2 : (l : ResidueField (integralClosure ℤ_[l] L)) = 0 := by
          rw [← map_natCast (residue _), residue_eq_zero_iff, hmax]
          push_cast
          rw [norm_natCast_l]
          exact inv_lt_one_of_one_lt₀ hl1
        have h3 := congrArg (Nat.cast : ℕ → ResidueField (integralClosure ℤ_[l] L)) hc
        rw [Nat.cast_sub h1.le] at h3
        simp [h2] at h3
      · have h2 := congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : Om l)) ht
        push_cast at h2
        apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel h1.le, h2, one_mul]
    have hd : ((t - y : integralClosure ℤ_[l] L) : L) / l ∈ integralClosure ℤ_[l] L := by
      rw [hint]
      rw [hmax] at hty
      generalize ((t - y : integralClosure ℤ_[l] L) : L) = z at hty
      push_cast
      by_cases h0 : (z : Om l) = 0
      · simp [h0]
      obtain ⟨k, hk⟩ := h _ z.2 h0
      rw [hk, zpow_lt_one_iff_right₀ hl1] at hty
      rw [norm_div, hk, norm_natCast_l, div_inv_eq_mul, ← zpow_add_one₀ (by positivity)]
      exact zpow_le_one_of_nonpos₀ hl1.le (by omega)
    have he : y = t - (l : ℤ_[l]) • (⟨_, hd⟩ : integralClosure ℤ_[l] L) := by
      apply Subtype.ext
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      push_cast
      field_simp
      ring
    rw [he]
    refine sub_mem (Submodule.mem_sup_left htN) (Submodule.mem_sup_right
      (Submodule.smul_mem_smul ?_ Submodule.mem_top))
    exact PadicInt.irreducible_p.not_isUnit
  exact hle Submodule.mem_top

theorem le_Kur_of_norm : ∀ (l : ℕ) [Fact l.Prime] (M : FinExt l),
    (∀ x ∈ M.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) → M.1 ≤ MaximalUnramifiedExtension l := by
  intro l _ M h x hx
  obtain ⟨L, hL⟩ := M
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := integralClosure ℤ_[l] L) (⟨x, hx⟩ : L)
  have h1 : x = ((a : L) : Om l) / ((b : L) : Om l) := (congrArg Subtype.val hab).symm
  rw [h1]
  exact div_mem (integral_mem L h a) (integral_mem L h b)

end GlobalTheory.UnramValue
