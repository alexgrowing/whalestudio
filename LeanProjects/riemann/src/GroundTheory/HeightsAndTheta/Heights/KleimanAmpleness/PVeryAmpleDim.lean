import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleDimSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDimTie
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AmpleAffineGen

noncomputable section

universe u w

namespace VeryAmpleDim

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem mem_sub_of_mem_secs {H : SubSystem k x Ω} {s : Ω} (hs : s ∈ H.secs) (I : Chart x) :
    s ∈ H.sub I :=
  (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs I)

theorem ampleBase_le_funField {r : ℕ} (h : Fin (r + 1) → Ω) {j : Fin (r + 1)} (hj : h j ≠ 0) {a : Ω}
    (ha : a ∈ ampleBase (S := k) h j) : a ∈ funField (k := k) h := by
  have hle : ampleBase (S := k) h j ≤ (funField (k := k) h).toSubalgebra :=
    Algebra.adjoin_le (by
      rintro _ ⟨l, rfl⟩
      exact IntermediateField.subset_adjoin k _ ⟨j, l, hj, rfl⟩)
  exact hle ha

theorem mem_funField_of_mem_chartRing {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ chartRing k x (singleChart hi)) : a ∈ funField (k := k) x :=
  ampleBase_le_funField x hi (mem_ampleBase_of_mem_chartRing hi ha)

theorem funField_le (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    funField (k := k) h ≤ funField (k := k) x := by
  show IntermediateField.adjoin k _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, l, hj, rfl⟩
  obtain ⟨Q', hQ'⟩ := Nb.invertible (singleChart hi)
  have hone : (1 : Ω) ∈ Nb.sub (singleChart hi) * Q' := by
    rw [hQ']; exact Submodule.one_le.mp le_rfl
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Q', q ≠ 0 := by
    by_contra hc
    push Not at hc
    have hbot : Q' = ⊥ := (Submodule.eq_bot_iff _).mpr hc
    rw [hbot, Submodule.mul_bot] at hone
    exact one_ne_zero ((Submodule.mem_bot _).mp hone)
  have hmem : ∀ l, h l * q ∈ chartRing k x (singleChart hi) := by
    intro l
    have hl := Submodule.mul_mem_mul (mem_sub_of_mem_secs (hv.mem_secs l) (singleChart hi)) hq
    rw [hQ'] at hl
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hl
    rw [← ha]
    exact a.2
  have e : h l / h j = (h l * q) / (h j * q) := (mul_div_mul_right _ _ hq0).symm
  rw [e]
  exact div_mem (mem_funField_of_mem_chartRing hi (hmem l)) (mem_funField_of_mem_chartRing hi (hmem j))

theorem le_funField (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {j₀ : Fin (r + 1)} (hj₀ : h j₀ ≠ 0) :
    funField (k := k) x ≤ funField (k := k) h := by
  classical
  obtain ⟨n, a, b, J, -, hb, hsum, hloc⟩ := hv.affine j₀ hj₀
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at hsum
  have hh : ∀ I : Chart x, h j₀ ∈ (Nb.toSubSystem.pow 1).sub I := fun I =>
    Submodule.subset_span ⟨h j₀, mem_sub_of_mem_secs (hv.mem_secs j₀) I, 1,
      one_mem_twistMod_zero (S := k) I, by rw [smul_eq_mul, mul_one]⟩
  have hF : ∀ z ∈ ampleRing Nb.toSubSystem 1 (h j₀), z ∈ funField (k := k) h := fun z hz =>
    ampleBase_le_funField h hj₀ (hv.closed j₀ hj₀ hz)
  obtain ⟨c, hc⟩ := (J t).2.1
  have hxc : x c ≠ 0 := (mem_support x).mp ((J t).2.2 hc)
  have key : ∀ l, x l / x c ∈ funField (k := k) h := by
    intro l
    have hA : x l / x c ∈ chartRing k x (J t) :=
      ⟨X l, X c, 1, X_mem_monos hc, isHomogeneous_X k l, isHomogeneous_X k c, by simp⟩
    have hE : ∀ I : Chart x, ∃ E : ℕ,
        b t ^ E * (x l / x c) ∈ ampleChart Nb.toSubSystem 1 (h j₀) I := by
      intro I
      obtain ⟨e, he⟩ := hloc t I
      obtain ⟨D, hD⟩ := exists_pow_mul_mem I (J t)
        (chartRing_mono (subset_unionChart_right I (J t)) hA)
      refine ⟨e * D, ?_⟩
      rw [← pow_mul_cancel (u := b t) (y := x l / x c) (chartRatio_mul_chartRatio I (J t)) e D]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show _ ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from he) D)
        (mem_ampleSubalg_of_mem_chartRing (hh I) hD)
    choose E hE using hE
    have hmem : b t ^ (∑ I, E I) * (x l / x c) ∈ ampleRing Nb.toSubSystem 1 (h j₀) := by
      refine Set.mem_iInter.mpr fun I => ?_
      have hle : E I ≤ ∑ I, E I := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)
      have e : b t ^ (∑ I, E I) * (x l / x c) = b t ^ ((∑ I, E I) - E I) * (b t ^ E I * (x l / x c)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show b t ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from Set.mem_iInter.mp (hb t) I) _)
        (hE I)
    rw [← mul_div_cancel_left₀ (x l / x c) (pow_ne_zero (∑ I, E I) ht)]
    exact div_mem (hF _ hmem) (pow_mem (hF _ (hb t)) _)
  show IntermediateField.adjoin k _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, l, hi, rfl⟩
  have e : x l / x i = (x l / x c) / (x i / x c) := by field_simp
  rw [e]
  exact div_mem (key l) (key i)

end VeryAmpleDim

theorem VeryAmpleDim.proof : VeryAmpleDim.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hx hv
  obtain ⟨i, hi⟩ := hx.relevant
  have hxi : x i ≠ 0 := by
    intro h0
    apply hi
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X, h0]
  obtain ⟨j, hj⟩ : ∃ j, h j ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨Q', hQ'⟩ := Nb.invertible (singleChart hxi)
    have hbot : Nb.sub (singleChart hxi) = ⊥ := by
      rw [← hv.generates (singleChart hxi), Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      exact hc l
    rw [hbot, Submodule.bot_mul] at hQ'
    have h1 : (1 : Ω) ∈ (⊥ : Submodule (chartRing k x (singleChart hxi)) Ω) := by
      rw [hQ']; exact Submodule.one_le.mp le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).mp h1)
  have hfield : funField (k := k) x = funField (k := k) h :=
    le_antisymm (VeryAmpleDim.le_funField Nb hv hj) (VeryAmpleDim.funField_le Nb hv hxi)
  have hdx : dimCl k x = e := (DimTie.proof k Ω N x (Function.ne_iff.mpr ⟨i, hxi⟩) e).mp hx
  refine (DimTie.proof k Ω r h (Function.ne_iff.mpr ⟨j, hj⟩) e).mpr ?_
  rw [← hdx]
  unfold dimCl
  rw [hfield]

end

end GroundTheory.Heights₂.Heights.Kleiman
