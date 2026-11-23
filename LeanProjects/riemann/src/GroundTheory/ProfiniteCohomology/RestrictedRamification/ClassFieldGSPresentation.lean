import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSUnram
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup Function

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

theorem valued_finiteProj (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    Valued.v ((finiteProj v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-ord v x) := by
  rw [coe_finiteProj, ord, neg_neg, WithZero.exp_log (valued_ne_zero v x)]

theorem mem_unitsLevel_zero_iff {v : HeightOneSpectrum (𝓞 K)} {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v 0 ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  rw [mem_unitsLevel]
  refine ⟨And.left, fun h ↦ ⟨h, ?_⟩⟩
  rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
  exact Valuation.map_sub_le _ h.le (by simp)

theorem valued_localUniformizer_zpow (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) :
    Valued.v (((localUniformizer v ^ k : (v.adicCompletion K)ˣ)) : v.adicCompletion K) =
      WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_localUniformizer, ← WithZero.exp_zsmul,
    smul_neg, zsmul_one, Int.cast_id]

theorem valued_diagonal (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    Valued.v ((finiteProj v (diagonal K x) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp (-ordAt v x) := by
  rw [coe_finiteProj_diagonal, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    valuation_eq_exp_neg_ordAt]

theorem placesIdele_apply [Finite S] (a : ∀ w : S, (w.1.adicCompletion K)ˣ) :
    letI := Fintype.ofFinite S
    placesIdele S a = ∏ w : S, finiteEmbedding w.1 (a w) :=
  rfl

open Classical in

theorem finiteProj_placesIdele [Finite S] (a : ∀ w : S, (w.1.adicCompletion K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteProj v (placesIdele S a) = if h : v ∈ S then a ⟨v, h⟩ else 1 := by
  let := Fintype.ofFinite S
  rw [placesIdele_apply, map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single ⟨v, h⟩
      (fun w _ hw ↦ finiteProj_finiteEmbedding_of_ne (fun e ↦ hw (Subtype.ext e.symm)) _)
      (fun h' ↦ absurd (Finset.mem_univ _) h'), finiteProj_finiteEmbedding]
  · refine Finset.prod_eq_one fun w _ ↦ finiteProj_finiteEmbedding_of_ne ?_ _
    intro e
    rw [e] at h
    exact h w.2

open Classical in

def divisorExponent (D : sDivisor S) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  if h : v ∈ S then 0 else D ⟨v, h⟩

omit [NumberField K] in
theorem divisorExponent_of_not_mem (D : sDivisor S) {v : HeightOneSpectrum (𝓞 K)} (h : v ∉ S) :
    divisorExponent D v = D ⟨v, h⟩ :=
  dif_neg h

omit [NumberField K] in
theorem divisorExponent_of_mem (D : sDivisor S) {v : HeightOneSpectrum (𝓞 K)} (h : v ∈ S) :
    divisorExponent D v = 0 :=
  dif_pos h

omit [NumberField K] in
theorem divisorExponent_add (D₁ D₂ : sDivisor S) (v : HeightOneSpectrum (𝓞 K)) :
    divisorExponent (D₁ + D₂) v = divisorExponent D₁ v + divisorExponent D₂ v := by
  by_cases h : v ∈ S
  · simp [divisorExponent_of_mem _ h]
  · simp [divisorExponent_of_not_mem _ h]

theorem finiteProj_divisorIdele (D : sDivisor S) (v : HeightOneSpectrum (𝓞 K)) :
    finiteProj v (Additive.toMul (divisorIdele S D)) = localUniformizer v ^ divisorExponent D v := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp [divisorExponent]
  | add D₁ D₂ h₁ h₂ => rw [map_add, toMul_add, map_mul, h₁, h₂, divisorExponent_add, zpow_add]
  | single w k =>
    rw [divisorIdele_single, map_zpow]
    by_cases h : v = w.1
    · subst h
      rw [finiteProj_finiteEmbedding, divisorExponent_of_not_mem _ w.2]
      simp
    · rw [finiteProj_finiteEmbedding_of_ne h, one_zpow]
      by_cases hS : v ∈ S
      · rw [divisorExponent_of_mem _ hS, zpow_zero]
      · rw [divisorExponent_of_not_mem _ hS, Finsupp.single_apply, if_neg, zpow_zero]
        intro e
        exact h (congrArg Subtype.val e).symm

variable (S)

def principalPresentation : Kˣ →* (∀ w : S, (w.1.adicCompletion K)ˣ) × Multiplicative (sDivisor S) :=
  (MonoidHom.pi fun w : S ↦ (finiteProj w.1).comp (diagonal K)).prod
    (AddMonoidHom.toMultiplicativeRight (divS S))

theorem principalPresentation_apply (x : Kˣ) :
    principalPresentation S x =
      (fun w : S ↦ finiteProj w.1 (diagonal K x), Multiplicative.ofAdd (divS S (Additive.ofMul x))) :=
  rfl

theorem sPresentation_surjective [Finite S] : Surjective (sPresentation S) := by
  intro c
  obtain ⟨x, rfl⟩ := SIdeleClassGroup.mk_surjective S c
  let D : sDivisor S := Finsupp.ofSupportFinite (fun v ↦ ord v.1 x) (by
    refine ((eventually_ord_eq_zero x).preimage Subtype.val_injective.injOn).subset ?_
    intro v hv
    exact hv)
  have hD : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, D v = ord v.1 x := fun v ↦ rfl
  refine ⟨(fun w ↦ finiteProj w.1 x, Multiplicative.ofAdd D), ?_⟩
  rw [sPresentation_apply]
  apply (QuotientGroup.eq (s := sIdeleSubgroup S)).2
  refine Subgroup.mem_sup_right (mem_unitsOutside.2 ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩)
  · rw [map_mul, map_inv, map_mul, finiteProj_placesIdele, dif_pos hv, toAdd_ofAdd,
      finiteProj_divisorIdele, divisorExponent_of_mem _ hv, zpow_zero, mul_one, inv_mul_cancel]
  · rw [mem_unitsLevel_zero_iff, map_mul, map_inv, map_mul, finiteProj_placesIdele, dif_neg hv,
      toAdd_ofAdd, finiteProj_divisorIdele, divisorExponent_of_not_mem _ hv, hD, one_mul,
      Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_localUniformizer_zpow,
      valued_finiteProj]
    exact inv_mul_cancel₀ WithZero.exp_ne_zero

theorem ker_sPresentation [Finite S] : (sPresentation S).ker = (principalPresentation S).range := by
  ext ⟨a, D⟩
  rw [MonoidHom.mem_ker, sPresentation_apply, MonoidHom.mem_range]
  constructor
  · intro h
    have hmem := (QuotientGroup.eq_one_iff (N := sIdeleSubgroup S) _).1 h
    obtain ⟨_, ⟨x, rfl⟩, u, hu, hxu⟩ := Subgroup.mem_sup.1 hmem
    obtain ⟨hS, hout⟩ := mem_unitsOutside.1 hu
    refine ⟨x, Prod.ext (funext fun w ↦ ?_) ?_⟩
    · have e := congrArg (finiteProj w.1) hxu
      rw [map_mul, hS w.1 w.2, mul_one, map_mul, finiteProj_placesIdele, dif_pos w.2,
        finiteProj_divisorIdele, divisorExponent_of_mem _ w.2, zpow_zero, mul_one] at e
      exact e
    · apply Multiplicative.toAdd.injective
      ext v
      have e := congrArg (fun y ↦ Valued.v ((finiteProj v.1 y : (v.1.adicCompletion K)ˣ) :
        v.1.adicCompletion K)) hxu
      simp only [map_mul, Units.val_mul, finiteProj_placesIdele, dif_neg v.2,
        one_mul, finiteProj_divisorIdele, divisorExponent_of_not_mem _ v.2,
        valued_localUniformizer_zpow, valued_diagonal] at e
      rw [(mem_unitsLevel_zero_iff.1 (hout v.1 v.2)), mul_one, WithZero.exp_inj, neg_inj] at e
      change divS S (Additive.ofMul x) v = D.toAdd v
      rw [divS_apply, toMul_ofMul, e]
  · rintro ⟨x, hx⟩
    have h1 := congrArg Prod.fst hx
    have h2 := congrArg Prod.snd hx
    rw [principalPresentation_apply] at h1 h2
    subst h1
    subst h2
    apply (QuotientGroup.eq_one_iff (N := sIdeleSubgroup S) _).2
    have hu : (diagonal K x)⁻¹ * (placesIdele S (fun w ↦ finiteProj w.1 (diagonal K x)) *
        Additive.toMul (divisorIdele S (divS S (Additive.ofMul x)))) ∈ unitsOutside S := by
      refine mem_unitsOutside.2 ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
      · rw [map_mul, map_mul, map_inv, finiteProj_placesIdele, dif_pos hv, finiteProj_divisorIdele,
          divisorExponent_of_mem _ hv, zpow_zero, mul_one, inv_mul_cancel]
      · rw [mem_unitsLevel_zero_iff, map_mul, map_mul, map_inv, finiteProj_placesIdele, dif_neg hv,
          one_mul, finiteProj_divisorIdele, divisorExponent_of_not_mem _ hv, Units.val_mul, map_mul,
          Units.val_inv_eq_inv_val, map_inv₀, valued_diagonal, valued_localUniformizer_zpow]
        exact inv_mul_cancel₀ WithZero.exp_ne_zero
    have : placesIdele S (fun w ↦ finiteProj w.1 (diagonal K x)) *
        Additive.toMul (divisorIdele S (divS S (Additive.ofMul x))) =
        diagonal K x * ((diagonal K x)⁻¹ * (placesIdele S (fun w ↦ finiteProj w.1 (diagonal K x)) *
          Additive.toMul (divisorIdele S (divS S (Additive.ofMul x))))) := by group
    rw [toAdd_ofAdd, this]
    exact Subgroup.mul_mem_sup ⟨x, rfl⟩ hu

end

end GroundTheory.ProfCoh
