import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne
open NumberField IsDedekindDomain GlobalTheory.SUVol
open Matrix

namespace GlobalTheory.SUVol

theorem ncard_image_lifts_eq_card_specialUnitaryGroup {O : Type*} [CommRing O] (w : Ideal O)
    [StarRing (O ⧸ w)] (c : O → O)
    (hc : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x)) (r : ℕ) :
    Set.ncard ((fun g : Matrix (Fin r) (Fin r) O => g.map (Ideal.Quotient.mk w)) ''
      {g | g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w}) =
      Nat.card (Matrix.specialUnitaryGroup (Fin r) (O ⧸ w)) := by
  have key : ∀ g : Matrix (Fin r) (Fin r) O,
      (g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w) ↔
        (g.map (Ideal.Quotient.mk w))ᵀ ∈ Matrix.specialUnitaryGroup (Fin r) (O ⧸ w) := by
    intro g
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.det_transpose,
      and_comm]
    refine and_congr ?_ ?_
    · rw [← Matrix.ext_iff]
      refine forall_congr' fun a => forall_congr' fun b => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, sub_eq_zero]
      have e1 : Ideal.Quotient.mk w ((gᵀ * g.map c) a b) =
          ((g.map (Ideal.Quotient.mk w))ᵀ * star (g.map (Ideal.Quotient.mk w))ᵀ) a b := by
        simp [Matrix.mul_apply, Matrix.star_apply, hc]
      have e2 : Ideal.Quotient.mk w ((1 : Matrix (Fin r) (Fin r) O) a b) =
          (1 : Matrix (Fin r) (Fin r) (O ⧸ w)) a b := by
        simp only [Matrix.one_apply]; split_ifs <;> simp
      rw [e1, e2]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_one, RingHom.map_det,
        RingHom.mapMatrix_apply]
  have himg : ((fun g : Matrix (Fin r) (Fin r) O => g.map (Ideal.Quotient.mk w)) ''
      {g | g.det - 1 ∈ w ∧ ∀ a b, (gᵀ * g.map c - 1) a b ∈ w}) =
      Matrix.transpose '' (Matrix.specialUnitaryGroup (Fin r) (O ⧸ w) : Set _) := by
    ext A
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, (key g).1 hg, Matrix.transpose_transpose _⟩
    · rintro ⟨B, hB, rfl⟩
      choose s hs using Ideal.Quotient.mk_surjective (I := w)
      have e : (Bᵀ.map s).map (Ideal.Quotient.mk w) = Bᵀ := by
        ext a b; simp [hs]
      refine ⟨Bᵀ.map s, (key _).2 ?_, e⟩
      rw [e, Matrix.transpose_transpose]; exact hB
  rw [himg, Set.ncard_image_of_injective _ Matrix.transpose_injective, ← Nat.card_coe_set_eq]
  rfl

theorem exists_star_ne_of_not_surjective {K A : Type*} [Field K] [Finite K] [StarRing K]
    (f : A → K) (hadd : ∀ x : K, ∃ a, f a = x + star x) (hmul : ∀ x : K, ∃ a, f a = x * star x)
    (hf : ¬ Function.Surjective f) : ∃ a : K, star a ≠ a := by
  by_contra h
  push Not at h
  apply hf
  intro x
  by_cases h2 : (2 : K) = 0
  · have hinj : Function.Injective (fun y : K => y * y) := by
      intro y z hyz
      simp only at hyz
      have : (y - z) * (y - z) = 0 := by linear_combination hyz + (z * z - y * z) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj x
    obtain ⟨a, ha⟩ := hmul y
    exact ⟨a, by rw [ha, h y]; exact hy⟩
  · obtain ⟨a, ha⟩ := hadd (x / 2)
    exact ⟨a, by rw [ha, h]; field_simp; ring⟩

theorem prod_le_locFactor_of_isPrime (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r)
    (hw : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime) :
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  classical
  unfold locFactor resOrder
  rw [if_pos hw]
  set w := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hwdef
  set c := IsCMField.ringOfIntegersComplexConj E with hcdef
  have hcc : ∀ x, c (c x) = x := fun x => by
    ext; simp [hcdef]
  have hfix : ∀ a, c (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) = algebraMap _ _ a :=
    fun a => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E _).2 ⟨a, rfl⟩
  have hle : w ≤ w.comap (c : 𝓞 E →+* 𝓞 E) := by
    rw [hwdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c _ ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  have hw0 : w ≠ ⊥ := by
    rw [hwdef, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  haveI hmax : w.IsMaximal := hw.isMaximal hw0
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field w
  haveI : Finite (𝓞 E ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0
  let σ : (𝓞 E ⧸ w) →+* (𝓞 E ⧸ w) := Ideal.quotientMap w (c : 𝓞 E →+* 𝓞 E) hle
  have hσ : ∀ x, σ (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := fun x => rfl
  letI : StarRing (𝓞 E ⧸ w) :=
    { star := σ
      star_involutive := fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        change σ (σ _) = _
        rw [hσ, hσ, hcc]
      star_mul := fun x y => by
        change σ (x * y) = σ y * σ x
        rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hstar : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := hσ
  rw [ncard_image_lifts_eq_card_specialUnitaryGroup w c hstar r]
  set q := Ideal.absNorm v.asIdeal with hq
  have hK : Nat.card (𝓞 E ⧸ w) = q ^ 2 := by
    have h := Ideal.absNorm_algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) v.asIdeal
    rw [← IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two, Ideal.absNorm_apply (Ideal.map _ _),
      Submodule.cardQuot_apply] at h
    exact h
  have hq2 : 2 ≤ q := GlobalTheory.FiniteOrders.two_le_of_card_eq_sq hK
  have hs : ∃ a : 𝓞 E ⧸ w, star a ≠ a := by
    let f : (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) →+* (𝓞 E ⧸ w) :=
      Ideal.quotientMap w (algebraMap _ _) Ideal.le_comap_map
    have hf : ∀ a, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w (algebraMap _ _ a) :=
      fun a => rfl
    refine exists_star_ne_of_not_surjective f (fun x => ?_) (fun x => ?_) (fun hsurj => ?_)
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y + c y)).1
        (by change c _ = _; rw [map_add, hcc, add_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_add]⟩
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y * c y)).1
        (by change c _ = _; rw [map_mul, hcc, mul_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_mul]⟩
    · haveI : Finite (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) :=
        Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
      have h1 := Nat.card_le_card_of_surjective f hsurj
      have h2 : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = q := by
        rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hK, h2] at h1
      nlinarith
  have h := GlobalTheory.FiniteOrders.card_specialUnitaryGroup hK hs (Fin r) (Fintype.card_fin r) hr
  have h' := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at h'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  rw [le_div_iff₀ (by positivity)]
  refine le_of_le_of_eq ?_ h'.symm
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_))
    (by positivity)
  · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hq1))
  · have hp : (0 : ℝ) ≤ ((q : ℝ) ^ i)⁻¹ := by positivity
    rcases neg_one_pow_eq_or ℝ i with h1 | h1 <;> rw [h1] <;> linarith

end GlobalTheory.SUVol
