import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding
open scoped nonZeroDivisors Classical

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem norm_hms_le_norm_pInf (x : Ad F) :
    ‖homeomorphMixedSpace F x.1‖ ≤ ‖UpperTheory.V.TR.pInf F x‖ := by
  rw [norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun v _ ↦ ?_
  rw [normAtPlace_homeomorphMixedSpace]
  have hv := IsTotallyReal.isReal v
  have h : ‖x.1 v‖ = ‖UpperTheory.V.TR.pInf F x v‖ := by
    change ‖x.1 v‖ = ‖InfinitePlace.Completion.ringEquivRealOfIsReal hv (x.1 v)‖
    exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal hv).isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv)) (x.1 v)).symm
  rw [h]
  exact norm_le_pi_norm (UpperTheory.V.TR.pInf F x) v

theorem decay_one {C : Set (Ideles F)} (hC : IsCompact C) (d : 𝓞 F) (hd : d ≠ 0) (r : ℕ) :
    ∃ (k : ℕ) (u : F → ℝ), Summable u ∧ (∀ ξ, 0 ≤ u ξ) ∧ ∀ a ∈ C, ∀ T : {x : ℝ // 0 < x},
      1 ≤ (T : ℝ) → ∀ ξ : F, ξ ≠ 0 → (∃ s : 𝓞 F, (d : F) * ξ = s) →
      ((1 + ‖homeomorphMixedSpace F ((((moduleSection (w0 F) T * a : Ideles F) : Ad F) *
          algebraMap F (Ad F) ξ).1)‖) ^ k)⁻¹ ≤ ((T : ℝ) ^ r)⁻¹ * u ξ := by
  set dK : F := (d : F) with hdKdef
  have hdK : dK ≠ 0 := by
    intro h
    apply hd
    have h' : ((d : F)) = 0 := h
    exact_mod_cast h'
  set J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK))
  have hJ : ∀ ξ : F, (∃ s : 𝓞 F, dK * ξ = s) → ξ ∈ (J : FractionalIdeal (𝓞 F)⁰ F) := by
    rintro ξ ⟨s, hs⟩
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨s, ?_⟩
    rw [Algebra.smul_def]
    change (s : F) * dK⁻¹ = ξ
    rw [← hs, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]
  have hNd : ((Algebra.norm ℚ dK : ℚ) : ℝ) ≠ 0 := by
    rw [Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).2 hdK
  set κ₀ : ℝ := |((Algebra.norm ℚ dK : ℚ) : ℝ)|⁻¹
  have hκ₀ : 0 < κ₀ := inv_pos.2 (abs_pos.2 hNd)
  have hNξ : ∀ ξ : F, ξ ≠ 0 → (∃ s : 𝓞 F, dK * ξ = s) →
      κ₀ ≤ mixedEmbedding.norm (mixedEmbedding F ξ) := by
    rintro ξ hξ0 ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hξ0
      have h0 : dK * ξ = 0 := by rw [hs]; simp
      exact (mul_eq_zero.1 h0).resolve_left hdK
    have hmul : Algebra.norm ℚ dK * Algebra.norm ℚ ξ = Algebra.norm ℚ (s : F) := by
      rw [← map_mul, hs]
    have hξN : ((Algebra.norm ℚ ξ : ℚ) : ℝ) =
        ((Algebra.norm ℚ (s : F) : ℚ) : ℝ) * ((Algebra.norm ℚ dK : ℚ) : ℝ)⁻¹ := by
      rw [← hmul, Rat.cast_mul]
      field_simp
    rw [mixedEmbedding.norm_eq_norm, Rat.cast_abs, hξN, abs_mul, abs_inv]
    exact le_mul_of_one_le_left (by positivity) (one_le_abs_norm_of_ne_zero hs0)
  have hcm : Continuous fun a : IdeleGroup F ↦ (infiniteModule a)⁻¹ :=
    continuous_infiniteModule.inv₀ fun a ↦ (infiniteModule_pos a).ne'
  obtain ⟨B₂, hB₂⟩ := hC.exists_bound_of_continuousOn hcm.continuousOn
  set m : ℝ := (max B₂ 1)⁻¹
  have hm0 : 0 < m := inv_pos.2 (zero_lt_one.trans_le (le_max_right _ _))
  have hmC : ∀ a ∈ C, m ≤ infiniteModule a := by
    intro a ha
    have h1 : (infiniteModule a)⁻¹ ≤ max B₂ 1 := by
      have := hB₂ a ha
      rw [Real.norm_of_nonneg (inv_nonneg.2 (infiniteModule_pos a).le)] at this
      exact this.trans (le_max_left _ _)
    exact inv_le_of_inv_le₀ (infiniteModule_pos a) h1
  set kL := Module.finrank ℤ (idealLattice F J) + 1
  set n := Module.finrank ℚ F
  have hcont : Continuous fun a : IdeleGroup F ↦ ‖homeomorphMixedSpace F
      ((IdeleGroup.toInfinite F a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)‖ :=
    continuous_norm.comp ((homeomorphMixedSpace F).continuous.comp (Units.continuous_val.comp
      ((IdeleGroup.continuous_toInfinite (K := F)).comp continuous_inv)))
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  set κ := m * κ₀
  have hκ : 0 < κ := mul_pos hm0 hκ₀
  refine ⟨kL + n * r, fun ξ ↦ if ξ ∈ (J : FractionalIdeal (𝓞 F)⁰ F) then
      B' ^ kL * (κ ^ r)⁻¹ * ((1 + ‖mixedEmbedding F ξ‖) ^ kL)⁻¹ else 0, ?_, ?_, ?_⟩
  · exact summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ B' ^ kL * (κ ^ r)⁻¹ * ((1 + ‖x‖) ^ kL)⁻¹)
      ((summable_inv_one_add_norm_pow_idealLattice J).mul_left (B' ^ kL * (κ ^ r)⁻¹))
  · intro ξ
    dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  intro a ha t ht ξ hξ0 hξs
  have hξJ := hJ ξ hξs
  set y := moduleSection (w0 F) t * a
  set c := homeomorphMixedSpace F
    ((IdeleGroup.toInfinite F y : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)
  set c' := homeomorphMixedSpace F
    ((IdeleGroup.toInfinite F a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)
  set e' := homeomorphMixedSpace F
    ((IdeleGroup.toInfinite F (moduleSection (w0 F) t⁻¹) : (InfiniteAdeleRing F)ˣ) :
      InfiniteAdeleRing F)
  have hcc : c' * (e' * c) = 1 := by
    rw [← homeomorphMixedSpace_mul, ← homeomorphMixedSpace_mul, ← Units.val_mul, ← Units.val_mul,
      ← map_mul, ← map_mul, map_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel_right, inv_mul_cancel,
      map_one, Units.val_one, homeomorphMixedSpace_apply, map_one]
  have he' : ∀ v, normAtPlace v e' ≤ 1 := by
    intro v
    rw [normAtPlace_homeomorphMixedSpace]
    refine norm_moduleSection_apply_le_one (w0 F) ?_ v
    change (t : ℝ)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ ht
  have hz_eq : homeomorphMixedSpace F ((((y : Ideles F) : Ad F) * algebraMap F (Ad F) ξ).1) =
      c * mixedEmbedding F ξ := by
    have h1 : (((y : Ideles F) : Ad F) * algebraMap F (Ad F) ξ).1 =
        ((IdeleGroup.toInfinite F y : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) *
          algebraMap F (InfiniteAdeleRing F) ξ := rfl
    rw [h1, homeomorphMixedSpace_mul, homeomorphMixedSpace_algebraMap]
  rw [hz_eq]
  dsimp only
  rw [if_pos hξJ]
  set x := mixedEmbedding F ξ
  set z := c * x
  have hx : ‖x‖ ≤ B' * ‖z‖ := by
    calc ‖x‖ = ‖c' * (e' * z)‖ := by rw [← mul_assoc, ← mul_assoc, mul_assoc c', hcc, one_mul]
      _ ≤ ‖c'‖ * ‖e' * z‖ := norm_mul_le _ _
      _ ≤ B' * ‖z‖ :=
        mul_le_mul (((norm_norm _).symm.trans_le (hB a ha)).trans (le_max_left _ _))
          (norm_mul_le_of_normAtPlace_le_one he' z) (norm_nonneg _) hB'0.le
  have hN : (t : ℝ) * κ ≤ mixedEmbedding.norm z := by
    rw [map_mul, mixedEmbedding_norm_toInfinite, infiniteModule_mul,
      infiniteModule_moduleSection]
    have h1 := hmC a ha
    have h2 := hNξ ξ hξ0 hξs
    have ht0 : (0 : ℝ) ≤ t := t.2.le
    calc (t : ℝ) * κ = (t : ℝ) * m * κ₀ := by rw [mul_assoc]
      _ ≤ (t : ℝ) * infiniteModule a * mixedEmbedding.norm x :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 ht0) h2 hκ₀.le
          (mul_nonneg ht0 (infiniteModule_pos a).le)
  have htκ : 0 < (t : ℝ) * κ := mul_pos t.2 hκ
  have hz : (t : ℝ) * κ ≤ (1 + ‖z‖) ^ n :=
    hN.trans ((mixedEmbedding_norm_le_norm_pow z).trans
      (pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg z]) n))
  have hx' : (1 + ‖x‖) / B' ≤ 1 + ‖z‖ := by
    rw [div_le_iff₀ hB'0]
    nlinarith [norm_nonneg z]
  have h1 : ((1 + ‖z‖) ^ kL)⁻¹ ≤ (((1 + ‖x‖) / B') ^ kL)⁻¹ :=
    inv_anti₀ (pow_pos (div_pos (by positivity) hB'0) kL)
      (pow_le_pow_left₀ (div_pos (by positivity) hB'0).le hx' kL)
  have h2 : (((1 + ‖z‖) ^ n) ^ r)⁻¹ ≤ (((t : ℝ) * κ) ^ r)⁻¹ :=
    inv_anti₀ (pow_pos htκ r) (pow_le_pow_left₀ htκ.le hz r)
  calc ((1 + ‖z‖) ^ (kL + n * r))⁻¹ = ((1 + ‖z‖) ^ kL)⁻¹ * (((1 + ‖z‖) ^ n) ^ r)⁻¹ := by
        rw [pow_add, pow_mul, mul_inv]
    _ ≤ (((1 + ‖x‖) / B') ^ kL)⁻¹ * (((t : ℝ) * κ) ^ r)⁻¹ :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = ((t : ℝ) ^ r)⁻¹ * (B' ^ kL * (κ ^ r)⁻¹ * ((1 + ‖x‖) ^ kL)⁻¹) := by
        rw [div_pow, inv_div, mul_pow, mul_inv]
        ring

theorem exists_decay_bound_two (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    {C : Set (Ideles F)} (hC : IsCompact C) (d : 𝓞 F) (hd : d ≠ 0) (r : ℕ) :
    ∃ (k : ℕ) (U : (Fin 2 → F) → ℝ), Summable U ∧ ∀ a ∈ C, ∀ T : {x : ℝ // 0 < x}, 1 ≤ (T : ℝ) →
      ∀ ξ : Fin 2 → F, ξ ≠ 0 → (∀ i, ∃ s : 𝓞 F, (d : F) * ξ i = s) →
      ((1 + ‖fun i => UpperTheory.V.TR.pInf F (((moduleSection (w0 F) T * a : Ideles F) : Ad F) *
          algebraMap F (Ad F) (ξ i))‖) ^ k)⁻¹ ≤ ((T : ℝ) ^ r)⁻¹ * U ξ := by
  obtain ⟨k, u, hu, hu0, hb⟩ := decay_one hC d hd r
  set W : F → ℝ := fun η => if η = 0 then 1 else u η with hWdef
  have hW0 : ∀ η, 0 ≤ W η := fun η => by
    simp only [hWdef]
    split_ifs
    · exact zero_le_one
    · exact hu0 η
  have hWs : Summable W := by
    refine Summable.of_nonneg_of_le hW0 (fun η => ?_)
      (hu.add (hasSum_ite_eq (0 : F) (1 : ℝ)).summable)
    simp only [hWdef]
    split_ifs with h
    · linarith [hu0 η]
    · linarith
  refine ⟨2 * k, fun ξ => W (ξ 0) * W (ξ 1), ?_, ?_⟩
  · have hprod : Summable fun p : F × F => W p.1 * W p.2 :=
      hWs.mul_of_nonneg hWs (fun η => hW0 η) (fun η => hW0 η)
    exact (finTwoArrowEquiv F).summable_iff.2 hprod
  intro a ha T hT ξ hξ hds
  set y : Ideles F := moduleSection (w0 F) T * a with hy
  have hTr : ((T : ℝ) ^ r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hT)
  set f : Fin 2 → ℝ := fun i =>
    ((1 + ‖homeomorphMixedSpace F (((y : Ad F)) * algebraMap F (Ad F) (ξ i)).1‖) ^ k)⁻¹ with hfdef
  have hf0 : ∀ i, 0 ≤ f i := fun i => by simp only [hfdef]; positivity
  have hfT : ∀ i, ξ i ≠ 0 → f i ≤ ((T : ℝ) ^ r)⁻¹ * W (ξ i) := by
    intro i h
    simp only [hfdef, hWdef, if_neg h]
    exact hb a ha T hT (ξ i) h (hds i)
  have hfW : ∀ i, f i ≤ W (ξ i) := by
    intro i
    by_cases h : ξ i = 0
    · have h0 : homeomorphMixedSpace F (((y : Ad F)) * algebraMap F (Ad F) (ξ i)).1 = 0 := by
        rw [h, map_zero, mul_zero, homeomorphMixedSpace_apply]
        exact map_zero _
      simp only [hfdef, hWdef, if_pos h, h0, norm_zero, add_zero, one_pow, inv_one, le_refl]
    · exact (hfT i h).trans (mul_le_of_le_one_left (hW0 _) hTr)
  have hvec : ∀ i, ‖homeomorphMixedSpace F (((y : Ad F)) * algebraMap F (Ad F) (ξ i)).1‖ ≤
      ‖fun i => UpperTheory.V.TR.pInf F ((y : Ad F) * algebraMap F (Ad F) (ξ i))‖ := fun i =>
    (norm_hms_le_norm_pInf _).trans
      (norm_le_pi_norm (fun i => UpperTheory.V.TR.pInf F ((y : Ad F) * algebraMap F (Ad F) (ξ i))) i)
  have hmain : ((1 + ‖fun i => UpperTheory.V.TR.pInf F ((y : Ad F) * algebraMap F (Ad F) (ξ i))‖) ^
      (2 * k))⁻¹ ≤ f 0 * f 1 := by
    rw [two_mul, pow_add, mul_inv]
    exact mul_le_mul
      (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith [hvec 0]) k))
      (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith [hvec 1]) k))
      (by positivity) (hf0 0)
  refine hmain.trans ?_
  have hTr0 : 0 ≤ ((T : ℝ) ^ r)⁻¹ := by positivity
  by_cases h0 : ξ 0 = 0
  · have h1 : ξ 1 ≠ 0 := by
      intro h1
      apply hξ
      funext i
      fin_cases i
      · exact h0
      · exact h1
    calc f 0 * f 1 ≤ W (ξ 0) * (((T : ℝ) ^ r)⁻¹ * W (ξ 1)) :=
          mul_le_mul (hfW 0) (hfT 1 h1) (hf0 1) (hW0 _)
      _ = ((T : ℝ) ^ r)⁻¹ * (W (ξ 0) * W (ξ 1)) := by ring
  · calc f 0 * f 1 ≤ (((T : ℝ) ^ r)⁻¹ * W (ξ 0)) * W (ξ 1) :=
          mul_le_mul (hfT 0 h0) (hfW 1) (hf0 1) (mul_nonneg hTr0 (hW0 _))
      _ = ((T : ℝ) ^ r)⁻¹ * (W (ξ 0) * W (ξ 1)) := by ring

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
