import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent

noncomputable section

open NumberField Module ReciprocityTheory.GeometryOfNumbersTheory
open scoped nonZeroDivisors

namespace GlobalTheory.CM

open NumberField Module in
open scoped nonZeroDivisors in

theorem _root_.GlobalTheory.CM.deg_ideal_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V) (Λ : Submodule (𝓞 K) V) {v : V} (hv : v ≠ 0)
    {m : (K →+* ℂ) → ℝ} (hm : ∀ s, 0 < m s) (hf : ∀ s, (h.form s v v).re = m s)
    {𝔠 : FractionalIdeal (𝓞 K)⁰ K} (h𝔠 : 𝔠 ≠ 0) (hΛ : ∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ t ∈ 𝔠) :
    _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = -Real.log (FractionalIdeal.absNorm 𝔠) / finrank ℚ K - _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K m / 2 := by
  set φ : K →ₗ[𝓞 K] V := (LinearMap.toSpanSingleton K V v).restrictScalars (𝓞 K) with hφ
  have hφapp : ∀ t, φ t = t • v := fun t => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    simp only [hφapp] at hab
    exact smul_left_injective K hv hab
  have hΛmap : Λ = (𝔠 : Submodule (𝓞 K) K).map φ := by
    ext z
    rw [hΛ, Submodule.mem_map]
    constructor
    · rintro ⟨t, rfl, ht⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, rfl, ht⟩
  have hform : ∀ s, h.form s v v = (m s : ℂ) := by
    intro s
    have hc := h.conj_symm s v v
    apply Complex.ext
    · simp [hf s]
    · simp only [Complex.ofReal_im]
      exact Complex.conj_eq_iff_im.mp hc
  have hcFG : (𝔠 : Submodule (𝓞 K) K).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔠
  obtain ⟨r, w, hw⟩ := _root_.ReciprocityTheory.GeometryOfNumbersTheory.exists_isFullRankFamily_of_fg (𝔠 : Submodule (𝓞 K) K) hcFG
  have hw' := hw
  unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame at hw'
  obtain ⟨hwmem, hwli, hwspan⟩ := hw'
  have hrange : Set.range (fun i => φ (w i)) = φ '' Set.range w := Set.range_comp φ w
  have hframe : _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K Λ (fun i => φ (w i)) := by
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [hΛmap]; exact Submodule.mem_map_of_mem (hwmem i)
    · exact hwli.map' (LinearMap.toSpanSingleton K V v) (LinearMap.ker_toSpanSingleton K hv)
    · intro z hz
      rw [SetLike.mem_coe, hΛ] at hz
      obtain ⟨t, rfl, ht⟩ := hz
      have ht' : t ∈ Submodule.span K (Set.range w) := hwspan ht
      have hmem := Submodule.mem_map_of_mem (f := LinearMap.toSpanSingleton K V v) ht'
      rw [Submodule.map_span, ← Set.range_comp] at hmem
      exact hmem
  have hΛFG : Λ.FG := hΛmap ▸ hcFG.map φ
  have hrel : (Submodule.span (𝓞 K) (Set.range (fun i => φ (w i)))).toAddSubgroup.relIndex
      Λ.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range w)).toAddSubgroup.relIndex
      (𝔠 : Submodule (𝓞 K) K).toAddSubgroup := by
    rw [hΛmap, hrange, ← Submodule.map_span, Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hgram : ∀ σ, h.gram σ (fun i => φ (w i)) = (_root_.GlobalTheory.lineHerm m hm).gram σ w := by
    intro σ
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram
    ext i j
    simp only [Matrix.of_apply, hφapp, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_smul_left, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.smul_right, hform]
    unfold _root_.GlobalTheory.lineHerm
    simp only
    ring
  calc _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily h Λ (fun i => φ (w i)) := _root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hΛFG hframe
    _ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily (_root_.GlobalTheory.lineHerm m hm) (𝔠 : Submodule (𝓞 K) K) w := by
      unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily
      rw [hrel]
      simp_rw [hgram]
    _ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg (_root_.GlobalTheory.lineHerm m hm) (𝔠 : Submodule (𝓞 K) K) :=
      (_root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily _ hcFG hw).symm
    _ = _ := _root_.GlobalTheory.deg_lineHerm m hm h𝔠

open NumberField Module in
open scoped nonZeroDivisors in

theorem _root_.GlobalTheory.CM.two_mul_deg_dual_line : ∀ (E K V : Type) [Field E] [NumberField E] [IsCMField E]
    [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V)
    (Λ : Submodule (𝓞 K) V) (v : V) (τ : E →+* K) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (β : E) (n : (K →+* ℂ) → ℝ), 𝔞 ≠ 0 → v ≠ 0 → (∀ s, 0 < n s) →
    (∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0) →
    (∀ s, (h.form s v v).re = (s (τ β)).re * n s) →
    (∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ ∀ b ∈ 𝔞, IsIntegral ℤ (t * τ (β * IsCMField.complexConj E b))) →
    2 * _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = (2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) +
      Real.log |(Algebra.norm ℚ β : ℚ)|) / Module.finrank ℚ E - _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
  intro E K V _ _ _ _ _ _ _ _ _ h Λ v τ 𝔞 β n h𝔞 hv hn hβ hf hΛ
  have hβ0 : β ≠ 0 := by
    rintro rfl
    obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
    simpa using (hβ s).1
  set 𝔞' : FractionalIdeal (𝓞 E)⁰ E :=
    FractionalIdeal.spanSingleton (𝓞 E)⁰ β * _root_.GlobalTheory.conjFrac 𝔞 with h𝔞'def
  have h𝔞' : 𝔞' ≠ 0 :=
    mul_ne_zero (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
      (_root_.GlobalTheory.conjFrac_ne_zero h𝔞)
  obtain ⟨𝔟, h𝔟, h𝔟span, h𝔟log⟩ := _root_.GlobalTheory.exists_fractionalIdeal_eq_span_image τ h𝔞'
  have hm : ∀ s : K →+* ℂ, 0 < (s (τ β)).re * n s := fun s => mul_pos (hβ (s.comp τ)).1 (hn s)
  have hmemΛ : ∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ t ∈ 𝔟⁻¹ := by
    intro z
    rw [hΛ]
    refine exists_congr fun t => and_congr_right fun _ => ?_
    rw [FractionalIdeal.mem_inv_iff h𝔟]
    constructor
    · intro H y hy
      rw [← FractionalIdeal.mem_coe, h𝔟span] at hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, hx, rfl⟩ := hx
        rw [SetLike.mem_coe, h𝔞'def, FractionalIdeal.mem_singleton_mul] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [_root_.GlobalTheory.mem_conjFrac] at hz
        have key := H _ hz
        rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z = IsCMField.complexConj E z from rfl,
          IsCMField.complexConj_apply_apply] at key
        exact (_root_.GlobalTheory.mem_one_fractionalIdeal_iff).2 key
      | zero => simp
      | add x y _ _ hx hy =>
        rw [mul_add, ← FractionalIdeal.mem_coe]
        rw [← FractionalIdeal.mem_coe] at hx hy
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [mul_smul_comm, ← FractionalIdeal.mem_coe]
        exact Submodule.smul_mem _ a hx
    · intro H b hb
      rw [← _root_.GlobalTheory.mem_one_fractionalIdeal_iff]
      apply H
      rw [← FractionalIdeal.mem_coe, h𝔟span]
      apply Submodule.subset_span
      refine ⟨β * IsCMField.complexConj E b, ?_, rfl⟩
      rw [SetLike.mem_coe, h𝔞'def, FractionalIdeal.mem_singleton_mul]
      exact ⟨IsCMField.complexConj E b, _root_.GlobalTheory.cc_mem_conjFrac.2 hb, rfl⟩
  have hdeg := _root_.GlobalTheory.CM.deg_ideal_smul h Λ hv hm hf (inv_ne_zero h𝔟) hmemΛ
  have hsumE : ∑ s : E →+* ℂ, Real.log (s β).re = Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| := by
    rw [← Real.log_prod (fun s _ => ne_of_gt (hβ s).1)]
    congr 1
    have hprodC : ((∏ s : E →+* ℂ, (s β).re : ℝ) : ℂ) = (((Algebra.norm ℚ β : ℚ) : ℝ) : ℂ) := by
      push_cast
      have hre : ∀ s : E →+* ℂ, ((s β).re : ℂ) = s β := fun s =>
        Complex.ext (by simp) (by simp [(hβ s).2])
      simp_rw [hre]
      rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun s => s β) (fun σ => σ β)
        (fun s => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ β]
      simp
    have hprod : (∏ s : E →+* ℂ, (s β).re : ℝ) = ((Algebra.norm ℚ β : ℚ) : ℝ) := by
      exact_mod_cast hprodC
    rw [hprod, abs_of_pos]
    rw [← hprod]
    exact Finset.prod_pos fun s _ => (hβ s).1
  have hM : _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => (s (τ β)).re * n s) =
      Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| / finrank ℚ E + _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
    have hsplit : _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => (s (τ β)).re * n s) =
        _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => ((s.comp τ) β).re) + _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
      unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog
      rw [← add_div, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      exact Real.log_mul (ne_of_gt (hβ (s.comp τ)).1) (ne_of_gt (hn s))
    have hres := _root_.GlobalTheory.meanLog_comp τ (fun s : E →+* ℂ => (s β).re)
    rw [hsplit, hres, ← hsumE]
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog
    rfl
  have hlog𝔞' : Real.log (FractionalIdeal.absNorm 𝔞' : ℝ) =
      Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| + Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) := by
    rw [h𝔞'def, map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs,
      Real.log_mul, _root_.GlobalTheory.log_absNorm_conjFrac h𝔞]
    · exact abs_ne_zero.mpr (Rat.cast_ne_zero.mpr ((Algebra.norm_ne_zero_iff).mpr hβ0))
    · exact Rat.cast_ne_zero.mpr (fun h0 => _root_.GlobalTheory.conjFrac_ne_zero h𝔞
        (FractionalIdeal.absNorm_eq_zero_iff.mp h0))
  have hinv : -Real.log (FractionalIdeal.absNorm 𝔟⁻¹ : ℝ) / finrank ℚ K =
      Real.log (FractionalIdeal.absNorm 𝔟 : ℝ) / finrank ℚ K := by
    rw [map_inv₀, Rat.cast_inv, Real.log_inv, neg_neg]
  rw [hdeg, hinv, h𝔟log, hlog𝔞', hM]
  ring

end GlobalTheory.CM
