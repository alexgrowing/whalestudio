import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentHaarDomainStatement

noncomputable section

namespace GlobalTheory.SplitUniq

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

open Matrix GlobalTheory.LeviLine

theorem split2_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} {W : Spc F E (a + a')} {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {X : Chars F E}
    (hlt : a' < a)
    (hdom : ∃ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ ∧ μ 𝓕 = 1)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m ∧ 1 < (absE F E t : ℝ))
    {f fa fb fa' fb' : UA σ W.J → ℂ} (h₁ : Split2 W₁ H' X f fa fb) (h₂ : Split2 W₁ H' X f fa' fb') :
    fa = fa' ∧ fb = fb' := by
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := hdom
  obtain ⟨t, m, hm, ht⟩ := hlevi
  have hsum : ∀ h, fa h + fb h = fa' h + fb' h := by
    intro h
    have e1 := h₁.1 μ 𝓕 hμ h𝓕 h1 h
    have e2 := h₂.1 μ 𝓕 hμ h𝓕 h1 h
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
  have key : ∀ h, fa h = fa' h := by
    intro h
    by_contra hne
    have hA := h₁.2.1 t m hm h
    have hA' := h₂.2.1 t m hm h
    have hB := h₁.2.2 t m hm h
    have hB' := h₂.2.2 t m hm h
    have s1 := hsum (m * h)
    have s0 := hsum h
    set cA' : ℂ := (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) with hcA
    set cB : ℂ := (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) with hcB
    have e : cA' * (fa h - fa' h) = cB * (fa h - fa' h) := by
      linear_combination -hA + hA' + s1 - hB + hB' - cB * s0
    have e' : cA' = cB := mul_right_cancel₀ (sub_ne_zero.2 hne) e
    have n1 : ‖cA'‖ = (absE F E t : ℝ) ^ ((a' : ℝ) / 2) := by
      rw [hcA, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    have n2 : ‖cB‖ = (absE F E t : ℝ) ^ ((a : ℝ) / 2) := by
      rw [hcB, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    have hlt' : (a' : ℝ) / 2 < (a : ℝ) / 2 := by
      have : (a' : ℝ) < a := by exact_mod_cast hlt
      linarith
    have := Real.rpow_lt_rpow_of_exponent_lt ht hlt'
    rw [← n1, ← n2, e'] at this
    exact lt_irrefl _ this
  refine ⟨funext key, funext fun h => ?_⟩
  have := hsum h
  rw [key h] at this
  exact add_left_cancel this

theorem exists_levi_skew {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E d₁} {H' : Plane E n d₁} {i₀ i₁ r s : ℕ}
    (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) :
    ∃ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m ∧ 1 < (absE F E t : ℝ) := by
  have hcm := hB.cm
  set c : AE F E →+* AE F E := (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom with hcdef
  have hc : ∀ r, c (c r) = r := cA_invol hcm
  have hJ : ∀ i j, c (incM F W.J j i) = -incM F W.J i j := by
    intro i j
    change cA σ (inclR (F := F) (AF F) (W.J j i)) = -inclR (F := F) (AF F) (W.J i j)
    rw [cA_inclR, hW.skew i j, map_neg]
  have hxx : sf c (incM F W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [sf_inc, hH.xx, map_zero]
  have hyy : sf c (incM F W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [sf_inc, hH.yy, map_zero]
  have hxy : sf c (incM F W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [sf_inc, hH.xy, map_one]
  have hyx : sf c (incM F W.J) (incV F H'.y) (incV F H'.x) = -1 := by rw [sf_skew c _ hc hJ, hxy, map_one]
  set t : (AE F E)ˣ := (GlobalTheory.Eis.Conv.halfE F E)⁻¹ with htdef
  have hts : (t : AE F E) * c (c (↑t⁻¹ : AE F E)) = 1 := by rw [hc, Units.mul_inv]
  have hst : c (↑t⁻¹ : AE F E) * c (t : AE F E) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  let L := levi c (incM F W.J) (incV F H'.x) (incV F H'.y)
  let g : GL (Fin n) (AE F E) :=
    ⟨L t (c ↑t⁻¹), L ↑t⁻¹ (c t), by
      rw [levi_mul hc hJ hxx hyy hxy, Units.mul_inv, ← map_mul, Units.inv_mul, map_one, levi_one],
      by rw [levi_mul hc hJ hxx hyy hxy, Units.inv_mul, ← map_mul, Units.mul_inv, map_one, levi_one]⟩
  have hg : g ∈ UG (cA σ) (incM F W.J) := levi_unitary hc hJ hxx hyy hxy hts hst
  refine ⟨t, ⟨g, hg⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · change L t (c ↑t⁻¹) *ᵥ incV F H'.x = _
    rw [levi_mulVec, hxx, hxy]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) *ᵥ incV F H'.y = c ↑t⁻¹ • incV F H'.y
    rw [levi_mulVec, hyy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) * incM F H'.ι = incM F H'.ι * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))
    rw [Matrix.mul_one]
    refine ext_mulVec_single fun k => ?_
    have hcol : incM F H'.ι *ᵥ Pi.single k 1 = incV F (H'.ι *ᵥ Pi.single k 1) := by
      ext i
      simp [mulVec_single_one, incM, incV]
    rw [← mulVec_mulVec, hcol]
    exact levi_mulVec_of_orth _ _ _ _ (by rw [sf_inc, (hH.orth _).1, map_zero]) (by rw [sf_inc, (hH.orth _).2, map_zero])
  · have h1 := GlobalTheory.Eis.Conv.absE_halfE F E σ hcm
    have h2 : absE F E t * absE F E (GlobalTheory.Eis.Conv.halfE F E) = 1 := by
      rw [← map_mul, htdef, inv_mul_cancel, map_one]
    rw [h1] at h2
    have h3 : absE F E t = (4 : ℝ≥0) ^ Fintype.card (InfinitePlace F) := by
      rw [← mul_one (absE F E t), ← inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (4 : ℝ≥0) ≠ 0)), ← mul_assoc, h2, one_mul]
    rw [h3]
    have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    push_cast
    exact one_lt_pow₀ (by norm_num) hpos.ne'

theorem split2_unique_skew : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (W : Spc F E (a + a')) (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ r s r₁ s₁ : ℕ) (X : Chars F E), B.IsGood σ → a' < a → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ f fa fb fa' fb' : UA σ W.J → ℂ, Split2 W₁ H' X f fa fb → Split2 W₁ H' X f fa' fb' → fa = fa' ∧ fb = fb' := by
  intro _ F E _ _ _ _ _ σ B a a' W d₁ W₁ H' i₀ i₁ r s r₁ s₁ X hB hlt hW hW₁ hH f fa fb fa' fb' h₁ h₂
  exact split2_eq hlt (GlobalTheory.T.exists_unipotent_haar_domain F E σ B (a + a') d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hH) (exists_levi_skew hB hW hH) h₁ h₂

end GlobalTheory.SplitUniq

end
