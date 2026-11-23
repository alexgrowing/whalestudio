import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Formalism.LocalToGlobal.UnitaryNorms.CharProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.FinprodNormEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScalField

open Formalism.L2.Host

def sqN {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : ℝ :=
  Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)

theorem absNorm_pos {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem sqN_pos {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : 0 < sqN v :=
  Real.sqrt_pos.2 (absNorm_pos v)

theorem sqN_sq {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    sqN v ^ 2 = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
  Real.sq_sqrt (absNorm_pos v).le

theorem cpow_neg_half (n : ℕ) :
    ((n : ℕ) : ℂ) ^ (-(((-1 / 2 : ℝ)) : ℂ)) = ((Real.sqrt n : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  congr 1
  ring

theorem ordF_natCast {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (u : Eˣ) (M₀ : ℕ)
    (hu : (u : E) = ((M₀ : ℕ) : E)) :
    ordF v u = ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {((M₀ : ℕ) : 𝓞 E)})).factors : ℤ) := by
  have h0 : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((M₀ : ℕ) : E) = 0 := by
      have := congrArg (algebraMap (𝓞 E) E) h
      simpa using this
    exact u.ne_zero (hu.trans this)
  have e : (u : E) = algebraMap (𝓞 E) E ((M₀ : ℕ) : 𝓞 E) := by rw [hu, map_natCast]
  rw [ordF, e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v h0,
    WithZero.log_exp, neg_neg]

end GlobalTheory.FlipScalField

namespace GlobalTheory.FlipScalField
open Formalism.L2.Host

set_option maxHeartbeats 800000 in

theorem mem_fieldRange : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ r w : ℕ) (u a : Eˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (k : Type) [Field k] (σ : k →+* ℂ), Odd w → (u : E) = ((M₀ : ℕ) : E) → IsIntegral ℤ (a : E) → (∀ v ∈ T, ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∉ v.asIdeal → χ.UnrAt v) → χ.ValuesIn (-1 / 2) σ → (∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| ^ (-(w : ℝ) / 2) : ℝ) : ℂ)) → (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1) → (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) * ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ ∈ σ.fieldRange := by
  intro E _ _ χ M₀ r w u a T k _ σ hw hu ha hT hunr hval hinf hTa hST
  classical
  have hM0 : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((M₀ : ℕ) : E) = 0 := by
      have := congrArg (algebraMap (𝓞 E) E) h
      simpa using this
    exact u.ne_zero (hu.trans this)
  have hSfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_
    · rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  set S := hSfin.toFinset with hSdef
  have hmemS : ∀ v, v ∈ S ↔ ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal := fun v => Set.Finite.mem_toFinset _
  set R := (GlobalTheory.HeckeProduct.finite_ordF a).toFinset with hRdef
  have hR : ∀ v, v ∉ R → ordF v a = 0 := fun v hv => by
    by_contra h; exact hv ((Set.Finite.mem_toFinset _).2 h)
  have hTS : T ⊆ S := fun v hv => (hmemS v).2 (hT v hv)
  have hoST : ∀ v ∈ S, v ∉ T → ordF v a = 0 := fun v hv hvT => by
    rw [ordF, (hST v ((hmemS v).1 hv) hvT).2, WithZero.log_one, neg_zero]
  have hoT : ∀ v ∈ T, ordF v a = ordF v u := fun v hv => by
    rw [ordF, ordF, (hTa v hv).2, hu]
  have hPR := Formalism.L2.Host.HChar.productRule χ S (fun v hv => hunr v (fun h => hv ((hmemS v).2 h))) a
  have hloc : ∏ v ∈ S, χ.locK v a = ∏ v ∈ T, χ.locK v u := by
    rw [← Finset.prod_subset hTS (fun v hv hvT => (hST v ((hmemS v).1 hv) hvT).1)]
    exact Finset.prod_congr rfl fun v hv => (hTa v hv).1
  have hfin : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v a) =
      ∏ v ∈ R \ S, χ.val v ^ ordF v a := by
    apply finprod_mem_eq_prod_of_subset (s := {v | v ∉ S})
    · rintro v ⟨hv1, hv2⟩
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe]
      refine ⟨?_, hv1⟩
      by_contra h
      exact hv2 (by simp [hR v h])
    · intro v hv
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hv
      exact hv.2
  rw [hloc, hfin] at hPR
  choose! y hy using hval
  have hvalv : ∀ v, v ∉ S → ((χ.val v : ℂˣ) : ℂ) = σ (y v) / ((sqN v : ℝ) : ℂ) := fun v hv => by
    have h1 := hy v (hunr v fun h => hv ((hmemS v).2 h))
    have h2 : ((sqN v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sqN_pos v).ne'
    rw [h1, HChar.valTw, cpow_neg_half, ← sqN, mul_div_assoc, div_self h2, mul_one]
  obtain ⟨y0, hy0⟩ := hinf
  set Q : ℝ := ∏ v ∈ R, sqN v ^ ordF v a with hQ
  have hQpos : 0 < Q := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hNa : |((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| = Q ^ 2 := by
    rw [← PI.AlgValsFin.W.prod_norm_emb, PI.AlgValsFin.W.prodNorm a R hR, hQ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← sqN_sq v, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  have hinfv : ((χ.inf a : ℂˣ) : ℂ) = σ y0 * (((Q ^ w)⁻¹ : ℝ) : ℂ) := by
    rw [hy0, hNa]
    congr 2
    rw [← Real.rpow_natCast Q 2, ← Real.rpow_mul hQpos.le, ← Real.rpow_natCast, ← Real.rpow_neg hQpos.le]
    congr 1
    push_cast
    ring
  set A : ℝ := ∏ v ∈ T, sqN v ^ ordF v a with hA
  set B : ℝ := ∏ v ∈ R \ S, sqN v ^ ordF v a with hB
  have hApos : 0 < A := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hBpos : 0 < B := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hQAB : Q = A * B := by
    rw [hQ, ← Finset.prod_inter_mul_prod_diff R S]
    congr 1
    have e1 : ∏ v ∈ R ∩ S, sqN v ^ ordF v a = ∏ v ∈ S, sqN v ^ ordF v a :=
      Finset.prod_subset Finset.inter_subset_right fun v hv hv' => by
        rw [hR v (fun h => hv' (Finset.mem_inter.2 ⟨h, hv⟩)), zpow_zero]
    have e2 : ∏ v ∈ T, sqN v ^ ordF v a = ∏ v ∈ S, sqN v ^ ordF v a :=
      Finset.prod_subset hTS fun v hv hvT => by rw [hoST v hv hvT, zpow_zero]
    rw [e1, ← e2]
  have hprodval : ∏ v ∈ R \ S, ((χ.val v : ℂˣ) : ℂ) ^ ordF v a =
      σ (∏ v ∈ R \ S, y v ^ ordF v a) / ((B : ℝ) : ℂ) := by
    rw [map_prod, hB, Complex.ofReal_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hvalv v (Finset.mem_sdiff.1 hv).2, map_zpow₀, Complex.ofReal_zpow, div_zpow]
  have key := congrArg (fun z : ℂˣ => (z : ℂ)) hPR
  simp only [Units.val_mul, Units.val_one, Units.coe_prod, Units.val_zpow_eq_zpow_val] at key
  rw [hinfv, hprodval, hQAB] at key
  set P : ℂ := ∏ v ∈ T, ((χ.locK v u : ℂˣ) : ℂ) with hPdef
  set Y : k := ∏ v ∈ R \ S, y v ^ ordF v a with hY
  have h1 : σ y0 ≠ 0 := fun h => by rw [h] at key; simp at key
  have h2 : σ Y ≠ 0 := fun h => by rw [h] at key; simp at key
  have hA0 : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have hB0 : ((B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hP : P = ((A : ℝ) : ℂ) ^ w * ((B : ℝ) : ℂ) ^ (w + 1) / (σ y0 * σ Y) := by
    rw [eq_div_iff (mul_ne_zero h1 h2)]
    push_cast at key
    field_simp at key
    linear_combination key

  have hsqrt : Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) =
      A ^ (r * w) := by
    rw [← Real.sqrt_sq (pow_nonneg hApos.le _)]
    congr 1
    push_cast
    rw [hA, ← Finset.prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hoT v hv, ordF_natCast v u M₀ hu, HeightOneSpectrum.maxPowDividing, map_pow, zpow_natCast]
    push_cast
    rw [← sqN_sq v]
    ring
  set q : ℚ := ∏ v ∈ R \ S, ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ ordF v a with hq
  have hqB : ((q : ℚ) : ℂ) = ((B : ℝ) : ℂ) ^ 2 := by
    have : ((q : ℚ) : ℝ) = B ^ 2 := by
      rw [hq, hB, ← Finset.prod_pow]
      push_cast
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [← sqN_sq v, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
    rw [← Complex.ofReal_ratCast, this, Complex.ofReal_pow]
  obtain ⟨m, rfl⟩ := hw
  have heq : (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) *
      ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * (2 * m + 1)) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ =
      (((q : ℚ) : ℂ) ^ (m + 1)) ^ r * ((σ y0 * σ Y)⁻¹) ^ r := by
    rw [hsqrt, Finset.prod_pow, ← hPdef, hP, hqB]
    push_cast
    field_simp
    ring
  rw [heq]
  refine mul_mem (pow_mem (pow_mem (SubfieldClass.ratCast_mem _ q) _) _) (pow_mem (inv_mem (mul_mem ?_ ?_)) _)
  · exact ⟨y0, rfl⟩
  · exact ⟨Y, rfl⟩

end GlobalTheory.FlipScalField
