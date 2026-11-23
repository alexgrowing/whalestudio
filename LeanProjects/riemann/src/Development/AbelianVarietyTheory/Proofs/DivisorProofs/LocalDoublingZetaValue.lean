import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupIsoGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDoublingIntegralUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalFunctionLatticeSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumLatticeIndicatorStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

noncomputable section

namespace GlobalTheory.ThK.Bot.SplitCoef

theorem pairing_of_orth {α : Type} [MeasurableSpace α] {m : Measure α} {f p h : α → ℂ} (hf : MemLp f 2 m) (hp : MemLp p 2 m)
    (hh : MemLp h 2 m) (a a' : ℂ) (h1 : ∫ x, (f x - a * p x) * starRingEnd ℂ (h x) ∂m = 0)
    (h2 : ∫ x, p x * starRingEnd ℂ (h x - a' * p x) ∂m = 0) :
    ∫ x, f x * starRingEnd ℂ (h x) ∂m = a * starRingEnd ℂ a' * ∫ x, p x * starRingEnd ℂ (p x) ∂m := by
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by norm_num [ENNReal.inv_two_add_inv_two]⟩
  have hint : ∀ u w : α → ℂ, MemLp u 2 m → MemLp w 2 m → Integrable (fun x => u x * starRingEnd ℂ (w x)) m :=
    fun u w hu hw => MemLp.integrable_mul (p := 2) (q := 2) hu hw.star
  have e1 : ∫ x, (f x - a * p x) * starRingEnd ℂ (h x) ∂m =
      ∫ x, f x * starRingEnd ℂ (h x) ∂m - a * ∫ x, p x * starRingEnd ℂ (h x) ∂m := by
    rw [← integral_const_mul, ← integral_sub (hint f h hf hh) ((hint p h hp hh).const_mul a)]
    congr 1; funext x; ring
  have e2 : ∫ x, p x * starRingEnd ℂ (h x - a' * p x) ∂m =
      ∫ x, p x * starRingEnd ℂ (h x) ∂m - starRingEnd ℂ a' * ∫ x, p x * starRingEnd ℂ (p x) ∂m := by
    rw [← integral_const_mul, ← integral_sub (hint p h hp hh) ((hint p p hp hp).const_mul _)]
    congr 1; funext x; rw [map_sub, map_mul]; ring
  rw [e1, sub_eq_zero] at h1
  rw [e2, sub_eq_zero] at h2
  rw [h1, h2, mul_assoc]

theorem integral_mul_conj_eq {α : Type} [MeasurableSpace α] {m : Measure α} {f : α → ℂ} (hf : AEStronglyMeasurable f m) :
    ∫ x, f x * starRingEnd ℂ (f x) ∂m = (((∫⁻ x, ‖f x‖ₑ ^ 2 ∂m).toReal : ℝ) : ℂ) := by
  have e : ∫ x, f x * starRingEnd ℂ (f x) ∂m = ((∫ x, ‖f x‖ ^ 2 ∂m : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _) (hf.norm.pow 2)]
  congr 2
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem const_eq {z : ℂ} (hz : ‖z‖ = 1) {q : ℝ} (hq : 0 < q) (δ : ℝ) (S P A : ℤ) (h : S - 2 * P = -A) :
    (z ^ S * ((q ^ (δ * (S : ℝ)) : ℝ) : ℂ)) / (z ^ P * ((q ^ (δ * (P : ℝ)) : ℝ) : ℂ)) *
      starRingEnd ℂ (z ^ P * ((q ^ (δ * (P : ℝ)) : ℝ) : ℂ))⁻¹ = z ^ S * ((q ^ (-δ * (A : ℝ)) : ℝ) : ℂ) := by
  have h1 : z ^ P * starRingEnd ℂ (z ^ P) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_zpow, hz]; simp
  have h2 : q ^ (-δ * (A : ℝ)) = q ^ (δ * (S : ℝ)) / (q ^ (δ * (P : ℝ)) * q ^ (δ * (P : ℝ))) := by
    rw [← Real.rpow_add hq, ← Real.rpow_sub hq]
    congr 1
    have : (A : ℝ) = 2 * P - S := by exact_mod_cast (by omega : A = 2 * P - S)
    rw [this]; ring
  rw [h2, map_inv₀, map_mul, Complex.conj_ofReal]
  push_cast
  calc _ = z ^ S * ((q ^ (δ * (S : ℝ)) : ℝ) : ℂ) / ((z ^ P * starRingEnd ℂ (z ^ P)) *
      (((q ^ (δ * (P : ℝ)) : ℝ) : ℂ) * ((q ^ (δ * (P : ℝ)) : ℝ) : ℂ))) := by
        simp only [div_eq_mul_inv, mul_inv]; ring
    _ = _ := by rw [h1, one_mul, mul_div_assoc]

theorem indicator_mul_eq_zero {α : Type} {G P L : Set α} {y : α} (h : y ∈ P ↔ y ∈ G ∧ y ∈ L) (a : ℂ) {b : ℂ} (hb : b ≠ 0) :
    (a • G.indicator (1 : α → ℂ) - (a / b) • b • P.indicator (1 : α → ℂ)) y * L.indicator (1 : α → ℂ) y = 0 ∧
    (b • P.indicator (1 : α → ℂ)) y * (L.indicator (1 : α → ℂ) - b⁻¹ • b • P.indicator (1 : α → ℂ)) y = 0 := by
  by_cases h1 : y ∈ G <;> by_cases h2 : y ∈ L <;> simp [h1, h2] at h <;> simp [h, h1, h2, hb]

theorem coef_split : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r₁ s₁ : ℕ),
    IsPair B M χX χW om r s r₁ s₁ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ (v : Pl F) (ρ : Fn F n d), (∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ) →
    ∀ (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)), IsSplitBasis t X.L b → UnrAt χW (splitPrime t) →
    ∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ (e : Fin n → ℤ) (T : GL (Fin n) (Fv F v)), T.1 = Matrix.diagonal (fun i => ϖ.1 ^ e i) → ∀ k₁ ∈ KGL v n, ∀ k₂ ∈ KGL v n,
    ∀ g ∈ UAt σ X (evFin F v), GlobalTheory.KSplit.locMat t b g = k₁ * T * k₂ →
      coef m om (tens (evFin F v) (M.vac v) ρ) g =
        (chrW χW t ϖ : ℂ) ^ (∑ j, e j) * (((qV F v : ℝ) ^ (-((d : ℝ) / 2) * ((∑ j, |e j| : ℤ) : ℝ)) : ℝ) : ℂ) *
          coef m om (tens (evFin F v) (M.vac v) ρ) 1 := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r₁ s₁ hP _ hB m hm v ρ hR t b hb hU ϖ hϖ e T hT k₁ hk₁ k₂ hk₂ g hg hgm
  classical
  have hcm := hP.base.cm
  haveI := hP.skew.lat
  obtain ⟨c, hc⟩ := exists_isSplitBasis t W.L hcm
  obtain ⟨ι, hι, hvac⟩ := GlobalTheory.T.split_basis_witt_model_local hPr F E σ B n d X W M χX χW om r s r₁ s₁ hP v t b c hb hc
  obtain ⟨ch, hch, -⟩ := GlobalTheory.T.local_unitary_group_iso_GL F E σ B n X hcm ⟨hP.herm.herm, GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hP.herm⟩
    hP.herm.lat v (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hP.base hP.herm v) _
    (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X) t b hb
  let T' : GL (Fin n) (Fv F v) := ⟨Matrix.diagonal fun i => ϖ.1 ^ max (e i) 0, Matrix.diagonal fun i => (ϖ.1 ^ max (e i) 0)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (zpow_ne_zero _ ϖ.ne_zero),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (zpow_ne_zero _ ϖ.ne_zero)⟩
  have hT' : T'.1 = Matrix.diagonal fun i => ϖ.1 ^ max (e i) 0 := rfl
  have hgp : GlobalTheory.KSplit.locMat t b (ch.symm (k₁ * T' * 1)).1 = k₁ * T' * 1 := by rw [← hch, ch.apply_symm_apply]
  obtain ⟨φg, hφg, hAg, hιg⟩ := GlobalTheory.T.weil_vacuum_lattice_indicator hPr F E σ B n d X W M χX χW om r s r₁ s₁ hP v t b c ι hι hvac hU ϖ hϖ e T hT
    k₁ hk₁ k₂ hk₂ g hg hgm
  obtain ⟨φp, hφp, hAp, hιp⟩ := GlobalTheory.T.weil_vacuum_lattice_indicator hPr F E σ B n d X W M χX χW om r s r₁ s₁ hP v t b c ι hι hvac hU ϖ hϖ
    (fun i => max (e i) 0) T' hT' k₁ hk₁ 1 (one_mem _) _ (ch.symm (k₁ * T' * 1)).2 hgp
  have hint := GlobalTheory.T.spherical_function_lattice_support F v n d ϖ hϖ e T hT k₁ hk₁ k₂ hk₂ T' hT'
  rw [mul_one] at hιp
  have hind := fun Y => indicator_mul_eq_zero (y := Y) (G := {Y : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, (((k₁ * T * k₂)⁻¹).1 * Y) i j ∈ v.adicCompletionIntegers F})
    (P := {Y : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, (((k₁ * T')⁻¹).1 * Y) i j ∈ v.adicCompletionIntegers F})
    (L := {Y : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers F}) (hint Y)
  have hv : M.vac v ∈ SB (Fin n × Fin d → Fv F v) := (hP.good.vac v).1
  have hz : ‖(chrW χW t ϖ : ℂ)‖ = 1 := (GlobalTheory.ChrWLocal.chrW_local F E χW hP.hW v t).1.2 ϖ
  have hq : (0 : ℝ) < qV F v := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero v)
  set cg : ℂ := (chrW χW t ϖ : ℂ) ^ (∑ j, e j) * (((qV F v : ℝ) ^ ((d : ℝ) / 2 * ((∑ j, e j : ℤ) : ℝ)) : ℝ) : ℂ) with hcg
  set cp : ℂ := (chrW χW t ϖ : ℂ) ^ (∑ j, max (e j) 0) *
    (((qV F v : ℝ) ^ ((d : ℝ) / 2 * ((∑ j, max (e j) 0 : ℤ) : ℝ)) : ℝ) : ℂ) with hcp
  have hcp0 : cp ≠ 0 := mul_ne_zero (zpow_ne_zero _ (Units.ne_zero _))
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne')
  have o1 := GlobalTheory.T.local_doubling_integral_unramified F E σ B n d X W M χX χW om r s r₁ s₁ hP m hm v ρ hR t b c ι hι (φg - (cg / cp) • φp)
    (Submodule.sub_mem _ hφg (Submodule.smul_mem _ _ hφp)) (M.vac v) hv (fun Y => by
      rw [map_sub, map_smul, hιg, hιp, hvac]
      exact (hind Y cg hcp0).1)
  have o2 := GlobalTheory.T.local_doubling_integral_unramified F E σ B n d X W M χX χW om r s r₁ s₁ hP m hm v ρ hR t b c ι hι φp hφp (M.vac v - cp⁻¹ • φp)
    (Submodule.sub_mem _ hv (Submodule.smul_mem _ _ hφp)) (fun Y => by
      rw [map_sub, map_smul, hιp, hvac]
      exact (hind Y cg hcp0).2)
  obtain ⟨rfl⟩ := hB
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  have hL : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), MemLp (tens (evFin F v) φ ρ) 2 m := fun φ hφ =>
    GlobalTheory.WeilM.schA_memLp_two F _ m hm _ (hR φ hφ).2
  have key := pairing_of_orth (hL _ hφg) (hL _ hφp) (hL _ hv) (cg / cp) cp⁻¹
    (by rw [← o1]; congr 1; funext x; simp only [tens, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
    (by rw [← o2]; congr 1; funext x; simp only [tens, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; congr 2; ring)
  have hun := hP.weil.isUSplitting.unit m hm ((ch.symm (k₁ * T' * 1)).1, 1) _ (hR _ hv).2
  rw [hAp ρ (hR _ hv)] at hun
  unfold coef
  rw [hAg ρ (hR _ hv), key, show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply,
    integral_mul_conj_eq (hL _ hφp).1, integral_mul_conj_eq (hL _ hv).1, hun, hcg, hcp,
    const_eq hz hq _ _ _ (∑ j, |e j|)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases le_total (e j) 0 with h | h
  · rw [max_eq_right h, abs_of_nonpos h]; ring
  · rw [max_eq_left h, abs_of_nonneg h]; ring

end GlobalTheory.ThK.Bot.SplitCoef

end
