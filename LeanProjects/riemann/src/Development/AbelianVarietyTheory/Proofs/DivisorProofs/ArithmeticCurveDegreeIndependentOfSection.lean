import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaArithmeticCurveRationalFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDivisorDegreeZeroFiniteFieldCurveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveIndep

variable {Y : Scheme.{0}} [IsIntegral Y] {L : LB Y}

theorem exists_ratio (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ} (hr : IsRatSec L r)
    (hr' : IsRatSec L r') : ∃ f : Y.functionFieldˣ, ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f := by
  obtain ⟨i₀, h₀⟩ := exists_chart hL (genericPoint Y)
  refine ⟨(r i₀)⁻¹ * r' i₀, fun i hi => Units.ext ?_⟩
  have e := hr i i₀ ⟨hi, h₀⟩
  have e' := hr' i i₀ ⟨hi, h₀⟩
  have h0 : (r i₀ : Y.functionField) ≠ 0 := (r i₀).ne_zero
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [e', e]
  field_simp

theorem div_eq_add_principal (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ} (hr : IsRatSec L r)
    (hr' : IsRatSec L r') (f : Y.functionFieldˣ) (hf : ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f) :
    divOfRatSec hL hr' = divOfRatSec hL hr + CartierDiv.principal f :=
  (presents_divOfRatSec hL hr').unique ⟨hL, hr', fun i x hx => by
    rw [hf i (gen_mem hx)]
    exact ((presents_divOfRatSec hL hr).add_principal f).isEqn i x hx⟩

theorem mult_eq_add_ord [IsLocallyNoetherian Y] (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (hr' : IsRatSec L r') (f : Y.functionFieldˣ)
    (hf : ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f) (z : Y) :
    (divOfRatSec hL hr').mult z = (divOfRatSec hL hr).mult z + Scheme.ord (f : Y.functionField) z := by
  rw [div_eq_add_principal hL hr hr' f hf, CartierDiv.mult_add,
    (CartierDiv.isEqn_principal f z).mult_eq]

end GlobalTheory.CurveIndep

namespace GlobalTheory.CurveIndep

open Classical in

theorem mixArch_zero {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}
    (L : Fin 0 → HermLB q) (N : HermLB q) {r : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r) :
    mixArch L N hr = (HermLB.triv q).archInt N 0 hr := by
  have h (n : Fin 0 → ℤ) : (comb L n).archInt N 0 hr = (HermLB.triv q).archInt N 0 hr := by
    have e : comb L n = HermLB.triv q := by simp [comb]
    rw [e]
  have e (S : Finset (Fin 0)) : S.card = 0 := by simp [Subsingleton.elim S ∅]
  simp [mixArch, FibreProj.pol, h, e]

theorem archInt_eq_zero {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (L M : HermLB q) (e : ℕ)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : L.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
  haveI := hq σ
  simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (0 + 1 : ℕ) → ∀ (N : HermLB q) (L : Fin 0 → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr = recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr' := by
  intro k _ Y _ _ q hA hd N L r hr r' hr'
  obtain ⟨f, hf⟩ := exists_ratio N.isLB hr hr'
  have := hA.isNoetherian
  set c : Y → ℝ := fun z => Real.log (Nat.card (Y.residueField z)) with hc
  have hfin (D : CartierDiv Y) : (Function.support fun z => (D.mult z : ℝ) * c z).Finite :=
    (CartierDiv.finite_support_mult D).subset fun z hz h0 => hz (by simp [h0])
  have hord (z : Y) : Scheme.ord (f : Y.functionField) z = (CartierDiv.principal f).mult z :=
    ((CartierDiv.isEqn_principal f z).mult_eq).symm
  have hsum : ∑ᶠ z, ((N.div hr').mult z : ℝ) * c z =
      ∑ᶠ z, ((N.div hr).mult z : ℝ) * c z + ∑ᶠ z, (Scheme.ord (f : Y.functionField) z : ℝ) * c z := by
    simp_rw [hord]
    rw [← finsum_add_distrib (hfin _) (hfin _)]
    refine finsum_congr fun z => ?_
    rw [HermLB.div, HermLB.div, mult_eq_add_ord N.isLB hr hr' f hf z, hord]
    push_cast
    ring
  unfold recVal
  rw [hsum, mixArch_zero, mixArch_zero]
  rcases GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hA (0 + 1) hd with ⟨l, hl, ⟨alg⟩, hemp⟩ | ⟨e, he, hq⟩
  · have h0 : ∑ᶠ z, (Scheme.ord (f : Y.functionField) z : ℝ) * c z = 0 :=
      @GlobalTheory.T.principalDivisor_degree_zero_finiteField_curve k _ Y _ _ q hA hd l hl alg (f : Y.functionField) f.ne_zero
    rw [h0, archInt_eq_zero hemp, archInt_eq_zero hemp]
    ring
  · obtain rfl : e = 0 := by omega
    have := hq.finite_emb
    rw [GlobalTheory.ArchDimZero.main k Y q hq N (HermLB.triv q) r hr,
      GlobalTheory.ArchDimZero.main k Y q hq N (HermLB.triv q) r' hr',
      GlobalTheory.T.productFormula_arithmeticCurve_rationalFunction k Y q hq (f : Y.functionField) f.ne_zero]
    have hlog (σ : k →+* ℂ) (y : CxPts q σ) : logNorm (N.φ σ) r' y =
        Real.log ‖ratVal (f : Y.functionField) y‖ + logNorm (N.φ σ) r y := by
      have hy := GlobalTheory.TwistTop.under_eq_genericPoint hq y
      have hreg (g : Y.functionField) : RegAt (under y) g := by
        rw [hy]; exact regAt_genericPoint g
      have hunit (g : Y.functionFieldˣ) : UnitAt (under y) (g : Y.functionField) := by
        rw [hy]; exact unitAt_genericPoint g.ne_zero
      have hi : genericPoint Y ∈ N.B.U (pick (N.φ σ).isLB y) :=
        gen_mem (mem_ptsIn.1 (mem_pick (N.φ σ).isLB y))
      simp only [logNorm]
      rw [hf _ hi, Units.val_mul, ratVal_mul (hreg _) (hreg _), norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero (hunit _)))
          (norm_ne_zero_iff.2 (ratVal_ne_zero (hunit f)))]
      ring
    have hσ (σ : k →+* ℂ) : ∑ᶠ y : CxPts q σ, logNorm (N.φ σ) r' y =
        ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (f : Y.functionField) y‖ + ∑ᶠ y : CxPts q σ, logNorm (N.φ σ) r y := by
      have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
      simp_rw [hlog σ]
      exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
    simp_rw [hσ]
    rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    ring

end GlobalTheory.CurveIndep
