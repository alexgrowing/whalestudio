import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

section Lat

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {n : ℕ}

theorem diag_ne_zero_of_linearIndependent {w : Fin n → U} {g : Matrix (Fin n) (Fin n) C}
    (hg : ∀ i j, i < j → g i j = 0) (h : LinearIndependent C fun i => ∑ j, g i j • w j) (i : Fin n) : g i i ≠ 0 := by
  have hl : LinearIndependent C g.row := LinearIndependent.of_comp (Fintype.linearCombination C w) h
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hl)
  rw [Matrix.det_of_lowerTriangular _ fun i j hij => hg i j hij] at hu
  exact Finset.prod_ne_zero_iff.1 hu.ne_zero i (Finset.mem_univ i)

theorem IsLatBasis.diag_le {v : Valuation C ℝ≥0} (hv : v.Integers O) {La : Submodule O U} {w : Fin n → U}
    {g g' : Matrix (Fin n) (Fin n) C} (hg : ∀ i j, i < j → g i j = 0) (hg' : ∀ i j, i < j → g' i j = 0)
    (h : IsLatBasis C La fun i => ∑ j, g i j • w j) (i : Fin n) (h' : ∑ j, g' i j • w j ∈ La) :
    v (g' i i) ≤ v (g i i) := by
  have hd : IsUnit g.det := lowerTri_isUnit_det g hg fun i => (diag_ne_zero_of_linearIndependent hg h.1 i).isUnit
  have e : (g' * g⁻¹) * g = g' := Matrix.nonsing_inv_mul_cancel_right _ _ hd
  have e1 : ∑ j, (g' * g⁻¹) i j • ∑ k, g j k • w k = ∑ k, g' i k • w k := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, ← Matrix.mul_apply, e]
  obtain ⟨b, hb⟩ := (h.sum_mem_iff ((g' * g⁻¹) i)).1 (e1 ▸ h') i
  have e2 := lowerTri_mul_diag _ _ (lowerTri_mul _ _ hg' (lowerTri_inv g hg hd)) hg i
  rw [e] at e2
  rw [e2, map_mul, ← hb]
  exact mul_le_of_le_one_left' (hv.map_le_one b)

theorem IsLatBasis.mem {La : Submodule O U} {w : Fin n → U} (h : IsLatBasis C La w) (i : Fin n) : w i ∈ La :=
  (h.2.le (Submodule.subset_span ⟨i, rfl⟩)).1

end Lat

theorem IsHTFrame.exists_frBor {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [Algebra c.F C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] [StarRing (𝓞 E)] [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] C] [Algebra ℤ_[p] O]
    [IsScalarTower ℤ_[p] O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : CDVR} {io : c.F →+* T.Fr} {y₀ : IntFr Xo c T io} {k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C}
    {y y' : FrPt Xo c C} (h : IsHTFrame p v O y₀ k y) (h' : IsHTFrame p v O y₀ k y') :
    ∃ t : Ix Dw → Cˣ, FrBor t y y' ∧ ∀ i, v (t i) = 1 := by
  letI := io.toAlgebra
  obtain ⟨-, kO, P, ψ, z, hP, hz, g, a, x, hc, hg, ha, hx, hb⟩ := h
  obtain ⟨-, kO', P', ψ', z', hP', hz', g', a', x', hc', hg', ha', hx', hb'⟩ := h'
  obtain rfl : z = z' := FlagTan.frMap_unique hz hz'
  have key := fun τ => sum_bLie_mem_htLat_iff_of_pointOver E H Dw l Xo c p C v O T _ _ kO kO' P P' ψ ψ' hP hP' τ _
    (z.u τ) (x τ) (x' τ) (hx τ) (hx' τ)
  have hd := fun τ => diag_ne_zero_of_linearIndependent (hg τ) (hb τ).1
  have hd' := fun τ => diag_ne_zero_of_linearIndependent (hg' τ) (hb' τ).1
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have ha0' : a' ≠ 0 := by rintro rfl; simp at ha'
  let t : Ix Dw → Cˣ := fun i => Option.rec (Units.mk0 a ha0) (fun s => Units.mk0 _ (hd s.1 s.2)) i
  let t' : Ix Dw → Cˣ := fun i => Option.rec (Units.mk0 a' ha0') (fun s => Units.mk0 _ (hd' s.1 s.2)) i
  have b1 : FrBor t z y := (frBor_iff_frChg z y t).2 ⟨g, hg, fun _ _ => rfl, hc⟩
  have b2 : FrBor t' z y' := (frBor_iff_frChg z y' t').2 ⟨g', hg', fun _ _ => rfl, hc'⟩
  have hv : ∀ i : Ix Dw, v (t' i).val = v (t i).val := by
    rintro (_ | ⟨τ, i⟩)
    · exact ha'.trans ha.symm
    · exact le_antisymm
        (IsLatBasis.diag_le P.integers (hg τ) (hg' τ) (hb τ) i ((key τ _).2 ((hb' τ).mem i)))
        (IsLatBasis.diag_le P.integers (hg' τ) (hg τ) (hb' τ) i ((key τ _).1 ((hb τ).mem i)))
  refine ⟨t' * t⁻¹, (frBor_calculus E H Dw l Xo c C y z y').2.2.1 _ _
    ((frBor_calculus E H Dw l Xo c C z y y).2.2.2 t b1) b2, fun i => ?_⟩
  rw [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hv]
  exact mul_inv_cancel₀ ((Valuation.ne_zero_iff v).2 (t i).ne_zero)

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

theorem isHTFrameCp_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y y' : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y → IsHTFrameCp p y₀ k y' → (∃ t : Ix Dw → ℂ_[p]ˣ, FrBor t y y' ∧ ∀ i, ‖(t i : ℂ_[p])‖ = 1) ∧ ∀ (e : Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ‖evR Xo c f y‖ = ‖evR Xo c f y'‖ := by
  intro E _ _ _ H Dw l Xo c p _ _ T io y₀ k y y' h h'
  letI := H.starRing
  obtain ⟨t, ht, hv⟩ := IsHTFrame.exists_frBor h h'
  have hn : ∀ i, ‖(t i : ℂ_[p])‖ = 1 := fun i => by
    rw [PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict, hv i, NNReal.coe_one]
  refine ⟨⟨t, ht, hn⟩, fun e f hf => ?_⟩
  rw [FlagTan.evR_frBor hf ht, norm_mul, Units.coe_prod, norm_prod]
  simp [norm_zpow, hn]

end GlobalTheory.CompHt
