import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticMapTangentDifferential
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNhdsNEInChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingStalk
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve

section

open Filter Polynomial
open GlobalTheory.WeierstrassCurve (affineX affineY)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

open GroundTheory.Global.Elliptic

variable (Λ : PeriodPair) {Ω : ℂ} (W : WeierstrassCurve ℂ)

def IsEvalAt (Ω z : ℂ) (e : W.toAffine.CoordinateRing →+* ℂ) : Prop :=
  (∀ r, e (algebraMap ℂ _ r) = r) ∧ e (affineX W) = Λ.weierstrassP z / Ω ^ 2 ∧
    e (affineY W) = Λ.derivWeierstrassP z / (2 * Ω ^ 3)

theorem exists_quotient (hΩ : Ω ≠ 0) {f : ℂ → ℂ} (hf : IsEllipticFunction Λ f) :
    ∃ a d : W.toAffine.CoordinateRing, ∀ᶠ z in codiscrete ℂ, ∀ e, IsEvalAt Λ W Ω z e →
      e d ≠ 0 ∧ e a = e d * f z := by
  obtain ⟨P, Q, R, S, hQ, hS, h⟩ := exists_rational_weierstrassP hf
  let t : ℂ[X] → W.toAffine.CoordinateRing := fun p =>
    p.eval₂ (algebraMap ℂ _) (algebraMap ℂ _ (Ω ^ 2) * affineX W)
  refine ⟨t P * t S + algebraMap ℂ _ (2 * Ω ^ 3) * affineY W * t R * t Q, t Q * t S, ?_⟩
  filter_upwards [h, eventually_codiscrete_eval_weierstrassP_ne_zero (L := Λ) hQ,
    eventually_codiscrete_eval_weierstrassP_ne_zero (L := Λ) hS] with z hz h1 h2 e ⟨e0, ex, ey⟩
  have ht : ∀ p, e (t p) = p.eval (Λ.weierstrassP z) := fun p => by
    have h3 : e.comp (algebraMap ℂ _) = RingHom.id ℂ := RingHom.ext e0
    rw [hom_eval₂, h3, map_mul, e0, ex, mul_div_cancel₀ _ (pow_ne_zero 2 hΩ), eval₂_id]
  simp only [map_add, map_mul, ht, e0, ey, hz]
  refine ⟨mul_ne_zero h1 h2, ?_⟩
  field_simp

theorem exists_vector (hΩ : Ω ≠ 0) {ι : Type} [Fintype ι] {f : ι → ℂ → ℂ} (hf : ∀ j, IsEllipticFunction Λ (f j)) :
    ∃ v : ι → W.toAffine.CoordinateRing, ∀ᶠ z in codiscrete ℂ, ∀ e, IsEvalAt Λ W Ω z e →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ j, e (v j) = c * f j z := by
  classical
  choose a d h using fun j => exists_quotient Λ W hΩ (hf j)
  refine ⟨fun j => a j * ∏ i ∈ Finset.univ.erase j, d i, ?_⟩
  filter_upwards [eventually_all.2 h] with z hz e he
  refine ⟨∏ i, e (d i), Finset.prod_ne_zero_iff.2 fun i _ => (hz i e he).1, fun j => ?_⟩
  rw [map_mul, map_prod, (hz j e he).2, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  ring

end GlobalTheory.ProjHol

end

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

namespace GlobalTheory.CMTorsion

open Filter Topology GlobalTheory.ProjHol

theorem curve_Δ_ne_zero (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) : (curve Λ Ω).Δ ≠ 0 := by
  have h := GlobalTheory.latticeCurve_Δ_ne_zero Λ
  rw [GlobalTheory.latticeCurve_Δ] at h
  have e : (curve Λ Ω).Δ = (Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2) / Ω ^ 12 := by
    simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    field_simp
    ring
  rw [e]
  exact div_ne_zero h (pow_ne_zero _ hΩ)

theorem eventually_nhdsNE_of_codiscrete {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, p w := by
  have := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h z (Set.mem_univ z)
  simpa [Filter.Eventually] using this

theorem exists_hom_of_periodic_holomorphic : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (N : ℕ) (φ : ℂ → (Sp ℂ ⟶ PSpace ℂ N)), (∀ z, φ z ≫ PSpace.str ℂ N = 𝟙 _) → (∀ z, ∀ l ∈ Λ.lattice, φ (z + l) = φ z) → (∀ (U : (PSpace ℂ N).Opens) (s : Γ(PSpace ℂ N, U)), IsOpen {z | ⊤ ≤ (φ z) ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (φ z) U s) {z | ⊤ ≤ (φ z) ⁻¹ᵁ U}) → ∃ ψ : scheme (curve Λ Ω) ⟶ PSpace ℂ N, ψ ≫ PSpace.str ℂ N = toSpec (curve Λ Ω) ∧ ∀ z, pt Λ Ω z ≫ ψ = φ z := by
  intro Λ Ω hΩ N φ hstr hper hhol
  have hH : IsHolTo (Set.univ : Set ℂ) φ := fun U s => by
    simpa only [Set.mem_univ, true_and] using hhol U s
  have : (curve Λ Ω).IsElliptic := ⟨IsUnit.mk0 _ (curve_Δ_ne_zero Λ Ω hΩ)⟩
  obtain ⟨k, hk⟩ := exists_inChart (φ 0)
  obtain ⟨v, hv⟩ := exists_vector Λ (curve Λ Ω) hΩ (f := fun j w => rv (φ w) k j)
    fun j => ⟨meromorphic_rv hH hk j, fun z l hl => by simp only [hper z l hl]⟩
  have hev : ∀ z₀, ∀ᶠ z in 𝓝[≠] z₀, InChart (φ z) k ∧
      ∃ e : (curve Λ Ω).toAffine.CoordinateRing →+* ℂ, (∀ r, e (algebraMap ℂ _ r) = r) ∧
        pt Λ Ω z = spMap e ≫ GlobalTheory.WeierstrassCurve.chartZ (curve Λ Ω) ∧
        ∃ c : ℂ, c ≠ 0 ∧ ∀ j, e (v j) = c * rv (φ z) k j := fun z₀ => by
    have hl : ∀ᶠ z in 𝓝[≠] z₀, z ∉ Λ.lattice := by
      filter_upwards [nhdsWithin_le_nhds (Λ.compl_lattice_sdiff_singleton_mem_nhds z₀), self_mem_nhdsWithin]
        with z h1 h2 h3 using h1 ⟨h3, h2⟩
    filter_upwards [eventually_nhdsNE_inChart hH hk z₀, eventually_nhdsNE_of_codiscrete hv z₀, hl] with z h1 h2 h3
    have h4 := GlobalTheory.WeierstrassCurve.affineEval_algebraMap (curve Λ Ω) (RingHom.id ℂ) _ _
      (HolPt.affine_equation Λ Ω hΩ z h3)
    exact ⟨h1, _, h4, HolPt.pt_eq_chartZ Λ Ω hΩ z h3, h2 _ ⟨h4,
      GlobalTheory.WeierstrassCurve.affineEval_affineX .., GlobalTheory.WeierstrassCurve.affineEval_affineY ..⟩⟩
  have hvk : v k ≠ 0 := by
    obtain ⟨z, h1, e, -, -, c, hc, h⟩ := (hev 0).exists
    intro h0
    have := h k
    rw [h0, map_zero, rv_self h1, _root_.mul_one] at this
    exact hc this.symm
  obtain ⟨ψ, hψ, hpt⟩ := exists_extend (curve Λ Ω) v k hvk
  have hs : ∀ z, (pt Λ Ω z ≫ ψ) ≫ PSpace.str ℂ N = φ z ≫ PSpace.str ℂ N := fun z => by
    rw [hstr, Category.assoc, hψ, pt, GlobalTheory.WeierstrassCurve.ptHom_toSpec]
    exact Spec.map_id _
  refine ⟨ψ, hψ, fun z₀ => eq_of_eventuallyEq
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (HolPt.isHolTo_pt Λ Ω hΩ) ψ) hH (hs z₀) ?_⟩
  filter_upwards [hev z₀] with z ⟨h1, e, _, h2, c, hc, h⟩
  have h3 : e (v k) = c := by rw [h, rv_self h1, _root_.mul_one]
  have h4 : (e ∘ v) k ≠ 0 := h3.trans_ne hc
  have h5 : Ideal.span (Set.range (e ∘ v)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k, rfl⟩) (IsUnit.mk0 _ h4)
  have h6 : pt Λ Ω z ≫ ψ = GlobalTheory.ProjSpace.pt (e.comp (algebraMap ℂ _)) (e ∘ v) h5 := by
    rw [h2, Category.assoc, hpt e h4 h5]
  refine eq_of_rv_eq (hs z) (h6 ▸ inChart_pt _ _ h5 h4) h1 fun j => ?_
  rw [h6, rv_pt _ _ h5 h4, Function.comp_apply, Function.comp_apply, h3, h, mul_div_cancel_left₀ _ hc]

end GlobalTheory.CMTorsion
