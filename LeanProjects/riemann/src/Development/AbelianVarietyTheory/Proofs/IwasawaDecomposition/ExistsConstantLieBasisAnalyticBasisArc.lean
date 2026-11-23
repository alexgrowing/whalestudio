import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcLieFrame

theorem exists_const_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ), (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) ∧ IsLieBasis v ∧ (Matrix.of z).det ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha
  have hG := GlobalTheory.SemiRigid.globalFns
  obtain ⟨g', e, v, -, hev, hb, hu, -⟩ := GlobalTheory.ConstLie.exists_const_basis hG E H Dw l Xo c V V.subtype Y ℂ
    (σ.comp V.subtype) a χ W
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.ExpTan.anVec_bijective hG E H Dw l Xo c σ V V.subtype Y a χ W g ty Fu Ha
  choose z hz using fun i => (h1 (e i) (hev i).1).exists
  have hli : LinearIndependent ℂ z := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf
    obtain ⟨ν, hν⟩ := GlobalTheory.ConstLie.exists_gtComb cf e
    obtain ⟨ν₀, hν₀⟩ := GlobalTheory.ConstLie.exists_gtComb (0 : Fin g' → ℂ) e
    have a1 := (h4 g' cf e z ν hz).1 hν
    have a0 := (h4 g' 0 e z ν₀ hz).1 hν₀
    rw [hcf] at a1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at a0
    obtain rfl : ν = ν₀ := (h2 0).unique a1 a0
    have ht := h3 _ _ a1
    have := (hu ν ht).unique hν hν₀
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range z) := by
    intro z₀ _
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨ν, hν, -⟩ := h2 z₀
    obtain ⟨cf, hcf, -⟩ := hu ν (h3 _ _ hν)
    exact ⟨cf, (h1 ν (h3 _ _ hν)).unique ((h4 g' cf e z ν hz).1 hcf) hν⟩
  have hg : g' = g := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    simpa using this.symm
  subst hg
  refine ⟨e, v, z, fun k => ⟨(hev k).2, hz k⟩, hb, ?_⟩
  have hu' : IsUnit (Matrix.of z) := (Matrix.linearIndependent_rows_iff_isUnit).1 (by simpa using hli)
  exact (Matrix.isUnit_iff_isUnit_det _).1 hu' |>.ne_zero

end GlobalTheory.ArcLieFrame
