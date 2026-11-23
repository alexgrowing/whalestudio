import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeySectionEqConstMulThetaFunctionFibreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidificationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesianStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

open GlobalTheory GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare

theorem exists_thetaChar_mulVec_ne {g : ℕ} (τ h : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hh : IsUnit h.det) : ∃ z, thetaChar τ c₁ c₂ (h.mulVec z) ≠ 0 := by
  have re : ∀ c : Fin g → ℂ, (∀ k, c k = 0 ∨ c k = 1 / 2) → (fun i => (((c i).re : ℝ) : ℂ)) = c := by
    intro c hc
    funext i
    rcases hc i with e | e <;> rw [e] <;> norm_num
  have hne := GlobalTheory.CanTh.thetaChar_ne_zero hs hp (fun i => (c₁ i).re) (fun i => (c₂ i).re)
  rw [re c₁ h₁, re c₂ h₂] at hne
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  refine ⟨h⁻¹.mulVec z₀, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec]
  exact hz₀

theorem exists_unif_of_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_ : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hσ hty hP hover hgen hM
  have hh : IsUnit Θ.h.det := by
    refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun i k => Ha.Pw 0 (Θ.bas (Pi.single (.inl k) 1)) i) ?_
    ext i k
    have e := congrFun (Θ.per 0 k).1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using e
  refine ⟨Ha.T, fun w hw yF hy₁ hy₂ hz x φ hx => ?_⟩
  have hPer := Ha.period w hw
  obtain ⟨fr, hf₁, hf₂, hf₃, -, s, hs⟩ := Θ.frame w hw
  obtain ⟨-, wx, -, hgp, hwx, -, -, -⟩ := hx
  obtain ⟨φ', hφ₁, hφ₂, hgp', hiso⟩ := GlobalTheory.T.genericFibre_group_factors_universal_cartesian E H Dw l Xo c _ _ Y yF x φ hgp ⟨wx, hwx⟩
  rw [hy₁] at hgp'
  have hL := Xo.univ.t.PP.isLB
  have hM' := pull_isLB hL (φ' ≫ Y.m0.toSABMap.φ)
  let u₁ := fibreUnif hgp' (Fu.ex Ha.i (Ha.Pw w)) (Ha.Pw w).range fr (Fu.ex_add _ _ hPer) (Fu.ex_onto _ _ hPer)
    (Fu.ex_ker _ _ hPer) hPer.2.2.1 hPer.2.2.2.1 (isHolTo_exp Fu Ha.i hPer) hf₁ hf₂ hf₃
  obtain ⟨wI, hwI⟩ := LBIso.symm hiso
  let u₂ := carry u₁ hM' x.P.isLB hwI
  have hex₁ : ∀ z, (u₂.ex z).left ≫ φ' ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left := fun z =>
    liftPt_comp hgp' _
  obtain hθ : ∃ z, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) ≠ 0 :=
    exists_thetaChar_mulVec_ne _ _ _ _ (Θ.pos w hw).1 (Θ.pos w hw).2 Θ.half₁ Θ.half₂ hh

  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.keySection_eq_const_mul_thetaFunction_fibre x _ Xo.univ.t.G Xo.univ.t.PP.L (Fu.u Ha.i (Ha.Pw w)) (φ' ≫ Y.m0.toSABMap.φ) g u₂ wI
    (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr s hL hgp'.1 hwI hθ
    (fun j z hj => hf₂ j z (by rwa [hex₁] at hj))
    (fun k j z hkj => by
      obtain ⟨hk, hj⟩ := (top_le_preimage_inf _ _ _).1 hkj
      exact carry_fr u₁ hM' x.P.isLB hwI k j z hk hj)
    (fun j z p hp₁ hp₂ hj => hs j z p (hp₁.trans (hex₁ z)) hp₂ (by rwa [hex₁] at hj))
  obtain ⟨u₃, lam, hlam, hex, hΛ, hR, hfr⟩ := GlobalTheory.T.exists_rescale_uniformisation_rigidification x.P.A x.P.L g u₂ x.rig x.P.isLB x.rig_gen
  have hFn : u₃.IsFn x.th fun z => c₁ / lam * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) := by
    intro i z hi
    rw [hex] at hi ⊢
    rw [hc₁ i z hi, hfr]
    field_simp
  have hdim : g = x.P.g := by
    obtain ⟨u₀, -, -, -, -, -, hv, hw', -⟩ := thetaUnifAV_all x.P x.rig x.rig_gen
    obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g g u₀ hv hw' u₃.ex u₃.ex_add
      (fun U f => by simpa only [Set.mem_univ, true_and] using u₃.hol U f)
    exact AHWeil.dim_eq u₃ u₀ F hF
  refine ⟨hdim.symm, u₃, c₁ / lam, hR, fun z => ⟨(u₃.ex z).left ≫ φ', ?_, ?_, ?_⟩, hΛ, hFn⟩
  · rw [Category.assoc, hex]
    exact hex₁ z
  · rw [Category.assoc, ← Category.assoc φ', hφ₂, Category.assoc, ← Category.assoc (u₃.ex z).left, Over.w (u₃.ex z),
      hy₂]
    exact Category.id_comp _
  · rw [Category.assoc, hφ₁]

end GlobalTheory.ArcNormal
