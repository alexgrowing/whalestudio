import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedGenericExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedPointLevelExtendsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLatticeEvaluationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_weil_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ a : Dw.La,
    ∃ κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ, GlobalTheory.HTMap.Mult Y.t ξ (p ^ n) κ ∧
      ∀ (P' : GlobalTheory.HTMap.FP Y.t ξ (p ^ n)) (b : P'.Bˣ), P'.Gl κ b → ∀ (x0 : R →+* 𝓞_ℂ_[p])
        (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
        PtOn Y (spMap x0 ≫ ξ) yy P π ψ → ∀ tt : P.T, (tt.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA a).left →
        ∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ Y.t.G.left), P'.At x0 w β →
        ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w →
          algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hstar hpW hA R _ _ _ ξ y hy a
  obtain ⟨κ, hκM, hκW⟩ := GlobalTheory.T.integrally_closed_generic_extension E H Dw l' Xo' c' W Y p n hA R ξ y hy a
  refine ⟨κ, hκM, ?_⟩
  intro P' b hb x0 yy P π ψ hPt tt hlev β w hAt z hz
  have hAt' := hAt.map (algebraMap 𝓞_ℂ_[p] ℂ_[p])
  obtain ⟨φ, hφ⟩ := GlobalTheory.HTMap.FP.ex_lift (P := P') hAt'.unit
  rw [← hφ] at hAt'
  obtain ⟨σ, hσ⟩ := hAt'.sect
  let wf : Over.mk (spMap (algebraMap R (Localization.Away P'.f)) ≫ ξ) ⟶ Y.t.G :=
    GlobalTheory.HTMap.mkPt (spMap σ.toRingHom ≫ P'.u.left) (P'.at_sect σ).over
  have hwf : wf ^ (p ^ n) = 1 := (P'.at_sect σ).tors (w := wf)
  have hgl := hb.1 _ _ (P'.at_sectK σ)
  have hsb : σ b = algebraMap R (Localization.Away P'.f) (κ (spMap (P'.toK.comp σ.toRingHom) ≫ P'.u.left)) := by
    apply P'.toK_inj
    rw [← RingHom.comp_apply P'.toK (algebraMap R _), P'.toK_comp]
    exact hgl
  let eyy : Over.mk yy ⟶ Y.oF.t.G := Over.homMk (yy ≫ (Y.oF.etaA a).left) (by
    rw [Category.assoc, Over.w (Y.oF.etaA a)]; exact Category.comp_id _)
  let σyy : Over.mk yy ⟶ Y.oF.t.G := Over.homMk (z.left ≫ ψ) (by
    rw [Category.assoc, hPt.2.2.2.1.1.w, ← Category.assoc, Over.w z]; simp)
  have hσyy : σyy.left ≫ Y.m.φ = spMap φ ≫ wf.left := by
    show (z.left ≫ ψ) ≫ Y.m.φ = spMap φ ≫ spMap σ.toRingHom ≫ P'.u.left
    rw [Category.assoc, hPt.2.2.2.2.1, hz, ← hAt'.2, hσ]
    exact (GlobalTheory.HTMap.spc_assoc _ _ _).symm
  obtain ⟨hσt, hW⟩ := GlobalTheory.T.integrally_closed_point_level_extends E H Dw l' Xo' c' W Y p n hpW hA R ξ y hy a κ hκW P'.f wf hwf P'.toK P'.toK_comp x0 φ hφ
    yy hPt.1 eyy σyy rfl hσyy
  have hc := GlobalTheory.T.p_adic_point_lattice_evaluation E H Dw l' Xo' c' W Y p n _ yy P π ψ hPt a tt hlev z eyy σyy rfl rfl hσt _ hW
  rw [← hc]
  have e1 : spMap P'.toK ≫ wf.left = spMap (P'.toK.comp σ.toRingHom) ≫ P'.u.left := GlobalTheory.HTMap.spc_assoc _ _ _
  rw [e1]
  show algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0) _
  rw [← hφ, RingHom.comp_apply, ← hsb]
  exact RingHom.congr_fun hσ _

end GlobalTheory.FlatModel
