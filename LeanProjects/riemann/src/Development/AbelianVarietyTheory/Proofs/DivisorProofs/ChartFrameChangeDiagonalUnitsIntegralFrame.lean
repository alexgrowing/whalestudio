import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelTangentOfPullbackTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTangentLiftOfModelTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackGroupPointToModelGroupLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigenvectorIntegralOfTangentPullbackMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorEqIntegralFrameTangentOnModelStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntFrameDiag

theorem integralFrame_transport : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w) → ∃ ub' : Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (∀ i, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (ub' i)).left = (ub i).left ≫ ψ.φ) ∧ ∀ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → ∃ a : Fin (Dw.mult τ) → T.V, ∑ i, a i • ub' i = v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro x x' e hinj G ψ τ ub hT hS
  choose ub' hub' using fun i => GlobalTheory.T.exists_modelTangent_of_pullback_tangent x G ψ (ub i) (hT i)
  refine ⟨ub', hub', fun v hv => ?_⟩
  obtain ⟨w, hw, hvw⟩ := GlobalTheory.T.exists_pullback_tangent_lift_of_modelTangent x G ψ v
  obtain ⟨a, ha, -⟩ := hS w hw (GlobalTheory.T.isEigenvector_integral_of_tangentPullback_mem T io x x' e hinj G ψ τ w v hvw hv)
  exact ⟨a, GlobalTheory.T.pullbackGroupPointToModelGroup_linearCombination x G ψ ub ub' a w v hub' hvw ha⟩

theorem diag_unit_of_intFr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (z : Sp T.V ⟶ X.YY), (X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ z) → ∀ (k : X.F.J), ⊤ ≤ z ⁻¹ᵁ X.F.U k → ∀ (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr k (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t (some ⟨σ, i⟩) : T.Fr) := by
  intro E _ _ _ H Dw l Xo c Y X T io
  letI := io.toAlgebra
  intro y' z hz0 k hzk hz Q t hQ ht σ i
  have hφ : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hl : X.F.Lies (spMap (algebraMap T.V T.Fr) ≫ z) y'.1 := by
    rw [← show X.ptY y'.1 = spMap (algebraMap T.V T.Fr) ≫ z from hz0]
    exact X.lies_ptY y'.1
  have e : spMap (algebraMap T.V T.Fr) ≫ z ≫ X.π = GlobalTheory.FlagMod.frX y'.1 ≫ Y.j := by
    rw [← Category.assoc]; exact hl.1
  obtain ⟨-, G, t', m1, m2, ⟨ub, hT, -, hS, hU⟩, -⟩ := y'.2
  obtain ⟨ψ, ρ, h1, h2, h3⟩ := GlobalTheory.T.exists_semiAbelianMap_model_of_integralFramedPoint Y T io y'.1 (z ≫ X.π) e G t' m1 m2
  have hx : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hzk rfl
  have hx' : ⊤ ≤ (GlobalTheory.FlagMod.frX y'.1 ≫ Y.j) ⁻¹ᵁ (X.F.M k).toMChart.U :=
    e ▸ GlobalTheory.FlagMod.le_preimage_comp _ hx
  have hinj : Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) := by
    intro u u' huu
    obtain ⟨cv, rfl⟩ := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx).surjective u
    obtain ⟨cv', rfl⟩ := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx).surjective u'
    rw [GlobalTheory.FlagMod.tanPull_vec _ _ e hx hx', GlobalTheory.FlagMod.tanPull_vec _ _ e hx hx'] at huu
    have := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx').injective huu
    congr 1
    funext j
    exact hφ (congrFun this j)
  obtain ⟨ub', hl', hsp⟩ := integralFrame_transport T io (z ≫ X.π) _ e hinj G ψ σ (ub σ) (hT σ) (hS σ)
  have hub : ∀ j, GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e (ub' j) = GlobalTheory.FlagMod.frVec Y y'.1 rfl σ j := by
    intro j
    obtain ⟨u', hu1, hu2⟩ := hU σ j
    exact GlobalTheory.T.frameVector_eq_integralFrameTangent_on_model T io y'.1 (z ≫ X.π) e G t' m1 m2 ψ ρ h1 h2 h3 σ j (ub σ j) u' hu1 hu2 (ub' j) (hl' j)
  have key : ∀ (w : Sp T.Fr ⟶ X.YY) (_ : w = spMap (algebraMap T.V T.Fr) ≫ z) (hzw : ⊤ ≤ w ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k w hzw Q → X.F.ChartFr k (spMap (algebraMap T.V T.Fr) ≫ z) (GlobalTheory.FlagMod.le_preimage_comp _ hzk) Q := by
    rintro _ rfl _ h
    exact h
  have hQ' := key _ ((X.pt_inc _).trans hz0) hz hQ
  exact (X.top.diag_unit (algebraMap T.V T.Fr) hφ z hzk hl e σ ub' hub hsp hQ' ht).2 i

end GlobalTheory.IntFrameDiag
