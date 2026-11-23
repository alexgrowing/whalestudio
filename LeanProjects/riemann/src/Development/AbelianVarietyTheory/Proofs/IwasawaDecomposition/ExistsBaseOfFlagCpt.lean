import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlagStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentRefinesLieFramesGradedStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.LieBase.exists_base_of_flagCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∃ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (E' : Fr (ratOf (Φ.C k).Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] (Φ.C k).Y.Fn), (j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str) ∧ IsLieBase e (Φ.C k) X j f f₀ Eb A₀ ∧ Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => (Φ.C k).gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k
  obtain ⟨X, j, hoi, hj, hr⟩ := GlobalTheory.T.exists_variety_connectedComponent_genericFibre E H Dw l Xo c O β T.Z F e T.smooth (Φ.C k).Y (Φ.C k).π (Φ.C k).π_str
  let f : (Φ.C k).Y.X ⟶ X.X := IsOpenImmersion.lift j (Φ.C k).π hr
  have hf : f ≫ j = (Φ.C k).π := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨f₀, Eb, A₀, hT⟩ := GlobalTheory.ShFam.TieBase.exists_tied E H Dw l Xo c O β T.Z F e X j hj
  have hcar := GlobalTheory.T.flagSpace_component_unique_point_each_flag E H Dw l Xo c O β T.Z F e σ _ U Φ k X j hoi hj f hf
  obtain ⟨E', φ, hR, hG⟩ := GlobalTheory.T.flagSpaceComponent_refines_lie_frames_graded E H Dw l Xo c O β T.Z F e (Φ.C k) X j hoi hj f hf f₀ Eb A₀ hT
    (fun K _ _ χ x hx g => hcar K χ x hx g)
  exact ⟨X, j, f, f₀, Eb, A₀, E', φ, hj, ⟨hoi, hf, hT⟩, hR, hG⟩
