import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.RootFrame

theorem UpperTheory.flag_component_eigen_frame :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (ε : F ≃+* c.F) (C : FlagCpt Z ε) (p : ℕ) [Fact p.Prime] (τ : E →+* ℂ), EigFr Z.t p (C.π ≫ genι Z) (fun y => (fr C y).v τ) (ε.symm.toRingHom.comp (embK c τ)) := by
  intro E _ _ _ H Dw l Xo c Z F _ _ ε C p _ τ v e y
  have hF := isFrame_fr C (below y.1) (psi p e y)
  refine ⟨(isFlagFrame_eig C τ).indep (below y.1) _ (psi p e y), fun i => ⟨(hF.1 τ i).1, fun a => ?_⟩⟩
  have h1 := RingHom.congr_fun (fr_spec C (below y.1)).1.2.1 (embK c τ a)
  have h2 := GlobalTheory.TrueGeo.Res.valAt_const y.2 (ε.symm (embK c τ a))
  have h3 : (Scheme.stalkClosedPointTo y.1).hom ((C.gr_spec (below y.1)).choose (embK c τ a)) =
      algebraMap F (AlgebraicClosure F) (ε.symm (embK c τ a)) :=
    (GlobalTheory.TrueGeo.Res.valAt_algebraMap y.1 _).symm.trans ((congrArg (TrueGeo.valAt y.1) h1.symm).trans h2)
  have h4 : ((psi p e y).comp (C.gr_spec (below y.1)).choose) (embK c τ a) =
      (((ioOf p e).comp (algebraMap F (AlgebraicClosure F))).comp (ε.symm.toRingHom.comp (embK c τ))) a :=
    congrArg (ioOf p e) h3
  rw [← h4]
  exact (hF.1 τ i).2 a
