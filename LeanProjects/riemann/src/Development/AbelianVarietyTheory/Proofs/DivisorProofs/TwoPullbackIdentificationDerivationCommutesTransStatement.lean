import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPullbackIdentificationDerivationCommutesTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pullback_identification_derivation_commutes_translations : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsGrpPullback A₀ Q.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → Commutes Q m₀ ed := by
  first | exact @GlobalTheory.HeatConn.Comm.commutes | exact GlobalTheory.HeatConn.Comm.commutes | (intros; apply GlobalTheory.HeatConn.Comm.commutes <;> assumption)
