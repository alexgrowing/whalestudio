import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (n : ℕ) (D₀ : DegPre W), D₀.PsiEven → D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → ∀ (ib : D₀.X ≃+ (Fin T.r → ℤ)) (β : D₀.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n D₀ ib β ββ w → ∀ (V : Type) [CommRing V] [IsDomain V] (iw : W →+* V), Function.Injective iw → ∀ (Q : DegPre V) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw D₀ (rescale Q g)) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (e : Q.X ≃+ (Fin T.r → ℤ)), (∀ y : Q.X, e y = ib (hD.xe y)) → (∀ a a' : Q.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing V)ˣ) : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e a'))) → ∃ (β' : Q.P.A.left ⟶ T.B.left) (ββ' : (G2 Q.P.A).left ⟶ (G2 T.B).left) (w' : LB.Iso (abelian₂ Q.P.A Q.P.L) ((abelian₂ T.B T.M.L).pull ββ')), From T iw s ε n Q e β' ββ' w' := by
  first | exact @GlobalTheory.TInj.from_rescale_pull | exact GlobalTheory.TInj.from_rescale_pull | (intros; apply GlobalTheory.TInj.from_rescale_pull <;> assumption)
