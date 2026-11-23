import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupEqEighthPowerLatticeOverTrait
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterGroup_eq_eighthPower_lattice_over_trait : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ M.Z) (D : DegPre R) (m : Fin 8 → Fin 8 → (D.X →+ D.X)) (T : Trait F) (ψ : R →+* T.V), ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∀ (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Sp (FractionRing T.V))) (U' : Unif (maximalIdeal T.V) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ι : D.X ≃+ D'.toPre.X), IsSemiAbelian G' → IsGrpPullback G' FinalForm.G (spMap ψ ≫ ξ) gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → CoordMap D D'.toPre ψ ι.toAddMonoidHom → (∀ a b, ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ (f a b).left ∧ ∀ m', EndChar U' f' m' → ∀ y, ι (m a b y) = m' (ι y)) → ∃ ρT : D.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  first | exact @GlobalTheory.Poinc.Eq8.PeriodsEighth.main | exact GlobalTheory.Poinc.Eq8.PeriodsEighth.main | (intros; apply GlobalTheory.Poinc.Eq8.PeriodsEighth.main <;> assumption)
