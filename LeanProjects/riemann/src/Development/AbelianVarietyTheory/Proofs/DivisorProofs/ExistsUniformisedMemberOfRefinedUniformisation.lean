import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValuePointLiesOverModuliPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPresentationEndomorphismsPullbackStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationEighthPowerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEighthPowerDataEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTrivialisationEqUnitMulMonomialStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.Poinc.Sep.MkMember

theorem exists_uMem : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → Q.IsMonomialTau t δ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ 𝔪 : UMem X₁ z₁ act V₁ ev Q.X (fun k => ρ (t k)) δ, SharpRef W Q ρ 𝔪.D.toPre 𝔪.e₈ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact V _ _ _ Q m t δ ht hsym hnn hmono V₁ _ _ _ ρ hCN hρi hρf D₀ e₀ href G₀ _ _ A₀ U₀ y α α₂ hS hpb hsq hlb ev hloc hreg hcomm
  obtain ⟨yK, hyK, hy⟩ := GlobalTheory.T.thetaValuePoint_lies_over_moduliPoint g n F Z i W X₁ z₁ V₁ ev y hreg hcomm
  subst hy
  obtain ⟨A, φ, -, cart, hlbA⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds yK X₁.ρ.P
  obtain ⟨wl, hwl⟩ := LBIso.symm hlbA
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hactc⟩ := hact
  obtain ⟨c', hc', pr', hpr', huniv', hbun', hlift⟩ := GlobalTheory.T.eighthPowerPresentation_endomorphisms_pullback g n (cycAway n) (zetaAway n) F W _ _ X₁.ρ.P A X₁.u (spMap yK) φ c hc pr hpr huniv hbun cart (LBIso.symm hlbA)
  have hsharp : SharpOver F W A (spMap yK ≫ X₁.u) := ⟨c', hc', pr', hpr', huniv', hbun'⟩
  obtain ⟨D, ⟨U⟩⟩ := GlobalTheory.T.uniformization_eighth_power_exists g n (cycAway n) (zetaAway n) F W hW V₁ hCN D₀ G₀ A₀ U₀ _ α α₂ hS hpb hsq hlb A hsharp
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨e, hsr, heq⟩ := GlobalTheory.T.uniformisation_eighthPower_data_equivariant g n (cycAway n) (zetaAway n) F W hW V Q V₁ ρ hCN hρi hρf D₀ e₀ href G₀ A₀ U₀ _ α α₂ hS hpb hsq hlb A c' hc' pr' hpr' huniv' hbun' (powObj G₀ 8) hS8 D U
  refine ⟨{ cn := hCN, loc := hloc, reg := hreg, yK := yK, yK_eq := hyK, D := D, e₈ := e, G := powObj G₀ 8, semi := hS8, A := A, U := U, φ := φ, cart := cart, wl := wl, wl_gen := hwl, equiv := ?_, psi := ?_ }, hsr⟩
  · intro a a' h
    obtain ⟨aA, h1, h2⟩ := hlift (act a) (fun u v => a u v) (hactc a)
    obtain ⟨E, hE, hE2⟩ := heq a a' h aA h1
    exact ⟨E, hE ▸ h2, hE2⟩
  · exact GlobalTheory.T.eighthPower_trivialisation_eq_unit_mul_monomial W X₁.posW V V₁ Q ρ hρi m t δ hsym hnn ht hmono D.toPre e hsr

end GlobalTheory.Poinc.Sep.MkMember
