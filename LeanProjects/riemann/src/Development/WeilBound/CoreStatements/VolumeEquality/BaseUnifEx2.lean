import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {sm : CMType H → CMType H ⊕ CMType H} {j j' n : ℕ}

def BaseUnif.Locc (B : BaseUnif Y sm j j' n) : Prop :=
  ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y.X)), IsOpen T → IsPreconnected T → IsHolTo T y →
    (∀ b ∈ T, centre (y b) ∈ abLocus Y.t.G) → ∀ b ∈ T, ∀ b' ∈ T, ∀ k k', ∀ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q,
      ∀ t' ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k').q, y b = B.pt k t → y b' = B.pt k' t' → k = k'

end

def BaseUnifEx2 : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ), 1 ≤ D.p + D.q →
    (sm = Sum.inr ∧ j = D.p ∧ j' = D.q ∨ sm = Sum.inl ∧ j = D.q ∧ j' = D.p) → n = Fintype.card (CMType H) * j * j' →
    ∃ B : BaseUnif Y sm j j' n, B.Locc

def OnePiece : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ)
    (B : BaseUnif Y sm j j' n) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Sp Ω₀ ⟶ Y.X) (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] (ξ₁ : Sp Ω₁ ⟶ Y.X)
    (g : Ω₁ →+* Ω₂) (cst : c.F →+* Ω₂) (U : Y.X.Opens), B.Locc → IsCptGen ξ₀ → genPt ξ₁ = genPt ξ₀ →
    spMap g ≫ ξ₁ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → (∀ a : Ω₁, IsAlgebraic ℤ a → g a ∈ cst.range) →
    genPt ξ₀ ∈ U → (∀ p : Sp ℂ ⟶ Y.X, ⊤ ≤ p ⁻¹ᵁ U → genPt ξ₀ ⤳ centre p) →
    ∀ κ : c.F →+* ℂ, ∃! k, B.κ k = κ ∧ ∃ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U

def BallVolEq : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (n : ℕ) (B : BaseUnif Y Sum.inr D.p D.q n)
    (FF : Fin B.np → Set (Fin n → ℂ)), 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → (∀ k, (B.F k).IsFundSet (B.Γ k) (FF k)) →
    ∀ k k', ∫ t in FF k, ballDens (B.F k).q t = ∫ t in FF k', ballDens (B.F k').q t

def DegPush : Prop :=
  ∃ c₀ : ℕ → ℕ → ℕ → ℝ, (∀ f p q, c₀ f p q ≠ 0) ∧ (PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
      (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
      [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem),
      Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → ∀ (a : T.Comp) (K : Type) [Fintype K]
      (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)]
      [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (Or : CptOrigin Y T.bad Dc Hd),
      Or.bg = Sum.inl → Or.sm = Sum.inr → Or.𝔐.OmVB → Or.Good → Dc.S = ∅ → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf →
      degMu Hd = c₀ (Fintype.card (CMType H)) D.p D.q * Or.deg * Module.finrank ℚ c.F * T.vol a)

end SheetDecomposition
