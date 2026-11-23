import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Mathlib
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

def LevelFree : Prop :=
  HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type)
    [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ), p ∈ S →
    0 < D.p + D.q → HT.HTFree 𝔐 p → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q →
      𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q

def MuHodge : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (bb : ∀ τ, Fin Dc.N → W τ)
    (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (lam : Ω),
    (∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)) →
    Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)) →
    ∀ (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z →
    ∃ (h : genPt Or.𝔐.ξ ⤳ centre z) (b : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li)
      (T : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω)
      (Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ),
      (∀ τ, (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)).IsFrameAt (b τ) ⟨centre z, h⟩ ∧ (∀ k, b τ k = ∑ k', T τ k' k • s τ k') ∧
        Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (b τ) (Γ τ) ∧ (Γ τ).PosDef) ∧
      SecNorm Or.𝔐.ξ Dc.y (muVert Hd B)
        (lam⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p)) z w
        (∏ τ, (T τ).det)⁻¹ (∏ τ, Real.sqrt (Γ τ).det.re)⁻¹

def muExp {Ψ : Type} {N : ℕ} (p : ℕ) (r : Ψ × Fin N) : ℤ := if p ≤ (r.2 : ℕ) then 1 else 0

def Common : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (oR : RootOrigin Y S RM Fx)
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ),
    S = S₀ ∪ Dc.SB B → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → oR.𝔐.OmVB → (∀ p ∈ S, oR.𝔐.R p = 4) →
    1 ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt Fx.ξf →
    ∃ (K₃ : Type) (_ : Fintype K₃) (ρ : K₃ → Type) (_ : ∀ k, Fintype (ρ k)) (κ₁ : RM.K → K₃)
      (v₁ : (Σ k, RM.ι k) → Σ k, ρ k) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ρ k) (Ω₃ : Type) (_ : Field Ω₃) (_ : CharZero Ω₃)
      (y : (Σ k, ρ k) → Ω₃) (β : MRing ρ) (d : K₃ → ℕ),
      IsBlockMap κ₁ v₁ ∧ IsBlockMap κ v ∧ mCoordIdeal (y ∘ v₁) = RM.P ∧ mCoordIdeal (y ∘ v) = mCoordIdeal Dc.y ∧
      IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog β d ∧ β ∉ mCoordIdeal y ∧
      IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0 ∧
      (∀ z ∈ mcPts (mCoordIdeal y), evC z β ≠ 0 → (fun p => z (v p)) ∉ Dc.Bd) ∧
      ∀ L L' : HermLine ρ, IsPullHerm κ₁ v₁ (Top.combLine oR.sing (muExp D.p)) L → IsPullHerm κ v (muVert Hd B) L' →
        IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z β ≠ 0} L L'

section Tame

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P B : Ideal (MRing J)} {e : ℕ}

def Tame (R : AnLogRes P B e) (Θ L : LocPot R.X) (s : R.X → R.X → ℂ) (A : ℝ → HermLine J) : Prop :=
  ∃ (ref : HermLine J) (C : ℝ), IsSmoothHerm ref ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (A t) ∧ (A t).a = ref.a ∧
    IsPsh R.A (potOf R (A t) + Θ.rsmul C) ∧ ∀ x ∉ bdry s,
      -C * Real.log (rW L s x) ≤ Real.log ((A t).h (R.lift x x)) - Real.log (ref.h (R.lift x x)) ∧
        Real.log ((A t).h (R.lift x x)) - Real.log (ref.h (R.lift x x)) ≤ C

end Tame

def Replace : Prop :=
  PB.Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (P B : Ideal (MRing J)) (e a b : ℕ) (R : AnLogRes P B e) (Θ L : LocPot R.X) (s : R.X → R.X → ℂ)
    (nb : ℕ) (mb : Fin nb → ℕ) (Wb : Fin nb → Set R.X) (σ : Type) [Fintype σ] (A : ℝ → σ → HermLine J) (M : ℝ → HermLine J)
    (m : σ → ℤ) (n : Fin b → σ → ℤ) (f g : MRing J) (w : ℝ → ((Σ k, J k) → ℂ) → ℝ) (C : ℝ),
    a + b = e + 1 → IsArithVar P (e + 1) → IsPotential R.A Θ → IsPosPot R.A Θ → IsPotential R.A L → IsSection R.A L s →
    IsSNC R.A L s mb Wb → (∀ x, logNormSec L s x ≤ 0) → (∀ i, Tame R Θ L s fun t => A t i) → Tame R Θ L s M →
    (∀ᶠ t in 𝓝[>] (0 : ℝ), IsLineIso P (Top.combLine (A t) m).a (M t).a f g ∧
      IsDefectOn P (mcPts P) f g (Top.combLine (A t) m) (M t) (w t) ∧
      ∀ x ∉ bdry s, |w t (R.lift x x)| ≤ C * Real.log (rW L s x)) →
    (∀ K' ⊆ (bdry s)ᶜ, IsCompact K' → TendstoUniformlyOn (fun t x => w t (R.lift x x)) (fun _ => 0) (𝓝[>] 0) K') →
    Tendsto (fun t => II K J P (a + b) (Fin.append (fun _ : Fin a => M t) fun j => Top.combLine (A t) (n j)) -
      II K J P (a + b) (Fin.append (fun _ : Fin a => Top.combLine (A t) m) fun j => Top.combLine (A t) (n j)))
      (𝓝[>] 0) (𝓝 0)

def RegUnif : Prop :=
  ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n : ℕ) (M : CxModel P n)
    (Xo : Set ((Σ k, J k) → ℂ)) (A : HermLine J) (S : LogLogRegularisationSetting M Xo A) (V : Set M.Xc) (g : M.Xc → ℝ), S.IsTied →
    IsOpen V → ContinuousOn g V → (∀ x ∈ V ∩ S.R.Yo, g x = S.R.ph x) →
    (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ x, S.regWeight t x ≤ C) ∧ ∀ x ∈ V, g x ≤ S.regWeight t x) ∧
      ∀ K' ⊆ V, IsCompact K' → TendstoUniformlyOn S.regWeight g (𝓝[>] 0) K'

def BaseSide : Prop :=
  ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type)
    [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W)
    (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (K' : Type) [Fintype K'] (J' : K' → Type)
    [∀ k, Fintype (J' k)] (P' B' : Ideal (MRing J')) (e : ℕ) (R : AnLogRes P' B' e) (κ : K → K') (v : (Σ k, J k) → Σ k, J' k)
    (Θ : LocPot R.X) (Mt : ℝ → HermLine J'), S.IsTied → IsBlockMap κ v → imageZ v P' = mCoordIdeal D.y →
    IsPotential R.A Θ → IsPosPot R.A Θ → (∀ t, IsPullHerm κ v (muReg Hd S B t) (Mt t)) →
    ∃ (ref : HermLine J') (C : ℝ), IsSmoothHerm ref ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (Mt t) ∧ (Mt t).a = ref.a ∧ IsPsh R.A (potOf R (Mt t) + Θ.rsmul C) ∧
        (∀ x, Real.log ((Mt t).h (R.lift x x)) - Real.log (ref.h (R.lift x x)) ≤ C) ∧
        ∀ x, (fun p => R.lift x x (v p)) ∉ D.Bd →
          Real.log ((muVert Hd B).h fun p => R.lift x x (v p)) ≤ Real.log ((Mt t).h (R.lift x x))) ∧
      ∀ K₀ ⊆ {x | (fun p => R.lift x x (v p)) ∉ D.Bd}, IsCompact K₀ → TendstoUniformlyOn
        (fun t x => Real.log ((Mt t).h (R.lift x x)) - Real.log ((muVert Hd B).h fun p => R.lift x x (v p)))
        (fun _ => 0) (𝓝[>] 0) K₀

end LevelTowerAlt.Comparison₂
