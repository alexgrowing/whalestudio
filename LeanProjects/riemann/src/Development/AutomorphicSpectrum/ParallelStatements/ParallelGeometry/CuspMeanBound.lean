import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

noncomputable section

namespace GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.CuspMeanBound

open NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar

section Clauses

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II Ψ K J Ω W} (Hd : HodgeData Dc)

def corrWeight (U : ((Σ k, J k) → ℂ) → ℝ) (z : (Σ k, J k) → ℂ) : ℝ := phMu Hd z + U z / 2

def meanOf (U : ((Σ k, J k) → ℂ) → ℝ) : ℝ :=
  ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) U / degMu Hd

variable {w : ((Σ k, J k) → ℂ) → ℝ} {M : XModel Dc} (S : BoundedRegularisationSetting M Dc.Xo Hd.aMu w)

def BundlePos : Prop :=
  ∀ B p q : ℕ, 4 * Dc.f + 2 ≤ B → 0 < p → p ≤ q → ∀ᶠ t' in 𝓝[>] (0 : ℝ),
    IsSemipositiveRel (mCoordIdeal Dc.y) (mCoordIdeal Dc.y) (MUc Hd S B p q t') ∧
      NefOnFibres (mCoordIdeal Dc.y) (MUc Hd S B p q t').a ∧ Ht.AmpleQ Dc.y (MUc Hd S B p q t').a

def HtLower (Ch rd Lval : ℝ) (pt : Ideal (MRing J) → Prop) : Prop :=
  ∀ B p q : ℕ, 4 * Dc.f * Dc.N ^ 2 ≤ B → 0 < p → p ≤ q → ∀ᶠ t' in 𝓝[>] (0 : ℝ),
    ∀ Q : Ideal (MRing J), IsArithVar Q 1 → mCoordIdeal Dc.y ≤ Q → pt Q →
      -(Ch * Dc.f * Dc.j' * abelian₂ B rd Lval) - (p : ℝ) / q * Dc.KA ≤ htMUc Hd S B p q t' Q

def HtInterior (Ch rd Lval : ℝ) : Prop := HtLower Hd S Ch rd Lval fun Q => ∀ z ∈ mcPts Q, z ∉ Dc.Bd

def HtBoundary (Ch rd Lval : ℝ) : Prop := HtLower Hd S Ch rd Lval fun Q => ∃ z ∈ mcPts Q, z ∈ Dc.Bd

def MeanUpper (Cu rd Lval : ℝ) (U : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  1 ≤ Dc.j' → 3 * Dc.j' + 1 ≤ Dc.N → ∀ B : ℕ, 4 * Dc.f * Dc.N ^ 2 ≤ B →
    meanOf Hd U ≤ Cu * Dc.f * Dc.j' * abelian₂ B rd Lval

theorem htInterior_and_htBoundary_iff (Ch rd Lval : ℝ) :
    HtInterior Hd S Ch rd Lval ∧ HtBoundary Hd S Ch rd Lval ↔ HtLower Hd S Ch rd Lval fun _ => True := by
  constructor
  · rintro ⟨h₁, h₂⟩ B p q hB hp hq
    filter_upwards [h₁ B p q hB hp hq, h₂ B p q hB hp hq] with t a b Q hQ hP _
    by_cases h : ∃ z ∈ mcPts Q, z ∈ Dc.Bd
    · exact b Q hQ hP h
    · exact a Q hQ hP fun z hz hb => h ⟨z, hz, hb⟩
  · intro h
    exact ⟨fun B p q hB hp hq => (h B p q hB hp hq).mono fun _ a Q hQ hP _ => a Q hQ hP trivial,
      fun B p q hB hp hq => (h B p q hB hp hq).mono fun _ a Q hQ hP _ => a Q hQ hP trivial⟩

theorem corrWeight_cuspWeight {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt] (Cd : CuspData Dc O Lt) :
    corrWeight Hd Cd.cuspWeight = cuspCorr Hd Cd ∧ meanOf Hd Cd.cuspWeight = meanU Hd Cd :=
  ⟨rfl, rfl⟩

end Clauses

def Admissible {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type}
    [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
    [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W}
    {Hd : HodgeData Dc} (Or : CptOrigin Y S₀ Dc Hd) : Prop :=
  (∀ r : ℕ, r ∈ S₀ ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M') ∧ S₀.card ≤ 4 * Dc.f * Dc.N ^ 2 ∧
    (∃ B₁ : ℕ, 4 * Dc.f + 2 ≤ B₁ ∧ ∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ S₀) ∧ Or.Good ∧ Dc.j' ≤ Dc.j

def CuspClauses (Ch Cu : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsAbelianGalois ℚ E →
  ∀ (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l)
    (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y →
  ∀ (II : IntersectionSystem), IsIntersectionSystem II →
  ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd),
    Admissible Or →
  ∀ U : ((Σ k, J k) → ℂ) → ℝ, Or.𝔐.IsCuspWeight Or.sm U →
    (∀ (M : XModel Dc) (S : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrWeight Hd U)), S.IsTied →
      BundlePos Hd S ∧ HtInterior Hd S Ch (hostRd E) (hostLval H) ∧ HtBoundary Hd S Ch (hostRd E) (hostLval H)) ∧
    MeanUpper Hd Cu (hostRd E) (hostLval H) U

end GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.CuspMeanBound
