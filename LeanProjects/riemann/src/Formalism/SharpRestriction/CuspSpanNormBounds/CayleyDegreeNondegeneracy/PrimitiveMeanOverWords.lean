import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Def

variable (D : D7)

abbrev LatticeW : Type := Submodule (𝓞 D.host.E) (D.sp.X 0).V

def latticeTraceOnW {T : D.host.E} (F : LFlag (hS D) D.R.rS T) (A : LatV D) : LatticeW D :=
  (A ⊔ toO (hS D) (Xsp F)).comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E))

def sublatticeIndex' (A B : LatticeW D) : ℕ := Nat.card (A ⧸ B.comap A.subtype)

def latticeRank (P : LatticeW D) : ℕ := finrank D.host.E (Submodule.span D.host.E (P : Set (D.sp.X 0).V))

def latticeSaturation (L0 P : LatticeW D) : LatticeW D :=
  L0 ⊓ (Submodule.span D.host.E (P : Set (D.sp.X 0).V)).restrictScalars (𝓞 D.host.E)

abbrev latticeDetW (P : LatticeW D) : ℝ := latDetH (D.sp.X 0).hT P

def sublatticeQuadruples (L0 : LatticeW D) (s : ℕ) (De : ℝ) : Set (LatticeW D × LatticeW D × LatticeW D × LatticeW D) :=
  {q | IsPrimitiveSub q.1 L0 ∧ latticeRank D q.1 = D.R.k - s ∧ q.2.1 ≤ q.1 ∧ q.2.2.1 ≤ q.2.1 ∧ q.2.2.2 ≤ q.2.1 ∧
    sublatticeIndex' D q.1 q.2.1 ≠ 0 ∧ sublatticeIndex' D q.2.1 q.2.2.1 ≠ 0 ∧ sublatticeIndex' D q.2.1 q.2.2.2 ≠ 0 ∧
    latticeDetW D q.1 * sublatticeIndex' D q.1 q.2.1 * sublatticeIndex' D q.2.1 q.2.2.1 * sublatticeIndex' D q.2.1 q.2.2.2 ≤ De ∧
    latticeRank D q.2.2.1 = D.R.k - s ∧ latticeRank D q.2.2.2 = D.R.k - s ∧ latticeDetW D q.2.2.1 ≤ De ∧ latticeDetW D q.2.2.2 ≤ De}

def quadrupleOfTriple (Λ : LatV D) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (p : Trip D T') :
    LatticeW D × LatticeW D × LatticeW D × LatticeW D :=
  (latticeSaturation D (L0X D Λ F) (latticeTraceOnW D F (Mlat Λ F p.1 p.2.1 p.2.2 (gS D))),
    latticeTraceOnW D F (Mlat Λ F p.1 p.2.1 p.2.2 (gS D)),
    latticeTraceOnW D F (Mlat Λ F p.1 p.2.1 p.2.2 (gS D)) ⊓ latticeTraceOnW D F (Thp Λ F p.1),
    latticeTraceOnW D F (Mlat Λ F p.1 p.2.1 p.2.2 (gS D)) ⊓ latticeTraceOnW D F (Thp Λ F p.2.1))

def termsOverSublattice (Λ : LatV D) {T : D.host.E} (T' : D.host.E) (F : LFlag (hS D) D.R.rS T) (Z : GramM D)
    (P : LatticeW D) : Set (LFlag (hS D) D.R.rS T') :=
  {F' | IsTermF D Λ F F' ∧ ZEquiv (ZhatL F F') Z ∧ P ≤ latticeTraceOnW D F (Thp Λ F F')}

def positionCount (r f s : ℕ) (NT De Hh : ℝ) : ℝ :=
  NT ^ (2 * r) * De ^ r * 9 ^ (s * f) * Hh ^ (9 * s + 9 * s * r + 16 * r ^ 2)

variable (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def QuadrupleMembership (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ (Z' Z'' : GramM D) (s : ℕ) (De : ℝ), 1 ≤ s →
  ∀ p ∈ PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De,
    quadrupleOfTriple D Λ (lf D F0) p ∈ sublatticeQuadruples D (L0X D Λ (lf D F0)) s De

def TermPositionCount (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Z : GramM D, RelZ D Z → ∀ s : ℕ, 1 ≤ s → s ≤ D.R.k →
  ∀ P : LatticeW D, P ≤ L0X D Λ (lf D F0) → latticeRank D P = D.R.k - s →
  ∀ De Hh : ℝ, 1 ≤ De → latticeDetW D P ≤ De → HHZ D large₂.sc.b C Z ≤ Hh → De ≤ Hh ^ 3 →
    (cntCl (termsOverSublattice D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤
      ENNReal.ofReal (positionCount D.R.rS D.R.f s (NT D u) De Hh)

def PairsModuloNormCount (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ (Z' Z'' : GramM D) (s : ℕ) (De : ℝ), 1 ≤ s →
  ∀ p₀ ∈ PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De,
    (cntCl {p | p ∈ PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De ∧
        TEqv D Λ (lf D F0) p₀.1 p.1 ∧ TEqv D Λ (lf D F0) p₀.2.1 p.2.1} (PEqv D Λ (lf D F0)) : ℝ≥0∞) ≤
      (((4 * D.R.f * s).factorial : ℕ) : ℝ≥0∞)

def PairsFibreCount (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Z' Z'' : GramM D, RelZ D Z' → RelZ D Z'' → ∀ s : ℕ, 2 ≤ s → s ≤ D.R.k →
  ∀ De Hh : ℝ, 1 ≤ De → HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'' ≤ Hh → De ≤ Hh ^ 3 →
    (cntPairs D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De : ℝ≥0∞) ≤
      ((sublatticeQuadruples D (L0X D Λ (lf D F0)) s De).encard : ℝ≥0∞) *
        ENNReal.ofReal (positionCount D.R.rS D.R.f s (NT D u) De Hh ^ 2 * ((4 * D.R.f * s).factorial : ℝ))

def QuadrupleMeanBound (C' Cl Cg cb Cu cT CT C0 A A1 : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ s : ℕ, 2 ≤ s → s ≤ D.R.k → ∀ De : ℝ, 1 ≤ De →
  ∀ HH : ℝ, Hb large₂.sc.b A1 D.R.m D.R.f ≤ HH →
    MeanLe D F0 what₂ (fun Λ => (sublatticeQuadruples D (L0X D Λ (lf D F0)) s De).encard)
      ((De / NT D u) ^ D.R.k * (De * NT D u) ^ (A1 * ((s : ℝ) + cF D.R.f)) * De ^ (cF D.R.f + 4) * XiS D u HH A1 s)

def PrimitiveMeanOverWords (C' Cl Cg cb Cu cT CT C0 A A1 : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ s : ℕ, 2 ≤ s → s ≤ D.R.k → ∀ de : ℕ, 1 ≤ de →
  ∀ HH : ℝ, Hb large₂.sc.b A1 D.R.m D.R.f ≤ HH →
    MeanLe D F0 what₂ (fun Λ => cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) de)
      (((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (A1 * s + A1 * Real.log D.R.f) * XiS D u HH A1 s)

def MeanOverWordsEqGenus : Prop :=
  (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ Λ₀ : LatV D, IsRowLat D F0 Λ₀ →
  ∀ reps : Finset (LatticeW D), Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ₀ (lf D F0)) reps →
  ∀ N : LatticeW D → ℕ∞, (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ L, N (Formalism.HermitianLatticesTheory.gmap γ L) = N L) →
    (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (L0X D Λ (lf D F0)) : ℝ≥0∞)) *
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ₀ (lf D F0))) =
      (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) *
        ∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ * (N L' : ℝ≥0∞)

def GramDeterminantIsNatural : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M : LatticeW D, M ≤ L0X D Λ (lf D F0) →
    ∃ de : ℕ, 1 ≤ de ∧ latticeDetW D M = de

end Def

end Formalism.MainNotions.BridgeLemma₂

end
