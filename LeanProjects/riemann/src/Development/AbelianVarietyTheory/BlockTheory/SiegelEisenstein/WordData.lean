import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalRingCardinality.DataTies
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2

namespace GlobalTheory.IndefiniteRowSideFullHecke.WordCollisionBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def WordData (D : D7) (u : D.what₂.Word) : Prop :=
  let k : ℝ := D.R.k
  let Del : ℝ := D.s.Del
  (∀ τ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l ∧ vOne D τ l ≤ 4 * k * Del) ∧
  (∀ l : ℕ, 1 ≤ l → l ≤ D.R.k - 2 →
    (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2) ∨ (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2 - Del)) ∧
  (∀ τ, 4 * k * Del ≤ uOne D u τ 1 - vOne D τ 1) ∧
  (∀ τ, ¬ IsTop D τ → uOne D u τ 1 - vOne D τ 1 ≤ 8 * k * Del) ∧
  (∀ τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) ∧
  (∀ τ, IsTop D τ → 3 ≤ bOne D τ 1 - bTop D τ ∧ bOne D τ 1 / 2 ≤ bTop D τ) ∧
  (∀ τ, InterlaceS (show D.R.k ≤ D.R.r by have := D.R.two_le_m; unfold Formalism.BasicNotions.Ranks.r; omega)
    (uS D u τ) (lamS D.R (D.hc τ))) ∧
  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  (∀ i, (D.host.g i).Prime ∧ SplitsE D (D.host.g i)) ∧ D.host.g 0 ≠ D.host.g 1 ∧
  ((D.mem u).A.T).Prime ∧ SplitsE D (D.mem u).A.T ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧
  (D.mem u).A.T ≡ 1 [MOD (D.host.g 0 * D.host.g 1) ^ 2]

def Sizes (D : D7) (L : ℝ) (u : D.what₂.Word) (C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let m : ℝ := D.R.m
  let f : ℝ := D.R.f
  let n : ℝ := D.R.r
  let r : ℝ := D.R.rS
  let b : ℝ := Real.exp L
  let Del : ℝ := D.s.Del
  let T : ℝ := ((D.mem u).A.T : ℝ)
  C' * m ^ 5 * f * L ≤ k ∧
  D.R.m ^ 4 ≤ D.R.f ∧ D.R.f ≤ D.R.k ∧
  Real.log f ≤ Real.sqrt r ∧
  Cl * L ≤ f * Real.log k ∧
  Cl * (m ^ 2 * L) ≤ k ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → Cl * (m * k * Del) ≤ bOne D τ j) ∧
  Cl * (m * Real.log D.host.v) ≤ k ∧
  Cl * (m ^ 3 * L * Real.log D.host.rdE) ≤ k * Real.log k ^ 2 ∧
  Real.log D.host.rdE ≤ L / Cl ∧
  (∀ i, (k * b) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ b ^ Cg) ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → max (k ^ Cl) (b ^ cb) ≤ bOne D τ j ∧ bOne D τ j ≤ b ^ (2 : ℝ)) ∧
  (∀ τ, bOne D τ D.R.m ≤ 2 * bOne D τ 1) ∧
  (∀ τ, uOne D u τ 1 ≤ b ^ Cu) ∧
  1 ≤ D.host.v ∧
  (k * f * L) ^ Cl ≤ Del ∧
  (∀ τ j, 1 ≤ j → j + 1 ≤ D.R.m → Cl * n ^ 19 * f ^ 5 * L ≤ bOne D τ (j + 1) - bOne D τ j) ∧
  (∀ τ (i : Fin D.R.r) (h : i.1 + 1 < D.R.r),
    Cl * k * m ^ 4 + n * m ^ 10 < lamS D.R (D.hc τ) i - lamS D.R (D.hc τ) ⟨i.1 + 1, h⟩) ∧
  b ^ (cT * m) ≤ T ∧ T ≤ b ^ (CT * m) ∧
  1 ≤ (D.host.ka / gg D) ^ (2 * D.R.rS) * T ∧
  Cl ≤ m ∧ 0 < Cl

def CollisionBound : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (L : ℝ) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (u : D.what₂.Word),
        1 < L → WordData D u → Sizes D L u C' Cl Cg cb Cu cT CT →
        Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → Nonempty (SIso D.s (sOf hF)) →
        ConcTie X Y → (Y.tO u u).AbsConv →
        (Y.tO u u).pairAbs ((Y.tO u u).big (Y.tO u u).nzSet) ≤
          Real.exp (-((1 / 3 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) *
            (duC X Y u ^ 2 / DstC X + duC X Y u)

end GlobalTheory.IndefiniteRowSideFullHecke.WordCollisionBound
