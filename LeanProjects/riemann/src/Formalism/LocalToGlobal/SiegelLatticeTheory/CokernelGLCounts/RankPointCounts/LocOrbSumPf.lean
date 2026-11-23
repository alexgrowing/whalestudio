import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalOrbitGerms

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def orbR (M : Loc.Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {Z' | ∃ l ρ : Matrix (Fin n) (Fin n) E, Formalism.MainNotions.S.TieN.IntLow M l ∧ Formalism.MainNotions.S.TieN.IntUp M ρ ∧ Z' = l * Z * ρ}

def zAt {m : ℕ} (a : Loc.Pt E (m + 1)) (xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
  Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2

def muA (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) :
    Measure ((Loc.IL (m + 1) → E) × (Loc.IN a → E)) :=
  (Measure.pi fun _ : Loc.IL (m + 1) => M.mu).prod (Measure.pi fun _ : Loc.IN a => M.mu)

def IsZO (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)) :
    Prop :=
  ∃ xy, (∀ i j, zAt a xy i j ∈ M.R) ∧ O = orbR M (zAt a xy)

def wtZ (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)) : ℝ :=
  (muA M a {xy | zAt a xy ∈ O}).toReal

def OrbCut (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : Prop :=
  ∀ (k : ℂ) (V : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E) → ℂ),
    (∀ O, ¬ IsZO M a O → V O = 0) →
    (∀ O, IsZO M a O → ∃ xy, zAt a xy ∈ O ∧ V O = k * M.bbIntegrand a c xy * (wtZ M a O : ℂ)) →
    HasSum V (k * M.BB a c) ∧ Summable (fun O => ‖V O‖)

end Loc

section Shift

variable {D : Formalism.BasicNotions.D7}

def shM (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : MatP D p :=
  Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0

def ModShift (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ a, modPt δ T T' p w = some a → a.mat = modMat δ T T' p w + shM δ T T' p w

def NAutNe (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) : Prop :=
  ∀ c : (M p).Cls D.R.rS, (M p).nAut c ≠ 0

end Shift

end Formalism.L2.SG.Pf.LocOrbSumPf
