import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.DataDIV
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardTargetJumpsEqRank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit

noncomputable section

namespace GlobalTheory.HTW.Rec.Model

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

instance decThickN {n b η : ℕ} (sz : ZMod n → ℕ) : DecidablePred (ThickN b η sz) := fun i => by
  unfold ThickN; infer_instance

def wordMixed : NWord 2 where
  up i := i = 1
  sz i := if i = 1 then 5 else 100
  b := 100
  w := 5
  S := 1
  η := 1
  m := 1
  Mi i := if i = 1 then 1 else 101
  hi i := if i = 1 then 6 else 1

def wordThick : NWord 2 where
  up i := i = 1
  sz i := if i = 1 then 499 else 500
  b := 499
  w := 2
  S := 1
  η := 1
  m := 1
  Mi i := if i = 1 then 1 else 501
  hi i := if i = 1 then 500 else 1

def cycPowSum {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (a : Fin n → ℤ) :
    ↥(GK K) →* Matrix (Fin n) (Fin n) ↥LL.1 where
  toFun g := Matrix.diagonal fun c => (((cycLL (P.PD K) ↥LL.1 ^ (-a c)) g : (↥LL.1)ˣ) : ↥LL.1)
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, Units.val_mul, Matrix.diagonal_mul_diagonal]

theorem cycPowSum_apply {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (a : Fin n → ℤ)
    (g : ↥(GK K)) (v : Fin n → ↥LL.1) (c : Fin n) :
    matRep (cycPowSum P K LL a) g v c = (((cycLL (P.PD K) ↥LL.1 ^ (-a c)) g : (↥LL.1)ˣ) : ↥LL.1) * v c :=
  Matrix.mulVec_diagonal _ v c

theorem cycPowSum_crys_mult {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) {n : ℕ} (a : Fin n → ℤ) :
    IsCrys (P.PD K) (matRep (cycPowSum P K LL a)) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (u : ℤ),
      multV (P.PD K) (matRep (cycPowSum P K LL a)) τ u = ((List.ofFn a).count u : ℕ) := by
  induction n with
  | zero =>
    refine ⟨?_, fun τ u => ?_⟩
    · unfold IsCrys
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (M := Fin 0 → ↥LL.1), mul_zero]
    · unfold multV
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
      simp
  | succ n ih =>
    obtain ⟨c1, m1⟩ := ih fun c => a c.succ
    obtain ⟨c2, -, m2⟩ := GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL (-a 0)
    obtain ⟨-, hc, hm⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T K LL _ (matRep (cycPowSum P K LL a)) _
      (charRep (cycLL (P.PD K) ↥LL.1 ^ (-a 0))) _ (matRep (cycPowSum P K LL fun c => a c.succ))
      (Fin.consLinearEquiv ↥LL.1 fun _ => ↥LL.1).symm fun g v =>
        Prod.ext (cycPowSum_apply P K LL a g v 0) (funext fun c =>
          (cycPowSum_apply P K LL a g v c.succ).trans (cycPowSum_apply P K LL (fun c => a c.succ) g (Fin.tail v) c).symm)
    refine ⟨hc.2 ⟨c2, c1⟩, fun τ u => ?_⟩
    rw [hm, m1, m2, List.ofFn_succ, List.count_cons, neg_neg]
    by_cases h : u = a 0
    · simp [h, add_comm]
    · simp [h, Ne.symm h]

section Input

variable (D : D7) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
  (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1)

end Input

end GlobalTheory.HTW.Rec.Model
