import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContinuousCrystallineMatrixRepOfIntertwinesDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isContinuousCrystallineMatrixRep_of_intertwines_det_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r r' : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (U : ZMod f → Multiset ℤ) (a : Mx ↥(OL LL) n n), MatGood P emb r U → Tw r' r a → a.det ≠ 0 → MatGood P emb r' U := by
  first | exact @GlobalTheory.WachPlace.matGood_of_tw | exact GlobalTheory.WachPlace.matGood_of_tw | (intros; apply GlobalTheory.WachPlace.matGood_of_tw <;> assumption)
