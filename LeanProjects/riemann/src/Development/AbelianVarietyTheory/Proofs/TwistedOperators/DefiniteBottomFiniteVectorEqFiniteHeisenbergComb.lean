import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option synthInstance.maxHeartbeats 100000

noncomputable section

namespace GlobalTheory.BottomFinComb

open StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

theorem eToEAf_mem (α : 𝓞 D.host.E) : eToEAf D (α : D.host.E) ∈ OO := (oToS D.host.F D.host.E α).2

theorem exists_nat_den (a : D.host.E) : ∃ q : ℕ, 0 < q ∧ (q : EAf D) * eToEAf D a ∈ OO := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := D.host.E) {a}
  have hi : IsIntegral ℤ (y • a) := hy a (by simp)
  have h1 : eToEAf D (y • a) ∈ OO := eToEAf_mem ⟨y • a, hi⟩
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hy0) (Int.natAbs_pos.2 hy0), ?_⟩
  have h0 : ((y.natAbs * y.natAbs : ℕ) : EAf D) = ((y * y : ℤ) : EAf D) := by
    rw [← Int.natAbs_mul_self' y, ← Nat.cast_mul, Int.cast_natCast]
  have h2 : ((y.natAbs * y.natAbs : ℕ) : EAf D) * eToEAf D a = (y : EAf D) * eToEAf D (y • a) := by
    rw [h0, zsmul_eq_mul, map_mul, map_intCast, Int.cast_mul, mul_assoc]
  rw [h2]
  exact mul_mem (intCast_mem _ _) h1

theorem frMapAdj_add' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  unfold frMapAdj
  rw [Matrix.map_add (cA D) (fun a b => (cA D).map_add a b), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

theorem frMapAdj_zero' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 := by
  have h := frMapAdj_add' S T βS βT 0 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem frMapAdj_nsmul' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (k : ℕ)
    (x : WO S T) : frMapAdj S T βS βT (k • x) = k • frMapAdj S T βS βT x := by
  induction k with
  | zero => rw [zero_smul, zero_smul, frMapAdj_zero']
  | succ n ih => rw [succ_nsmul, succ_nsmul, frMapAdj_add', ih]

theorem dualCoord_add_nsmul (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D))
    (t u : WO A' WW) (k : ℕ) :
    dualCoord A' WW βA' βW (t + k • u) = dualCoord A' WW βA' βW t + k • dualCoord A' WW βA' βW u := by
  unfold dualCoord
  rw [frMapAdj_add', frMapAdj_nsmul', smul_add, smul_comm]

theorem isIntM_rightBlock {k d : ℕ} (a : ℕ) {Y : Matrix (Fin k) (Fin d) (EAf D)} (h : IsIntM Y) :
    IsIntM (rightBlock a Y) := fun i j => by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · exact zero_mem _

theorem rightBlock_shift {k d : ℕ} (a : ℕ) {Y Y' Z : Matrix (Fin k) (Fin d) (EAf D)} {c : EAf D}
    (h : ∀ i j, Y' i j = Y i j + c * Z i j) (i j : Fin k) :
    rightBlock a Y' i j = rightBlock a Y i j + c * rightBlock a Z i j := by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · rw [mul_zero, add_zero]

set_option maxHeartbeats 1000000 in

theorem stdSnd_shift {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} {n₀ n c : ℕ} (hn₀ : ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I)
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1)
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) {t t' : WO A' WW} (hh : IsHalf (cA D e) t' ↔ IsHalf (cA D e) t)
    {Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)} (hZ : IsIntM Z)
    (h : ∀ i j, dualCoord A' WW βA' βW t' i j =
      dualCoord A' WW βA' βW t i j + ((n₀ * (n * c) : ℕ) : EAf D) * Z i j) :
    stdSnd ν e I a A' WW βA' βW t' = stdSnd ν e I a A' WW βA' βW t := by
  have hW1 : ∀ i j, ((n * c : ℕ) : EAf D) * Z i j ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hZ i j)
  have hW2 : ∀ i j, (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * Z i j) ∈ OO := fun i j =>
    mul_mem (natCast_mem _ _) (hW1 i j)
  have ha : ∀ i j, dualCoord A' WW βA' βW t' i j =
      dualCoord A' WW βA' βW t i j + (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * Z i j) := fun i j => by
    rw [h, Nat.cast_mul n₀, mul_assoc]
  have hb : ∀ i j, dualCoord A' WW βA' βW t i j =
      dualCoord A' WW βA' βW t' i j + (n₀ : EAf D) * (-(((n * c : ℕ) : EAf D) * Z i j)) := fun i j => by
    rw [ha, mul_neg, add_neg_cancel_right]
  have hint : IsIntM (dualCoord A' WW βA' βW t') ↔ IsIntM (dualCoord A' WW βA' βW t) :=
    forall_congr' fun i => forall_congr' fun j => by
      rw [ha]
      exact add_mem_cancel_right (hW2 i j)
  have hid : (∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t' i j)) ↔
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j) :=
    ⟨fun H i j hi => inId_shift hn₀ (neg_mem (hW1 i j)) (hb i j) (H i j hi),
      fun H i j hi => inId_shift hn₀ (hW1 i j) (ha i j) (H i j hi)⟩
  unfold stdSnd
  by_cases hcnd : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) ∧
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j)
  · rw [if_pos hcnd, if_pos ⟨hh.2 hcnd.1, hint.2 hcnd.2.1, hid.2 hcnd.2.2⟩]
    refine (unitChar_congr he hl hc (isIntM_rightBlock a hcnd.2.1)
      (Z := rightBlock a fun i j => (n₀ : EAf D) * Z i j)
      (isIntM_rightBlock a fun i j => mul_mem (natCast_mem _ _) (hZ i j))
      (rightBlock_shift a (c := ((n * c : ℕ) : EAf D)) fun i j => ?_)).symm
    rw [h, Nat.cast_mul n₀]
    ring
  · rw [if_neg hcnd, if_neg fun h' => hcnd ⟨hh.1 h'.1, hint.1 h'.2.1, hid.1 h'.2.2⟩]

set_option maxHeartbeats 1000000 in

theorem stdSnd_isSB {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (a : ℕ) (A' WW : HSp D)
    (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (Λ : AddSubgroup (WO A' WW))
    (hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ Λ, ∀ i j, (M : EAf D) * dualCoord A' WW βA' βW u i j ∈ OO)
    (hC : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A' WW, IsHalf (cA D e) t → IsIntM (dualCoord A' WW βA' βW t) → K • t ∈ Λ) :
    IsSBHalf (cA D e) Λ (stdSnd ν e I a A' WW βA' βW) := by
  obtain ⟨M, hM, hB⟩ := hB
  obtain ⟨K, hK, hC⟩ := hC
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  obtain ⟨c, hc, hcS⟩ : ∃ c : ℕ, 0 < c ∧ ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    refine ⟨∏ P ∈ S, Ideal.absNorm P.asIdeal, Finset.prod_pos fun P _ =>
      Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun P hP => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun P : Pl D.host.E => Ideal.absNorm P.asIdeal) hP
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem P.asIdeal)
  refine ⟨fun t ht => ?_, K * ((n₀ * (n * c)) * M),
    Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM), fun u hu hh t => ?_, fun t ht => ?_⟩
  · unfold stdSnd at ht
    by_contra h
    exact ht (if_neg fun h' => h h'.1)
  · refine stdSnd_shift he hnI hl hcS a A' WW βA' βW
      (Z := fun i j => (K : EAf D) * ((M : EAf D) * dualCoord A' WW βA' βW u i j))
      ?_ (fun i j => mul_mem (natCast_mem _ _) (hB u hu i j)) fun i j => ?_
    · rw [GlobalTheory.PlaceModel.isHalf_iff A' WW, GlobalTheory.PlaceModel.isHalf_iff A' WW]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 hh) _)
    · rw [dualCoord_add_nsmul, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
      push_cast
      ring
  · have h : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) := by
      unfold stdSnd at ht
      by_contra h
      exact ht (if_neg fun h' => h ⟨h'.1, h'.2.1⟩)
    rw [mul_nsmul]
    exact nsmul_mem (hC t h.1 h.2) _

end GlobalTheory.BottomFinComb

namespace GlobalTheory.BottomFinComb

open StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

set_option maxHeartbeats 1000000 in

theorem finVec_isFinComb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO A' WW), (∀ k, (x k).map (infPart D) = 0) ∧
      X.f' t = ∑ k, c k • heisO W.ψ A' WW (x k) X.vac' := by
  intro D T L sc G W i j A A' WW X hX t
  have he := hX.is.idem t
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hce : cA D (X.e t) * cA D (X.e t) = cA D (X.e t) := by rw [← RingHom.map_mul, hee]
  have hcinf : infPart D (cA D (X.e t)) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hν := (hX.is.weil' t).hecT.1
  have hI : X.ideal (locPl G) t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  have hξ := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  obtain ⟨d, hd, hL1⟩ : ∃ d : ℕ, 0 < d ∧ ∀ u ∈ (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True),
      IsIntM (frMapAdj A' WW X.rA'.β X.rW.β (d • u)) := by
    obtain ⟨k, hk, h⟩ := GlobalTheory.PlaceVec.frMapAdj_up A' WW X.rA'.β X.rW.β
    obtain ⟨M, hM, h'⟩ := GlobalTheory.PlaceDatum.exists_den_latO hX.is.rigA'.1.1.fg hX.is.rigW.1.1.fg
    refine ⟨M * k, Nat.mul_pos hM hk, fun u hu => ?_⟩
    rw [mul_nsmul, frMapAdj_nsmul']
    refine h _ fun a b => ?_
    change toEAf D (M • u a b) ∈ _
    rw [nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact h' u hu a b
  obtain ⟨q, hq, hqξ⟩ := exists_nat_den (D := D) D.host.xi0
  obtain ⟨q', hq', hq'ξ⟩ := exists_nat_den (D := D) D.host.xi0⁻¹
  obtain ⟨m, hm, hmem⟩ : ∃ m : ℕ, 0 < m ∧ ∀ s : WO A' WW, IsHalf (cA D (X.e t)) s →
      IsIntM (frMapAdj A' WW X.rA'.β X.rW.β s) → m • s ∈ (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) := by
    obtain ⟨N, hN, h'⟩ := GlobalTheory.PlaceVec.frMapAdj_down A' WW X.rA'.β X.rW.β
    obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO hX.is.rigA'.1.1 hX.is.rigW.1.1
    refine ⟨N * K, Nat.mul_pos hN hK, fun s hs hi => ?_⟩
    have ht := GlobalTheory.PlaceDatum.infPart_of_half hcinf hs
    rw [mul_nsmul]
    refine h _ (Matrix.ext fun a b => ?_) fun a b => ?_
    · change infPart D (N • s a b) = 0
      rw [nsmul_eq_mul, RingHom.map_mul, show infPart D (s a b) = 0 from congrFun (congrFun ht a) b, mul_zero]
    · change toEAf D (N • s a b) ∈ _
      rw [hom_nsmul]
      exact h' s hi a b
  have hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True), ∀ a b,
      (M : EAf D) * dualCoord A' WW X.rA'.β X.rW.β u a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine ⟨q * d, Nat.mul_pos hq hd, fun u hu a b => ?_⟩
    have h1 := hL1 u hu a b
    rw [frMapAdj_nsmul', Matrix.smul_apply, nsmul_eq_mul] at h1
    have e1 : ((q * d : ℕ) : EAf D) * dualCoord A' WW X.rA'.β X.rW.β u a b =
        ((q : EAf D) * eToEAf D D.host.xi0) * ((d : EAf D) * frMapAdj A' WW X.rA'.β X.rW.β u a b) := by
      unfold dualCoord
      rw [Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e1]
    exact mul_mem hqξ h1
  have hC : ∃ K : ℕ, 0 < K ∧ ∀ s : WO A' WW, IsHalf (cA D (X.e t)) s →
      IsIntM (dualCoord A' WW X.rA'.β X.rW.β s) → K • s ∈ (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) := by
    refine ⟨q' * m, Nat.mul_pos hq' hm, fun s hs hint => ?_⟩
    have h1 : IsIntM (frMapAdj A' WW X.rA'.β X.rW.β (q' • s)) := fun a b => by
      have e1 : frMapAdj A' WW X.rA'.β X.rW.β (q' • s) a b =
          ((q' : EAf D) * eToEAf D D.host.xi0⁻¹) * dualCoord A' WW X.rA'.β X.rW.β s a b := by
        rw [frMapAdj_nsmul', Matrix.smul_apply, nsmul_eq_mul]
        unfold dualCoord
        rw [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_assoc (eToEAf D _), ← map_mul, inv_mul_cancel₀ hξ,
          map_one, one_mul]
      rw [e1]
      exact mul_mem hq'ξ (hint a b)
    have h2 : IsHalf (cA D (X.e t)) (q' • s) :=
      (GlobalTheory.PlaceModel.isHalf_iff A' WW).2 (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 hs) _)
    rw [mul_nsmul]
    exact hmem _ h2 h1
  have hSB := stdSnd_isSB hν he hI A.rank A' WW X.rA'.β X.rW.β _ hB hC
  exact GlobalTheory.AdForm.isFinComb_of_isThetaAt W.ψ A' WW X.rA'.Λ X.rW.Λ (cA D (X.e t)) X.vac' _ (X.f' t) hX.is.isVac'.1
    hX.is.rigA'.1 hX.is.rigW.1 hce hcinf hSB (hX.is.snd t)

end GlobalTheory.BottomFinComb
