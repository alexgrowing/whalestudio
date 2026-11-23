import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv

namespace GlobalTheory.StdSndSB

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem isIntM_rightBlock {k d a : ℕ} {Y : Matrix (Fin k) (Fin d) (EAf D)} (h : IsIntM Y) :
    IsIntM (rightBlock a Y) := fun i j => by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · exact zero_mem _

private theorem rightBlock_shift {k d a : ℕ} {Y Y' W : Matrix (Fin k) (Fin d) (EAf D)} {c : EAf D}
    (h : ∀ i j, Y' i j = Y i j + c * W i j) (i j : Fin k) :
    rightBlock a Y' i j = rightBlock a Y i j + c * rightBlock a W i j := by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · rw [mul_zero, add_zero]

set_option maxHeartbeats 1000000 in
private theorem stdSnd_shift {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} {n₀ n c : ℕ} (hn₀ : ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I)
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1)
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : ℕ) (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) {t t' : WO A WW} (hh : IsHalf (cA D e) t' ↔ IsHalf (cA D e) t)
    {W : Matrix (Fin A.rank) (Fin WW.rank) (EAf D)} (hW : IsIntM W)
    (h : ∀ i j, dualCoord A WW βA βW t' i j = dualCoord A WW βA βW t i j + ((n₀ * (n * c) : ℕ) : EAf D) * W i j) :
    stdSnd ν e I a A WW βA βW t' = stdSnd ν e I a A WW βA βW t := by
  have hW1 : ∀ i j, ((n * c : ℕ) : EAf D) * W i j ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hW i j)
  have hW2 : ∀ i j, (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hW1 i j)
  have ha : ∀ i j, dualCoord A WW βA βW t' i j =
      dualCoord A WW βA βW t i j + (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) := fun i j => by
    rw [h, Nat.cast_mul n₀, mul_assoc]
  have hb : ∀ i j, dualCoord A WW βA βW t i j =
      dualCoord A WW βA βW t' i j + (n₀ : EAf D) * (-(((n * c : ℕ) : EAf D) * W i j)) := fun i j => by
    rw [ha, mul_neg, add_neg_cancel_right]
  have hint : IsIntM (dualCoord A WW βA βW t') ↔ IsIntM (dualCoord A WW βA βW t) :=
    forall_congr' fun i => forall_congr' fun j => by
      rw [ha]
      exact add_mem_cancel_right (hW2 i j)
  have hid : (∀ i j, j.1 < a → InId I (dualCoord A WW βA βW t' i j)) ↔
      ∀ i j, j.1 < a → InId I (dualCoord A WW βA βW t i j) :=
    ⟨fun H i j hi => inId_shift hn₀ (neg_mem (hW1 i j)) (hb i j) (H i j hi),
      fun H i j hi => inId_shift hn₀ (hW1 i j) (ha i j) (H i j hi)⟩
  unfold stdSnd
  by_cases hcnd : IsHalf (cA D e) t ∧ IsIntM (dualCoord A WW βA βW t) ∧
      ∀ i j, j.1 < a → InId I (dualCoord A WW βA βW t i j)
  · rw [if_pos hcnd, if_pos ⟨hh.2 hcnd.1, hint.2 hcnd.2.1, hid.2 hcnd.2.2⟩]
    refine (unitChar_congr he hl hc (isIntM_rightBlock hcnd.2.1)
      (Z := rightBlock a fun i j => (n₀ : EAf D) * W i j)
      (isIntM_rightBlock fun i j => mul_mem (natCast_mem _ _) (hW i j))
      (rightBlock_shift (c := ((n * c : ℕ) : EAf D)) fun i j => ?_)).symm
    rw [h, Nat.cast_mul n₀]
    ring
  · rw [if_neg hcnd, if_neg fun h' => hcnd ⟨hh.1 h'.1, hint.1 h'.2.1, hid.1 h'.2.2⟩]

private theorem dualCoord_add (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D))
    (x y : WO A WW) : dualCoord A WW βA βW (x + y) = dualCoord A WW βA βW x + dualCoord A WW βA βW y := by
  unfold dualCoord
  rw [GlobalTheory.PlaceVec.frMapAdj_add, smul_add]

private theorem mul_nsmul_mul_eq_nsmul_mul_nsmul {R : Type} [CommRing R] (k l : ℕ) (x y : R) : (k * l) • (x * y) = (k • x) * (l • y) := by
  simp only [nsmul_eq_mul]
  push_cast
  ring

private theorem inv_aux {R : Type} [CommRing R] (k : ℕ) {x x' : R} (h : x' * x = 1) (y : R) :
    k • y = (k • x') * (x * y) := by
  simp only [nsmul_eq_mul]
  linear_combination (-(k : R) * y) * h

set_option maxHeartbeats 1000000 in
private theorem dualCoord_up (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO A WW, IsIntM (x.map (toEAf D)) → IsIntM (k • dualCoord A WW βA βW x) := by
  obtain ⟨k, hk, h⟩ := GlobalTheory.PlaceVec.frMapAdj_up A WW βA βW
  obtain ⟨d, hd, hx⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0)
  refine ⟨d * k, mul_pos hd hk, fun x hi i j => ?_⟩
  change (d * k) • (eToEAf D D.host.xi0 * frMapAdj A WW βA βW x i j) ∈ OO
  rw [mul_nsmul_mul_eq_nsmul_mul_nsmul]
  exact mul_mem hx (h x hi i j)

set_option maxHeartbeats 1000000 in
private theorem dualCoord_down (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO A WW, IsIntM (dualCoord A WW βA βW x) → IsIntM ((k • x).map (toEAf D)) := by
  obtain ⟨k, hk, h⟩ := GlobalTheory.PlaceVec.frMapAdj_down A WW βA βW
  obtain ⟨d, hd, hx⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0⁻¹)
  have h1 : eToEAf D D.host.xi0⁻¹ * eToEAf D D.host.xi0 = 1 := by
    rw [← RingHom.map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one]
  refine ⟨k * d, mul_pos hk hd, fun x hi => ?_⟩
  have hn : frMapAdj A WW βA βW (d • x) = d • frMapAdj A WW βA βW x :=
    (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add A WW βA βW)).map_nsmul d x
  rw [mul_smul, GlobalTheory.PlaceVec.map_toEAf_nsmul]
  refine h (d • x) fun i j => ?_
  rw [hn]
  change d • frMapAdj A WW βA βW x i j ∈ OO
  rw [inv_aux d h1]
  exact mul_mem hx (hi i j)

set_option maxHeartbeats 1000000 in

private theorem stdSnd_isSB {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (a : ℕ) (A WW : HSp D) (βA : GL (Fin A.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) (Λ : AddSubgroup (WO A WW))
    (hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ Λ, IsIntM (dualCoord A WW βA βW (M • u)))
    (hC : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A WW, IsHalf (cA D e) t → IsIntM (dualCoord A WW βA βW t) → K • t ∈ Λ) :
    IsSBHalf (cA D e) Λ (stdSnd ν e I a A WW βA βW) := by
  obtain ⟨M, hM, hB⟩ := hB
  obtain ⟨K, hK, hC⟩ := hC
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  obtain ⟨c, hc, hcS⟩ := GlobalTheory.PlaceVec.exists_nat_mem_places S
  have hGn : ∀ (k : ℕ) x, dualCoord A WW βA βW (k • x) = k • dualCoord A WW βA βW x := fun k x =>
    (AddMonoidHom.mk' _ (dualCoord_add A WW βA βW)).map_nsmul k x
  refine ⟨fun t ht => ?_, (n₀ * (n * c)) * (K * M), Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) (Nat.mul_pos hK hM),
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · unfold stdSnd at ht
    by_contra h
    exact ht (if_neg fun h' => h h'.1)
  · refine stdSnd_shift he hnI hl hcS a A WW βA βW (W := K • dualCoord A WW βA βW (M • u))
      ?_ (GlobalTheory.PlaceVec.isIntM_nsmul (hB u hu) K) fun i j => ?_
    · rw [GlobalTheory.PlaceModel.isHalf_iff A WW, GlobalTheory.PlaceModel.isHalf_iff A WW]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A WW).1 hh) _)
    · rw [dualCoord_add, mul_smul, mul_smul K, hGn, hGn K, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
  · have h : IsHalf (cA D e) t ∧ IsIntM (dualCoord A WW βA βW t) := by
      unfold stdSnd at ht
      by_contra h
      exact ht (if_neg fun h' => h ⟨h'.1, h'.2.1⟩)
    rw [show (n₀ * (n * c)) * (K * M) = ((n₀ * (n * c)) * M) * K by ring, mul_smul]
    exact nsmul_mem (hC t h.1 h.2) _

set_option maxHeartbeats 1000000 in
private theorem main (ν : (AE D)ˣ →* Circle) (hν : Continuous ν) (e : AE D) (S : Finset (Pl D.host.E))
    (he : IsIdemSum e S) (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥) (a : ℕ) (A WW : HSp D)
    (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    (hA : IsSelfDualC A ΛA) (hW : IsSelfDualC WW ΛW) (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) :
    IsSBHalf (cA D e) (latO A WW (ΛA : Set (Fin A.rank → D.host.E)) (ΛW : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (stdSnd ν e I a A WW βA βW) := by
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  obtain ⟨k₁, hk₁, h₁⟩ := dualCoord_up A WW βA βW
  obtain ⟨k₂, hk₂, h₂⟩ := dualCoord_down A WW βA βW
  obtain ⟨k₃, hk₃, h₃⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := A) (T := WW) hA.1.fg hW.1.fg
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hA.1 hW.1
  refine stdSnd_isSB hν he hI a A WW βA βW _ ⟨k₁ * k₃, mul_pos hk₁ hk₃, fun u hu => ?_⟩
    ⟨k₄ * k₂, mul_pos hk₄ hk₂, fun t ht hi => ?_⟩
  · have hn : dualCoord A WW βA βW (k₁ • k₃ • u) = k₁ • dualCoord A WW βA βW (k₃ • u) :=
      (AddMonoidHom.mk' _ (dualCoord_add A WW βA βW)).map_nsmul k₁ _
    rw [mul_smul, hn]
    exact h₁ _ (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₃ u hu)
  · rw [mul_smul]
    exact h₄ (k₂ • t) (GlobalTheory.PlaceVec.half_infPart hinf (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A WW).1 ht) _)) (h₂ t hi)

end

end GlobalTheory.StdSndSB

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardThetaPair_second_isSchwartzBruhat_conjHalf : ∀ {D : D7} (ν : (AE D)ˣ →* Circle), Continuous ν → ∀ (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)),
    IsIdemSum e S → ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ (a : ℕ) (A' WW : HSp D)
    (ΛA : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A' ΛA → IsSelfDualC WW ΛW → ∀ (βA : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)),
    IsSBHalf (cA D e) (latO A' WW (ΛA : Set (Fin A'.rank → D.host.E)) (ΛW : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA βW) :=
  fun ν hν e S he I hI a A WW ΛA ΛW hA hW βA βW => GlobalTheory.StdSndSB.main ν hν e S he I hI a A WW ΛA ΛW hA hW βA βW
