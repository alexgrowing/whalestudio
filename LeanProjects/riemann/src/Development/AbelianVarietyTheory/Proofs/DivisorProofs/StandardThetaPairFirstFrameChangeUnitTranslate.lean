import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.frameChangeUnitDeterminant

open Formalism.IndefR.Datum

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem isIntM_mul {b a c : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} {κ : Matrix (Fin a) (Fin c) (EAf D)}
    (hN : IsIntM N) (hκ : IsIntM κ) : IsIntM (N * κ) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hN i l) (hκ l j)

private theorem frame_ratio_int {n : ℕ} {β β' : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Formalism.L2.DIV.IsFrame β Λ) (h' : Formalism.L2.DIV.IsFrame β' Λ) : IsIntM ((β'⁻¹).val * β.val) := fun i j => by
  have hv : (fun k => β.val k j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    refine (h _).2 fun i' => ?_
    have e1 : (β⁻¹).val.mulVec (fun k => β.val k j) i' =
        ((β⁻¹).val * β.val) i' j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [e1, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have := (h' _).1 hv i
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this

private theorem inId_mul {b a c : ℕ} {I : Ideal (𝓞 D.host.E)} {N : Matrix (Fin b) (Fin a) (EAf D)}
    {κ : Matrix (Fin a) (Fin c) (EAf D)} (hκ : IsIntM κ) (i : Fin b) (hN : ∀ l, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i l))
    (j : Fin c) : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((N * κ) i j) := by
  have hm : (N * κ) i j ∈ OO := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => mul_mem (hN l).1 (hκ l j)
  refine ⟨hm, ?_⟩
  have e : (⟨(N * κ) i j, hm⟩ : OO) = ∑ l, (⟨N i l, (hN l).1⟩ : OO) * ⟨κ l j, hκ l j⟩ := Subtype.ext (by
    show (N * κ) i j = _
    rw [Matrix.mul_apply]
    push_cast
    rfl)
  rw [e]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hN l).2

private theorem topL_mul {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (κ : Matrix (Fin a) (Fin a) (EAf D)) :
    topL a (N * κ) = topL a N * κ := by
  ext i j
  simp only [topL, Matrix.mul_apply]
  by_cases hi : i.1 < b
  · simp [hi]
  · simp [hi]

end GlobalTheory.frameChangeUnitDeterminant

namespace GlobalTheory.frameChangeUnitDeterminant

open Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem det_int {k : ℕ} {N : Matrix (Fin k) (Fin k) (EAf D)} (hN : IsIntM N) : N.det ∈ OO := by
  let A : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N i j, hN i j⟩
  have eA : N.det = ((A.det : OO) : EAf D) := by
    rw [show N = (OO).subtype.mapMatrix A from rfl]
    exact (RingHom.map_det (OO).subtype A).symm
  rw [eA]
  exact A.det.2

private theorem isUnitDet_unique {e : AE D} {k : ℕ} {N : Matrix (Fin k) (Fin k) (EAf D)} {x x' : (AE D)ˣ}
    (h : IsUnitDet e N x) (h' : IsUnitDet e N x') : x = x' :=
  Units.ext (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.eq_of_parts (h.1.trans h'.1.symm) (h.2.1.trans h'.2.1.symm))

private theorem idem_mul {R : Type} [CommRing R] {ε a b : R} (hε : ε * ε = ε) :
    (1 - ε + ε * a) * (1 - ε + ε * b) = 1 - ε + ε * (a * b) := by
  linear_combination (a * b - a - b + 1) * hε

private theorem succ_mul_succ_sub_one_div_succ {R : Type} [CommRing R] {ε z y yi a b : R} (hε : ε * ε = ε) (hz : z = 1 - ε + ε * (a * b))
    (hy : y = 1 - ε + ε * b) (hyy : y * yi = 1) : z * yi = 1 - ε + ε * a := by
  subst hz hy
  linear_combination (1 - ε + ε * a) * hyy - (a * b - a - b + 1) * yi * hε

private theorem isUnitDet_mul {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {L κ : Matrix (Fin k) (Fin k) (EAf D)} {x y : (AE D)ˣ} (hx : IsUnitDet e L x) (hy : IsUnitDet e κ y) :
    IsUnitDet e (L * κ) (x * y) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hx.1, hy.1, mul_one]
  · rw [Units.val_mul, map_mul, hx.2.1, hy.2.1, Matrix.det_mul, idem_mul hε]
  · rw [_root_.mul_inv_rev, Units.val_mul, map_mul]
    exact mul_mem hy.2.2 hx.2.2

set_option maxHeartbeats 1000000 in
private theorem isUnitDet_div {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {L κ : Matrix (Fin k) (Fin k) (EAf D)} (hκ : IsIntM κ) {z y : (AE D)ˣ} (hz : IsUnitDet e (L * κ) z)
    (hy : IsUnitDet e κ y) : IsUnitDet e L (z * y⁻¹) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hyy : toEAf D (y : AE D) * toEAf D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hinv : infPart D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (infPart D) (Units.mul_inv y)
    rwa [map_mul, hy.1, one_mul, map_one] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hz.1, hinv, mul_one]
  · rw [Units.val_mul, map_mul]
    exact succ_mul_succ_sub_one_div_succ hε (hz.2.1.trans (by rw [Matrix.det_mul])) hy.2.1 hyy
  · have e0 : (z * y⁻¹)⁻¹ = y * z⁻¹ := by rw [_root_.mul_inv_rev, inv_inv]
    rw [e0]
    rw [Units.val_mul]
    rw [map_mul]
    refine mul_mem ?_ hz.2.2
    rw [hy.2.1]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE (det_int hκ))

private theorem unitChar_mul (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S)
    {k : ℕ} (L κ : Matrix (Fin k) (Fin k) (EAf D)) (hκ : IsIntM κ) {y : (AE D)ˣ} (hy : IsUnitDet e κ y) :
    unitChar ν e (L * κ) = (((ν y)⁻¹ : Circle) : ℂ) * unitChar ν e L := by
  unfold unitChar
  by_cases hL : ∃ x, IsUnitDet e L x
  · have hLκ : ∃ x, IsUnitDet e (L * κ) x := ⟨_, isUnitDet_mul he hL.choose_spec hy⟩
    rw [dif_pos hL, dif_pos hLκ, isUnitDet_unique hLκ.choose_spec (isUnitDet_mul he hL.choose_spec hy), map_mul,
      _root_.mul_inv_rev, Circle.coe_mul]
  · have hLκ : ¬ ∃ x, IsUnitDet e (L * κ) x := fun ⟨z, hz⟩ => hL ⟨_, isUnitDet_div he hκ hz hy⟩
    rw [dif_neg hL, dif_neg hLκ, mul_zero]

end GlobalTheory.frameChangeUnitDeterminant

namespace GlobalTheory.frameChangeUnitDeterminant

open Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem half_mul {e : AE D} {m m' n : ℕ} (P : Matrix (Fin m) (Fin m') (AE D)) {y : Mx D m' n} (h : IsHalf e y) :
    IsHalf e (P * y : Mx D m n) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, h l j]

private theorem pull_eq (A WW : HSp D) (k : GA D WW) (y : WO A WW) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 k y =
      HMul.hMul (mt WW k⁻¹) (y : Matrix (Fin WW.rank) (Fin A.rank) (AE D)) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt
  rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one]

private theorem exists_unitDet {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {κ κ' : Matrix (Fin k) (Fin k) (EAf D)} (hκ : IsIntM κ) (hκ' : IsIntM κ') (hkk : κ * κ' = 1) :
    ∃ x, IsUnitDet e κ x ∧ Formalism.L2.Pj.FinUnit x := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hu : (1 - toEAf D e + toEAf D e * κ.det) * (1 - toEAf D e + toEAf D e * κ'.det) = 1 := by
    rw [idem_mul hε, ← Matrix.det_mul, hkk, Matrix.det_one, mul_one, sub_add_cancel]
  obtain ⟨x, a, b, c⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_unit hu
  have m1 : 1 - toEAf D e + toEAf D e * κ.det ∈ OO := add_mem (sub_mem (one_mem _) hE) (mul_mem hE (det_int hκ))
  have m2 : 1 - toEAf D e + toEAf D e * κ'.det ∈ OO := add_mem (sub_mem (one_mem _) hE) (mul_mem hE (det_int hκ'))
  exact ⟨x, ⟨a, b, c ▸ m2⟩, a, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (b ▸ m1),
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (c ▸ m2)⟩

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in

private theorem smul_inv_eq {n : ℕ} {ε : EAf D} {g B : GL (Fin n) (EAf D)} (h : ε • g.val = ε • B.val) :
    ε • (g⁻¹).val = ε • (B⁻¹).val := by
  calc ε • (g⁻¹).val = (g⁻¹).val * (ε • B.val) * (B⁻¹).val := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    _ = (g⁻¹).val * (ε • g.val) * (B⁻¹).val := by rw [h]
    _ = ε • (B⁻¹).val := by rw [Matrix.mul_smul, Units.inv_mul, Matrix.smul_mul, Matrix.one_mul]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 2000000 in

private theorem frMapO_change {e : AE D} (A WW : HSp D) (βA βA' : GL (Fin A.rank) (EAf D)) (βW βW' : GL (Fin WW.rank) (EAf D))
    (k : GA D WW) (hk : ∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j)
    {y : WO A WW} (hh : IsHalf e y) :
    frMapO A WW βA βW (HMul.hMul (mt WW k⁻¹) (y : Matrix (Fin WW.rank) (Fin A.rank) (AE D))) =
      HMul.hMul (frMapO A WW βA' βW' y) (HMul.hMul (βA'⁻¹).val βA.val : Matrix (Fin A.rank) (Fin A.rank) (EAf D)) := by
  have hy : toEAf D e • y.map (toEAf D) = y.map (toEAf D) := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, ← map_mul, hh i j]
  have hK : toEAf D e • (Formalism.IndefR.Lev.finE WW k).val = toEAf D e • (βW' * βW⁻¹).val := by
    ext i j
    exact hk i j
  have hKi := smul_inv_eq hK
  have hm : (mt WW k⁻¹).map (toEAf D) = ((Formalism.IndefR.Lev.finE WW k)⁻¹).val := by
    rw [← map_inv]
    rfl
  have hB : ((βW' * βW⁻¹)⁻¹ : GL (Fin WW.rank) (EAf D)) = βW * βW'⁻¹ := by rw [_root_.mul_inv_rev, inv_inv]
  have key : ((Formalism.IndefR.Lev.finE WW k)⁻¹).val * y.map (toEAf D) = (βW * βW'⁻¹).val * y.map (toEAf D) := by
    rw [← hy, Matrix.mul_smul, ← Matrix.smul_mul, hKi, Matrix.smul_mul, ← Matrix.mul_smul, hB]
  unfold frMapO
  rw [Matrix.map_mul, hm, Matrix.mul_assoc (βW⁻¹).val, key, Units.val_mul]
  simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc _ βA'.val, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.frameChangeUnitDeterminant

namespace GlobalTheory.frameChangeUnitDeterminant

open Formalism.IndefR.Datum

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 4000000 in

private theorem stdFst_change_frames : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (I : Ideal (𝓞 D.host.E)) (A WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (βA βA' : GL (Fin A.rank) (EAf D)), Formalism.L2.DIV.IsFrame βA ΛA → Formalism.L2.DIV.IsFrame βA' ΛA →
    ∀ (βW βW' : GL (Fin WW.rank) (EAf D)) (k : GA D WW), SuppAt e WW k →
    (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j) →
    ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ ∀ y : WO A WW,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA' βW' y =
        ((ν x : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 k y) := by
  intro D ν e S he I A WW ΛA βA βA' hA hA' βW βW' k _ hk
  have hκ := frame_ratio_int hA hA'
  have hκ' := frame_ratio_int hA' hA
  have hkk : (βA'⁻¹).val * βA.val * ((βA⁻¹).val * βA'.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc βA.val, Units.mul_inv, Matrix.one_mul, Units.inv_mul]
  obtain ⟨x, hx, hxu⟩ := exists_unitDet he hκ hκ' hkk
  refine ⟨x, hxu, fun y => ?_⟩
  rw [pull_eq]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  by_cases hh : IsHalf e y
  · have hh' : IsHalf e (HMul.hMul (mt WW k⁻¹) (y : Matrix (Fin WW.rank) (Fin A.rank) (AE D)) : Mx D WW.rank A.rank) :=
      half_mul _ hh
    rw [frMapO_change A WW βA βA' βW βW' k hk hh, topL_mul,
      unitChar_mul ν he _ _ hκ hx]
    have hI : IsIntM (frMapO A WW βA' βW' y * ((βA'⁻¹).val * βA.val)) ↔ IsIntM (frMapO A WW βA' βW' y) := by
      refine ⟨fun h => ?_, fun h => isIntM_mul h hκ⟩
      have := isIntM_mul h hκ'
      rwa [Matrix.mul_assoc, hkk, Matrix.mul_one] at this
    have hR : (∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((frMapO A WW βA' βW' y * ((βA'⁻¹).val * βA.val)) i j)) ↔
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA' βW' y i j) := by
      refine ⟨fun h i j hi => ?_, fun h i j hi => inId_mul hκ i (fun l => h i l hi) j⟩
      have := inId_mul hκ' i (fun l => h i l hi) j
      rwa [Matrix.mul_assoc, hkk, Matrix.mul_one] at this
    by_cases hc : IsIntM (frMapO A WW βA' βW' y) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA' βW' y i j)
    · rw [if_pos ⟨hh, hc⟩, if_pos ⟨hh', hI.2 hc.1, hR.2 hc.2⟩, ← mul_assoc, ← Circle.coe_mul, mul_inv_cancel,
        Circle.coe_one, one_mul]
    · rw [if_neg fun h => hc h.2, if_neg fun h => hc ⟨hI.1 h.2.1, hR.1 h.2.2⟩, mul_zero]
  · have hh' : ¬ IsHalf e (HMul.hMul (mt WW k⁻¹) (y : Matrix (Fin WW.rank) (Fin A.rank) (AE D)) : Mx D WW.rank A.rank) :=
      fun h => hh (by
        have := half_mul (mt WW k) h
        rwa [← Matrix.mul_assoc, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one,
          Matrix.one_mul] at this)
    rw [if_neg fun h => hh h.1, if_neg fun h => hh' h.1, mul_zero]

end GlobalTheory.frameChangeUnitDeterminant

end

theorem _root_.GlobalTheory.T.standardThetaPair_first_frameChange_unitTranslate : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (I : Ideal (𝓞 D.host.E)) (A WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (βA βA' : GL (Fin A.rank) (EAf D)), Formalism.L2.DIV.IsFrame βA ΛA → Formalism.L2.DIV.IsFrame βA' ΛA →
    ∀ (βW βW' : GL (Fin WW.rank) (EAf D)) (k : GA D WW), SuppAt e WW k →
    (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j) →
    ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ ∀ y : WO A WW,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA' βW' y =
        ((ν x : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 k y) :=
  GlobalTheory.frameChangeUnitDeterminant.stdFst_change_frames
