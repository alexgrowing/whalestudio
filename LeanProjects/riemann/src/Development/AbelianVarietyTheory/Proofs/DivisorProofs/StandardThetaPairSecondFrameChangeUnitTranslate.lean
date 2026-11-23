import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointSupportedOfConjHalf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SndFrames

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem smul_mul_eq_of {n m p : Type} [Fintype m] {R : Type} [CommRing R] (c : R) (M : Matrix n m R)
    (N N' : Matrix m p R) (hM : c • M = M) (h : ∀ i j, c * N i j = c * N' i j) : M * N = M * N' := by
  have hN : c • N = c • N' := by
    ext i j
    simpa [Matrix.smul_apply, smul_eq_mul] using h i j
  calc M * N = (c • M) * N := by rw [hM]
    _ = M * (c • N) := by rw [Matrix.smul_mul, Matrix.mul_smul]
    _ = M * (c • N') := by rw [hN]
    _ = (c • M) * N' := by rw [Matrix.smul_mul, Matrix.mul_smul]
    _ = M * N' := by rw [hM]

private theorem isHalf_mul {c : AE D} {m n : ℕ} (P : Matrix (Fin m) (Fin m) (AE D)) (u : Matrix (Fin m) (Fin n) (AE D))
    (Q : Matrix (Fin n) (Fin n) (AE D)) (h : ∀ i j, c * u i j = u i j) :
    ∀ i j, c * (HMul.hMul (HMul.hMul P u : Matrix (Fin m) (Fin n) (AE D)) Q : Matrix (Fin m) (Fin n) (AE D)) i j =
      (HMul.hMul (HMul.hMul P u : Matrix (Fin m) (Fin n) (AE D)) Q : Matrix (Fin m) (Fin n) (AE D)) i j := by
  have hu : c • u = u := by
    ext i j
    exact h i j
  have : c • (HMul.hMul (HMul.hMul P u : Matrix (Fin m) (Fin n) (AE D)) Q : Matrix (Fin m) (Fin n) (AE D)) =
      (HMul.hMul (HMul.hMul P u : Matrix (Fin m) (Fin n) (AE D)) Q : Matrix (Fin m) (Fin n) (AE D)) := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu]
  intro i j
  exact congrFun (congrFun this i) j

private theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  have := GlobalTheory.AdjAct.mt_one_inv S
  rwa [inv_one] at this

private theorem isHalf_pull (c : AE D) (S T : HSp D) (g : GA D S) (k : GA D T) (y : WO S T) (h : IsHalf c y) :
    IsHalf c (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt S T g k y) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt
  exact isHalf_mul _ _ _ h

private theorem pull_pull (S T : HSp D) (k : GA D T) (y : WO S T) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt S T 1 k⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt S T 1 k y) = y := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt
  rw [inv_inv, mt_one, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, GlobalTheory.AdjAct.mt_mul_mt_inv, Matrix.one_mul]

private theorem isHalf_pull_iff (c : AE D) (S T : HSp D) (k : GA D T) (y : WO S T) :
    IsHalf c (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt S T 1 k y) ↔ IsHalf c y := by
  constructor
  · intro h
    have := isHalf_pull c S T 1 k⁻¹ _ h
    rwa [pull_pull] at this
  · exact isHalf_pull c S T 1 k y

private theorem isIntM_frames {n : ℕ} {β β' : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Formalism.L2.DIV.IsFrame β Λ) (h' : Formalism.L2.DIV.IsFrame β' Λ) : IsIntM ((β⁻¹ * β').1) := by
  intro i j
  have hx := (h' (β'.1.mulVec (Pi.single j 1))).2 (fun l => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  have := (h _).1 hx i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at this
  exact this

private theorem isIntM_mul {m n p : ℕ} {K : Matrix (Fin m) (Fin n) (EAf D)} {Z : Matrix (Fin n) (Fin p) (EAf D)}
    (hK : IsIntM K) (hZ : IsIntM Z) : IsIntM (K * Z) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hK i l) (hZ l j)

private theorem inId_mul {I : Ideal (𝓞 D.host.E)} {m n p : ℕ} {K : Matrix (Fin m) (Fin n) (EAf D)}
    {Z : Matrix (Fin n) (Fin p) (EAf D)} (hK : IsIntM K) {j : Fin p} (hZ : ∀ l, InId I (Z l j)) (i : Fin m) :
    InId I ((K * Z) i j) := by
  have hmem : ∀ l, Z l j ∈ OO := fun l => (hZ l).1
  have hs : (K * Z) i j ∈ OO := by
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (hK i l) (hmem l)
  refine ⟨hs, ?_⟩
  have e1 : (⟨(K * Z) i j, hs⟩ : OO) = ∑ l, (⟨K i l, hK i l⟩ : OO) * ⟨Z l j, hmem l⟩ :=
    Subtype.ext (by simp [Matrix.mul_apply])
  rw [e1]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hZ l).2

private theorem rightBlock_mul {m d : ℕ} (a : ℕ) (K : Matrix (Fin m) (Fin m) (EAf D)) (Z : Matrix (Fin m) (Fin d) (EAf D)) :
    rightBlock a (K * Z) = K * rightBlock a Z := by
  ext i j
  simp only [rightBlock, Matrix.mul_apply]
  split_ifs <;> simp

private theorem idem_mul {R : Type} [CommRing R] {E a b : R} (hE : E * E = E) :
    (1 - E + E * a) * (1 - E + E * b) = 1 - E + E * (a * b) := by
  linear_combination (1 - a - b + a * b) * hE

private theorem det_mem {k : ℕ} {N : Matrix (Fin k) (Fin k) (EAf D)} (h : IsIntM N) : N.det ∈ OO := by
  let A : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N i j, h i j⟩
  have : N = (OO).subtype.mapMatrix A := rfl
  rw [this, ← RingHom.map_det]
  exact (A.det).2

private theorem exists_unitFactor {e : AE D} (hE : toEAf D e * toEAf D e = toEAf D e) {k : ℕ} (κ : GL (Fin k) (EAf D)) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = 1 - toEAf D e + toEAf D e * κ.1.det ∧
      toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - toEAf D e + toEAf D e * (κ⁻¹).1.det := by
  apply StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_unit
  have hd : κ.1.det * (κ⁻¹).1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [idem_mul hE, hd, mul_one, sub_add_cancel]

set_option maxHeartbeats 1000000 in

private theorem unitChar_mul (ν : (AE D)ˣ →* Circle) {e : AE D} (hE : toEAf D e * toEAf D e = toEAf D e) {k : ℕ}
    (κ : GL (Fin k) (EAf D)) (x : (AE D)ˣ) (h1 : infPart D (x : AE D) = 1)
    (h2 : toEAf D (x : AE D) = 1 - toEAf D e + toEAf D e * κ.1.det)
    (h3 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - toEAf D e + toEAf D e * (κ⁻¹).1.det)
    (hxI : toEAf D (x : AE D) ∈ OO) (hxI' : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ OO)
    (R : Matrix (Fin k) (Fin k) (EAf D)) :
    unitChar ν e R = ((ν x : Circle) : ℂ) * unitChar ν e (κ.1 * R) := by
  have uniq : ∀ {N : Matrix (Fin k) (Fin k) (EAf D)} {u u' : (AE D)ˣ}, IsUnitDet e N u → IsUnitDet e N u' → u = u' :=
    fun hu hu' => Units.ext (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.eq_of_parts (hu.1.trans hu'.1.symm) (hu.2.1.trans hu'.2.1.symm))
  have hd : κ.1.det * (κ⁻¹).1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have fwd : ∀ u, IsUnitDet e R u → IsUnitDet e (κ.1 * R) (u * x) := by
    rintro u ⟨a1, a2, a3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul, map_mul, a1, h1, one_mul]
    · rw [Units.val_mul, map_mul, a2, h2, Matrix.det_mul]
      rw [idem_mul hE, mul_comm R.det]
    · rw [mul_inv_rev, Units.val_mul, map_mul]
      exact mul_mem hxI' a3
  have hinf : infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (infPart D) (Units.mul_inv x)
    rw [map_mul, h1, one_mul, map_one] at this
    exact this
  have bwd : ∀ u, IsUnitDet e (κ.1 * R) u → IsUnitDet e R (u * x⁻¹) := by
    rintro u ⟨a1, a2, a3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul, map_mul, a1, hinf, one_mul]
    · rw [Units.val_mul, map_mul, a2, h3, Matrix.det_mul]
      rw [idem_mul hE, mul_comm κ.1.det R.det, mul_assoc, hd, mul_one]
    · rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul]
      exact mul_mem hxI a3
  unfold unitChar
  by_cases hR : ∃ u, IsUnitDet e R u
  · have hK : ∃ u, IsUnitDet e (κ.1 * R) u := ⟨_, fwd _ hR.choose_spec⟩
    rw [dif_pos hR, dif_pos hK, uniq hK.choose_spec (fwd _ hR.choose_spec), ← Circle.coe_mul]
    congr 1
    rw [map_mul, mul_inv_rev, mul_inv_cancel_left]
  · have hK : ¬ ∃ u, IsUnitDet e (κ.1 * R) u := fun ⟨u, hu⟩ => hR ⟨_, bwd u hu⟩
    rw [dif_neg hR, dif_neg hK, mul_zero]

private theorem frMapAdj_pull (A' WW : HSp D) (βA βA' : GL (Fin A'.rank) (EAf D)) (βW βW' : GL (Fin WW.rank) (EAf D))
    (k : GA D WW) {e : AE D} (he : e * e = e)
    (hk : ∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j)
    (y : WO A' WW) (hy : IsHalf (cA D e) y) :
    frMapAdj A' WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 k y) = HMul.hMul (βA⁻¹ * βA').1 (frMapAdj A' WW βA' βW' y) := by
  have hfr : ∀ (βS : GL (Fin A'.rank) (EAf D)) (βT : GL (Fin WW.rank) (EAf D)),
      frMapAdj A' WW βS βT y = HMul.hMul (HMul.hMul (βS⁻¹).1 (frMapAdj A' WW 1 1 y)) βT.1 := by
    intro βS βT
    simp only [frMapAdj, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  have hM : toEAf D e • frMapAdj A' WW 1 1 y = frMapAdj A' WW 1 1 y := by
    ext i j
    exact GlobalTheory.HalfSupp.frMapAdj_supp A' WW 1 1 e y he hy i j
  have hinv : (βW⁻¹ * Formalism.IndefR.Lev.finE WW k⁻¹ * βW)⁻¹ = βW⁻¹ * Formalism.IndefR.Lev.finE WW k * βW := by
    rw [map_inv]
    group
  have key := smul_mul_eq_of _ _ _ _ hM hk
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt_eq_actO, inv_one, GlobalTheory.AdjAct.frMapAdj_actO, hinv, hfr βA βW, hfr βA' βW']
  simp only [Units.val_mul] at key ⊢
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rw [← Matrix.mul_assoc (frMapAdj A' WW 1 1 y), key]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc βA'.val (βA'⁻¹).val, Units.mul_inv, Matrix.one_mul]

set_option maxHeartbeats 1000000 in

private theorem stdSnd_frames : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (βA βA' : GL (Fin A'.rank) (EAf D)), Formalism.L2.DIV.IsFrame βA ΛA → Formalism.L2.DIV.IsFrame βA' ΛA →
    ∀ (βW βW' : GL (Fin WW.rank) (EAf D)) (k : GA D WW), SuppAt e WW k →
    (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j) →
    ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ ∀ y : WO A' WW,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA' βW' y =
        ((ν x : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 k y) := by
  intro D ν e S he I a A' WW ΛA βA βA' hβA hβA' βW βW' k _ hk
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hEi := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hE : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, hee]
  have hκ : IsIntM (βA⁻¹ * βA').1 := isIntM_frames hβA hβA'
  have hκ' : IsIntM ((βA⁻¹ * βA')⁻¹).1 := by
    rw [mul_inv_rev, inv_inv]
    exact isIntM_frames hβA' hβA
  obtain ⟨x, h1, h2, h3⟩ := exists_unitFactor hE (βA⁻¹ * βA')
  have hxI : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [h2]
    exact add_mem (sub_mem (one_mem _) hEi) (mul_mem hEi (det_mem hκ))
  have hxI' : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [h3]
    exact add_mem (sub_mem (one_mem _) hEi) (mul_mem hEi (det_mem hκ'))
  refine ⟨x, ⟨h1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hxI, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hxI'⟩, fun y => ?_⟩
  have hh := isHalf_pull_iff (cA D e) A' WW k y
  unfold stdSnd
  by_cases hy : IsHalf (cA D e) y
  · have hZ : dualCoord A' WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 k y) =
        HMul.hMul (βA⁻¹ * βA').1 (dualCoord A' WW βA' βW' y) := by
      unfold dualCoord
      rw [frMapAdj_pull A' WW βA βA' βW βW' k hee hk y hy]
      ext i j
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _
    rw [hZ]
    have hZZ : ∀ Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D),
        HMul.hMul ((βA⁻¹ * βA')⁻¹).1 (HMul.hMul (βA⁻¹ * βA').1 Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)) = Z := fun Z => by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have hint : ∀ Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D), IsIntM (HMul.hMul (βA⁻¹ * βA').1 Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)) ↔ IsIntM Z :=
      fun Z => ⟨fun h => hZZ Z ▸ isIntM_mul hκ' h, fun h => isIntM_mul hκ h⟩
    have hid : ∀ Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D),
        (∀ i j, j.1 < a → InId I ((HMul.hMul (βA⁻¹ * βA').1 Z : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)) i j)) ↔ ∀ i j, j.1 < a → InId I (Z i j) :=
      fun Z => ⟨fun H i j hj => hZZ Z ▸ inId_mul hκ' (fun l => H l j hj) i,
        fun H i j hj => inId_mul hκ (fun l => H l j hj) i⟩
    by_cases hc : IsIntM (dualCoord A' WW βA' βW' y) ∧
        ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW' y i j)
    · rw [if_pos ⟨hy, hc⟩, if_pos ⟨hh.2 hy, (hint _).2 hc.1, (hid _).2 hc.2⟩, rightBlock_mul]
      exact unitChar_mul ν hE (βA⁻¹ * βA') x h1 h2 h3 hxI hxI' _
    · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc ⟨(hint _).1 h.2.1, (hid _).1 h.2.2⟩), mul_zero]
  · rw [if_neg (fun h => hy h.1), if_neg (fun h => hy (hh.1 h.1)), mul_zero]

end GlobalTheory.SndFrames

end

theorem _root_.GlobalTheory.T.standardThetaPair_second_frameChange_unitTranslate : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (βA βA' : GL (Fin A'.rank) (EAf D)), Formalism.L2.DIV.IsFrame βA ΛA → Formalism.L2.DIV.IsFrame βA' ΛA →
    ∀ (βW βW' : GL (Fin WW.rank) (EAf D)) (k : GA D WW), SuppAt e WW k →
    (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE WW k).1 i j = toEAf D e * (βW' * βW⁻¹).1 i j) →
    ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ ∀ y : WO A' WW,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA' βW' y =
        ((ν x : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a A' WW βA βW (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 k y) :=
  @GlobalTheory.SndFrames.stdSnd_frames
