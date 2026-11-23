import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.BotSmallDict.Supp

section Abstract
variable {R : Type} [CommRing R] {σ : R →+* R}

private theorem cT_mul {l m n : Type} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_add {m n : Type} (A B : Matrix m n R) : Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B :=
  Matrix.ext fun _ _ => map_add σ _ _

private theorem cT_smul {m n : Type} (c : R) (A : Matrix m n R) : Formalism.UG.cT σ (c • A) = σ c • Formalism.UG.cT σ A :=
  Matrix.ext fun _ _ => map_mul σ _ _

private theorem cT_one {n : Type} [DecidableEq n] : Formalism.UG.cT σ (1 : Matrix n n R) = 1 := by
  unfold Formalism.UG.cT
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

private theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {m n : Type} (A : Matrix m n R) : Formalism.UG.cT σ (Formalism.UG.cT σ A) = A :=
  Matrix.ext fun _ _ => hσ _

private theorem exists_unitary (hσ : ∀ x, σ (σ x) = x) (O : Subring R) (hO : ∀ x ∈ O, σ x ∈ O) {n : Type} [Fintype n] [DecidableEq n]
    {ε : R} (hε : ε ∈ O) (hee : ε * ε = ε) (h0 : ε * σ ε = 0) {M B : Matrix n n R} (hM : ∀ i j, M i j ∈ O)
    (hB : ∀ i j, B i j ∈ O) (eM : ε • M = M) (eB : ε • B = B) (hBM : B * M = ε • (1 : Matrix n n R)) :
    ∃ k : Matrix n n R, (∀ i j, k i j ∈ O) ∧ Formalism.UG.cT σ k * k = 1 ∧ Formalism.UG.cT σ M * k = σ ε • (1 : Matrix n n R) := by
  have hss : σ ε * σ ε = σ ε := by rw [← map_mul, hee]
  obtain ⟨f, hf⟩ : ∃ f, f = 1 - ε - σ ε := ⟨_, rfl⟩
  have hσf : σ f = f := by rw [hf, map_sub, map_sub, map_one, hσ]; ring
  have fe : f * ε = 0 := by rw [hf]; linear_combination -hee - h0
  have fs : f * σ ε = 0 := by rw [hf]; linear_combination -hss - h0
  have ff : f * f = f := by rw [hf] at fe fs ⊢; linear_combination -fe - fs
  have sM : σ ε • Formalism.UG.cT σ M = Formalism.UG.cT σ M := by rw [← cT_smul, eM]
  have sB : σ ε • Formalism.UG.cT σ B = Formalism.UG.cT σ B := by rw [← cT_smul, eB]
  have fM : f • M = 0 := by rw [← eM, smul_smul, fe, zero_smul]
  have fB : f • B = 0 := by rw [← eB, smul_smul, fe, zero_smul]
  have fM' : f • Formalism.UG.cT σ M = 0 := by rw [← sM, smul_smul, fs, zero_smul]
  have fB' : f • Formalism.UG.cT σ B = 0 := by rw [← sB, smul_smul, fs, zero_smul]
  have BB : B * Formalism.UG.cT σ B = 0 := by
    rw [← sB, Matrix.mul_smul, ← Matrix.smul_mul, ← eB, smul_smul, mul_comm, h0, zero_smul, Matrix.zero_mul]
  have MM : Formalism.UG.cT σ M * M = 0 := by
    rw [← sM, Matrix.smul_mul, ← Matrix.mul_smul]
    conv_lhs => enter [2]; rw [← eM, smul_smul, mul_comm, h0, zero_smul]
    rw [Matrix.mul_zero]
  have MB : Formalism.UG.cT σ M * Formalism.UG.cT σ B = σ ε • (1 : Matrix n n R) := by rw [← cT_mul, hBM, cT_smul, cT_one]
  have h3 : Formalism.UG.cT σ M * (f • (1 : Matrix n n R) + Formalism.UG.cT σ B + M) = σ ε • (1 : Matrix n n R) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, fM', MB, MM, zero_add, add_zero]
  refine ⟨f • (1 : Matrix n n R) + Formalism.UG.cT σ B + M, fun i j => ?_, ?_, h3⟩
  · refine add_mem (add_mem (mul_mem ?_ ?_) (hO _ (hB j i))) (hM i j)
    · rw [hf]
      exact sub_mem (sub_mem (one_mem _) hε) (hO _ hε)
    · rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · rw [cT_add, cT_add, cT_smul, cT_one, cT_cT hσ, hσf, Matrix.add_mul, h3, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
      smul_add, smul_add, fB', fM, smul_smul, ff, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, fB, BB, hBM,
      add_zero, add_zero, add_zero, zero_add, ← add_smul, ← add_smul, hf, show 1 - ε - σ ε + ε + σ ε = 1 by ring, one_smul]

private theorem adjugate_mem (O : Subring R) {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n R} (hY : ∀ i j, Y i j ∈ O) (i j : n) :
    Y.adjugate i j ∈ O := by
  let A : Matrix n n O := fun i j => ⟨Y i j, hY i j⟩
  have h := RingHom.map_adjugate O.subtype A
  rw [show O.subtype.mapMatrix A = Y from rfl] at h
  rw [← h]
  exact (A.adjugate i j).2

private theorem mul_mem' (O : Subring R) {l m n : Type} [Fintype m] {A : Matrix l m R} {B : Matrix m n R} (hA : ∀ i j, A i j ∈ O)
    (hB : ∀ i j, B i j ∈ O) (i : l) (j : n) : (A * B) i j ∈ O := by
  rw [Matrix.mul_apply]
  exact sum_mem fun a _ => mul_mem (hA i a) (hB a j)

private theorem exists_inv (O : Subring R) {n : Type} [Fintype n] [DecidableEq n] {ε ξ η t' : R} (hee : ε * ε = ε) (hξ : ε * ξ ∈ O)
    (hξη : ξ * η = 1) {β β' Y : Matrix n n R} (hβ : β' * β = 1) (hβ' : ∀ i j, β' i j ∈ O) (hY : ∀ i j, Y i j ∈ O)
    (ht : (1 - ε + ε * Y.det) * t' = 1) (ht' : t' ∈ O) :
    ∃ B : Matrix n n R, (∀ i j, B i j ∈ O) ∧ ε • B = B ∧ B * (η • (β * Y)) = ε • (1 : Matrix n n R) := by
  refine ⟨(ε * ξ * t') • (Y.adjugate * β'), fun i j => mul_mem (mul_mem hξ ht') (mul_mem' O (adjugate_mem O hY) hβ' i j), ?_, ?_⟩
  · rw [smul_smul, ← mul_assoc, ← mul_assoc, hee]
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc β', hβ, Matrix.one_mul, Matrix.adjugate_mul,
      smul_smul, smul_smul]
    congr 1
    linear_combination ε * ht + (ε * t' * Y.det) * hξη + (t' - t' * Y.det) * hee

private theorem core (hσ : ∀ x, σ (σ x) = x) (O : Subring R) (hO : ∀ x ∈ O, σ x ∈ O) {m n : Type} [Fintype n] [DecidableEq n] (r : n → m)
    {ε ξ η t' : R} (hε : ε ∈ O) (hee : ε * ε = ε) (h0 : ε * σ ε = 0) (hξ : ε * ξ ∈ O) (hη : η ∈ O) (hξη : ξ * η = 1)
    (β : GL n R) (hβi : ∀ i j, β.1 i j ∈ O ∧ (β⁻¹).1 i j ∈ O) {y : Matrix m n R} {Y : Matrix n m R}
    (hYe : Y = ξ • ((β⁻¹).1 * Formalism.UG.cT σ y)) (hY : ∀ i j, Y i j ∈ O) (hh : ∀ i j, σ ε * y i j = y i j)
    (ht : (1 - ε + ε * (Y.submatrix id r).det) * t' = 1) (ht' : t' ∈ O) :
    (∀ i l, y i l = σ (η * ∑ a, β.1 l a * Y a i)) ∧ ∃ k : Matrix n n R, (∀ i j, k i j ∈ O) ∧ Formalism.UG.cT σ k * k = 1 ∧
      ∀ i j, ∑ l, y (r i) l * k l j = if i = j then σ ε else 0 := by
  have hM : Formalism.UG.cT σ y = η • (β.1 * Y) := by
    rw [hYe, Matrix.mul_smul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, smul_smul, mul_comm η, hξη, one_smul]
  refine ⟨fun i l => (hσ _).symm.trans (congrArg σ (congrFun (congrFun hM l) i)), ?_⟩
  obtain ⟨B, hB, eB, hBM⟩ := exists_inv O hee hξ hξη β.inv_mul (fun i j => (hβi i j).2)
    (Y := Y.submatrix id r) (fun i j => hY i (r j)) ht ht'
  have hM2 : η • (β.1 * Y.submatrix id r) = Formalism.UG.cT σ (y.submatrix r id) :=
    Matrix.ext fun i j => (congrFun (congrFun hM i) (r j)).symm
  have hMi : ∀ i j, (η • (β.1 * Y.submatrix id r)) i j ∈ O := fun i j =>
    mul_mem hη (mul_mem' _ (fun i j => (hβi i j).1) (B := Y.submatrix id r) (fun i j => hY i (r j)) i j)
  have eM : ε • (η • (β.1 * Y.submatrix id r)) = η • (β.1 * Y.submatrix id r) := by
    rw [hM2]
    conv_lhs => rw [← hσ ε, ← cT_smul]
    congr 1
    exact Matrix.ext fun i j => hh (r i) j
  obtain ⟨k, hk, hku, hMk⟩ := exists_unitary hσ O hO hε hee h0 hMi hB eM eB hBM
  rw [hM2, cT_cT hσ] at hMk
  refine ⟨k, hk, hku, fun i j => (congrFun (congrFun hMk i) j).trans ?_⟩
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

end Abstract

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E
local notation "σσ" => GlobalTheory.AdelicLatMove.cF D

private def toE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* EAf D :=
  (GlobalTheory.BotFormula.toAfE D).trans (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

private theorem toE_int (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : toE D y ∈ OO ↔ y ∈ OhE D := GlobalTheory.BotClassDict.toAfE_int_iff y

private theorem comm_sigR (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (sigR (Af D.host.F) D.sp.cm.sig z) =
      σσ (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x a => rfl

private theorem toE_sgA (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : toE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = σσ (toE D y) := by
  change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (GlobalTheory.BotFormula.toAfE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y)) = _
  rw [GlobalTheory.BotFormula.toAfE_sgA, comm_sigR]
  rfl

private theorem toE_finStd (V : HSp D) (hG : V.gram = 1) (g : Formalism.L2.Theta.GA D V) (i j : Fin V.rank) :
    toE D ((GlobalTheory.BotClassDict.finStd V hG g).1.1 i j) = toEAf D (Formalism.L2.Theta.mt V g i j) := by
  change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (GlobalTheory.BotFormula.toAfE D _) = _
  rw [GlobalTheory.BotClassDict.toAfE_finStd]
  rfl

private theorem cF_cF (z : EAf D) : σσ (σσ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x a => rw [GlobalTheory.AdelicLatMove.cF_tmul, GlobalTheory.AdelicLatMove.cF_tmul, star_star]

private theorem cF_oToS (b : 𝓞 D.host.E) :
    σσ (Formalism.L2.DIV.oToS D.host.F D.host.E b : EAf D) = (Formalism.L2.DIV.oToS D.host.F D.host.E (D.host.conj • b) : EAf D) := by
  change (D.sp.cm.sig (b : D.host.E)) ⊗ₜ[D.host.F] (1 : Af D.host.F) = (D.host.conj (b : D.host.E)) ⊗ₜ[D.host.F] (1 : Af D.host.F)
  rw [Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj]

private theorem cF_mem (z : EAf D) (hz : z ∈ OO) : σσ z ∈ OO := by
  induction hz using Subring.closure_induction with
  | mem r hr =>
    rcases hr with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
    · have := (Formalism.L2.DIV.oToS D.host.F D.host.E (D.host.conj • b)).2
      rw [← cF_oToS] at this
      exact this
    · have h : σσ ((1 : D.host.E) ⊗ₜ[D.host.F] β) = (1 : D.host.E) ⊗ₜ[D.host.F] β := by
        rw [GlobalTheory.AdelicLatMove.cF_tmul, star_one]
      have h2 : (1 : D.host.E) ⊗ₜ[D.host.F] β ∈ OO := Subring.subset_closure (Or.inr ⟨⟨β, hβ⟩, rfl⟩)
      rw [← h] at h2
      exact h2
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

private theorem inId_cF {I : Ideal (𝓞 D.host.E)} {z : EAf D} (hz : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I z) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • I) (σσ z) := by
  obtain ⟨h, hz⟩ := hz
  let c : OO →+* OO := ((σσ).comp (OO).subtype).codRestrict OO fun x => cF_mem _ x.2
  have hle : Formalism.L2.DIV.idS D.host.F I ≤ (Formalism.L2.DIV.idS D.host.F (D.host.conj • I)).comap c := by
    refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
    have e : c (Formalism.L2.DIV.oToS D.host.F D.host.E b) = Formalism.L2.DIV.oToS D.host.F D.host.E (D.host.conj • b) :=
      Subtype.ext (cF_oToS b)
    rw [Ideal.mem_comap, Ideal.mem_comap, e]
    exact Ideal.mem_map_of_mem _ (Ideal.smul_mem_pointwise_smul _ _ _ hb)
  exact ⟨cF_mem _ h, hle hz⟩

private theorem inId_zero (I : Ideal (𝓞 D.host.E)) : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (0 : EAf D) := ⟨zero_mem _, zero_mem _⟩

private theorem inId_add {I : Ideal (𝓞 D.host.E)} {a b : EAf D} (ha : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I a) (hb : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I b) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (a + b) := ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩

private theorem inId_mul {I : Ideal (𝓞 D.host.E)} {a b : EAf D} (ha : a ∈ OO) (hb : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I b) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (a * b) := ⟨mul_mem ha hb.1, Ideal.mul_mem_left _ (⟨a, ha⟩ : OO) hb.2⟩

private theorem inId_sum {I : Ideal (𝓞 D.host.E)} {ι : Type} (s : Finset ι) {a : ι → EAf D}
    (ha : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (a i)) : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (∑ i ∈ s, a i) :=
  Finset.sum_induction _ _ (fun _ _ => inId_add) (inId_zero I) ha

private def sqI (D : D7) : 𝓞 D.host.E := ⟨D.host.sqrtMinusD, Formalism.L2.Pj.sqrtMinusD_isIntegral D⟩

private theorem xi0_mul_neg_sqI_eq_one_of_ccK_eq (hc : D.host.ccK = ⊤) : D.host.xi0 * ((-sqI D : 𝓞 D.host.E) : D.host.E) = 1 := by
  have h := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have e : D.host.xi0 = -1 / D.host.sqrtMinusD := by
    rw [Formalism.BasicNotions.Host.xi0, hc, Ideal.absNorm_top, Nat.cast_one, one_mul]
  have h0 : D.host.sqrtMinusD ≠ 0 := fun h0 => h (by rw [e, h0, div_zero])
  change D.host.xi0 * (-D.host.sqrtMinusD) = 1
  rw [e]
  field_simp

private theorem idempotent_mul_xi0_integral (hc : D.host.ccK = ⊤) {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) :
    toEAf D e * eToEAf D D.host.xi0 ∈ OO := by
  obtain ⟨⟨⟨es, hes, hs⟩, -⟩, hP⟩ := he
  have hx := xi0_mul_neg_sqI_eq_one_of_ccK_eq hc
  have hx0 : (-sqI D : 𝓞 D.host.E) ≠ 0 := fun h => by
    rw [h] at hx
    simp at hx
  have hξ : D.host.xi0 = ((-sqI D : 𝓞 D.host.E) : D.host.E)⁻¹ := eq_inv_of_mul_eq_one_left hx
  have hsq : (-sqI D) * (-sqI D) = -((D.host.d : ℕ) : 𝓞 D.host.E) := by
    apply RingOfIntegers.coe_injective
    have := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
    rw [map_mul, map_neg, map_neg, map_natCast]
    change -D.host.sqrtMinusD * -D.host.sqrtMinusD = _
    rw [← this]
    ring
  rw [hs, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.hom_sum, Finset.sum_mul]
  refine sum_mem fun w hw => ?_
  have hn : (-sqI D) ∉ w.asIdeal := fun h => hP w hw (by
    have h1 : ((D.host.d : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← neg_mem_iff, ← hsq]
      exact Ideal.mul_mem_left _ _ h
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ h1)
  have hmem : finPart D (es w * incA D (((-sqI D : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hn (((hes w hw).2 _ hx0).2 h)
  have h2 := GlobalTheory.IdemRes.toEAf_mem_of_finPart hmem
  rw [RingHom.map_mul, ← hξ] at h2
  exact h2

private theorem dualCoord_eq (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (βS : GL (Fin S.rank) (EAf D)) (y : WO S T) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS 1 y =
      eToEAf D D.host.xi0 • (HMul.hMul (βS⁻¹).1 (Formalism.UG.cT σσ ((y : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D)).map (toEAf D))) :
        Matrix (Fin S.rank) (Fin T.rank) (EAf D)) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord frMapAdj
  rw [hS, hT, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul,
    Matrix.mul_one, Units.val_one, Matrix.mul_one]
  congr 2
  exact Matrix.ext fun i j => GlobalTheory.AdelicLatMove.toEAf_cA _

private theorem exists_intG {n : ℕ} {k : Matrix (Fin n) (Fin n) (EAf D)} (hk : ∀ i j, k i j ∈ OO) (hu : Formalism.UG.cT σσ k * k = 1) :
    ∃ h ∈ GlobalTheory.NormSum.intG D n, ∀ i j, toE D (h.1.1 i j) = k i j := by
  let a : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D) := k.map (toE D).symm.toRingHom
  have hs : ∀ z, (toE D).symm.toRingHom (σσ z) = Formalism.MainNotions.StandardLatticesGL3.sgA D ((toE D).symm.toRingHom z) := fun z => by
    apply (toE D).injective
    rw [toE_sgA]
    exact ((toE D).apply_symm_apply _).trans (congrArg _ ((toE D).apply_symm_apply _).symm)
  have e : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) a = (Formalism.UG.cT σσ k).map (toE D).symm.toRingHom :=
    Matrix.ext fun i j => (hs _).symm
  have ha : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) a * a = 1 := by
    rw [e, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  let u : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ⟨a, Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) a, mul_eq_one_comm.1 ha, ha⟩
  have hu' : u ∈ Formalism.MainNotions.StandardLatticesGL3.GA D n := by
    change Formalism.UG.cT _ a * _ * a = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact ha
  have hi : ∀ z ∈ OO, (toE D).symm.toRingHom z ∈ OhE D := fun z hz => by
    rw [← toE_int]
    exact ((toE D).apply_symm_apply z).symm ▸ hz
  refine ⟨⟨u, hu'⟩, (GlobalTheory.NormSum.mem_intG _).2 fun i j => ⟨hi _ (hk i j), ?_⟩, fun i j => (toE D).apply_symm_apply _⟩
  change Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) a i j ∈ _
  rw [e]
  exact hi _ (cF_mem _ (hk j i))

private theorem actO_apply (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (y : WO S T) (i : Fin T.rank) (j : Fin S.rank) :
    actO S T g⁻¹ 1 y i j = ∑ l, y i l * Formalism.L2.Theta.mt S g l j := by
  unfold actO
  rw [inv_inv, show Formalism.L2.Theta.mt T 1 = 1 from rfl, Matrix.one_mul, Matrix.mul_apply]

private theorem rightBlock_eq {κ : Type} [Zero κ] {k d o : ℕ} (ho : o + k = d) (Y : Matrix (Fin k) (Fin d) κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock o Y = Y.submatrix id fun j : Fin k => (⟨o + j.1, by omega⟩ : Fin d) :=
  Matrix.ext fun _ j => dif_pos (by omega : o + j.1 < d)

private theorem rows_of_support (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (hc : D.host.ccK = ⊤) (βS : GL (Fin S.rank) (EAf D))
    (hβ : Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank)) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) {I : Ideal (𝓞 D.host.E)} {o : ℕ} (ho : o + S.rank = T.rank)
    {y : WO S T} (hh : IsHalf (cA D e) y) (hY : IsIntM (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS 1 y))
    (hI : ∀ i j, j.1 < o → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS 1 y i j)) {x : (Formalism.L2.Theta.AE D)ˣ}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock o (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS 1 y)) x) :
    (∀ i l, i.1 < o → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • I) (toEAf D (y i l))) ∧
      ∃ k : Matrix (Fin S.rank) (Fin S.rank) (EAf D), (∀ i j, k i j ∈ OO) ∧ Formalism.UG.cT σσ k * k = 1 ∧
        ∀ (i j : Fin S.rank), ∑ l, toEAf D (y ⟨o + i.1, by omega⟩ l) * k l j = if i = j then toEAf D (cA D e) else 0 := by
  obtain ⟨-, hx, hx'⟩ := hx
  have hβi := (GlobalTheory.BotClassDict.mem_range_intGL βS).1 (GlobalTheory.BotClassDict.frame_mem_range hβ)
  have hη : eToEAf D ((-sqI D : 𝓞 D.host.E) : D.host.E) ∈ OO := (Formalism.L2.DIV.oToS D.host.F D.host.E (-sqI D)).2
  have hξη : eToEAf D D.host.xi0 * eToEAf D ((-sqI D : 𝓞 D.host.E) : D.host.E) = 1 := by
    rw [← RingHom.map_mul, xi0_mul_neg_sqI_eq_one_of_ccK_eq hc, RingHom.map_one]
  have hee : toEAf D e * toEAf D e = toEAf D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he.1]
  have hε := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he.1
  have hσε : toEAf D (cA D e) = σσ (toEAf D e) := GlobalTheory.AdelicLatMove.toEAf_cA e
  have h0 : toEAf D e * σσ (toEAf D e) = 0 := by rw [← hσε, ← RingHom.map_mul, he.1.2, RingHom.map_zero]
  have hhalf : ∀ i j, σσ (toEAf D e) * toEAf D (y i j) = toEAf D (y i j) := fun i j => by
    rw [← hσε, ← RingHom.map_mul, hh i j]
  rw [rightBlock_eq ho] at hx
  have hYe := dualCoord_eq S T hS hT βS y
  have hξ := idempotent_mul_xi0_integral hc he
  have ht0 : toEAf D x.1 * toEAf D (x⁻¹).1 = 1 := by rw [← RingHom.map_mul, x.mul_inv, RingHom.map_one]
  rw [hx] at ht0
  unfold IsIntM at hY
  generalize GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS 1 y = Y at hY hI hYe ht0
  have hc := core (σ := σσ) (y := (y : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D)).map (toEAf D)) (Y := Y)
    cF_cF OO cF_mem (fun j : Fin S.rank => (⟨o + j.1, by omega⟩ : Fin T.rank)) hε hee h0 hξ hη hξη βS hβi hYe hY hhalf ht0 hx'
  obtain ⟨h1, k, hk, hku, h2⟩ := hc
  refine ⟨fun i l hi => ?_, k, hk, hku, fun i j => ?_⟩
  · have e1 : toEAf D (y i l) = _ := h1 i l
    rw [e1]
    exact inId_cF (inId_mul hη (inId_sum _ fun m _ => inId_mul (hβi l m).1 (hI m i hi)))
  · rw [hσε]
    exact h2 i j

private theorem exists_intG_cosetFn_ne_zero : ∀ {D : D7} (S T : HSp D), S.gram = 1 → T.gram = 1 → D.host.ccK = ⊤ →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank) →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    ∀ o : ℕ, o + S.rank = T.rank →
    ∀ (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) (y : WO S T), GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e (modul P c) o S T βS 1 y ≠ 0 →
    ∃ k ∈ GlobalTheory.NormSum.intG D S.rank, ∀ g : Formalism.L2.Theta.GA D S, GlobalTheory.BotFormula.IsFinPt S g k →
      cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g⁻¹ 1 y) ≠ 0 := by
  intro D S T hS hT hc βS hβ e P c he o ho ν y hy
  obtain ⟨⟨hh, hY, hI⟩, hy⟩ := ite_ne_right_iff.1 hy
  obtain ⟨⟨x, hx⟩, -⟩ := dite_ne_right_iff.1 hy
  obtain ⟨h1, k, hk, hku, h2⟩ := rows_of_support S T hS hT hc βS hβ he ho hh hY hI hx
  obtain ⟨h, hh1, hh2⟩ := exists_intG hk hku
  have hlt : ∀ j : Fin S.rank, o + j.1 < T.rank := fun j => by omega
  refine ⟨h, hh1, fun g hg => ?_⟩
  have hgk : ∀ i j, toEAf D (Formalism.L2.Theta.mt S g i j) = k i j := fun i j => by
    rw [← hh2, ← GlobalTheory.BotClassDict.finStd_of_isFinPt S hS hg, toE_finStd]
  have hfin : ∀ i j, toEAf D (actO S T g⁻¹ 1 y i j) = ∑ l, toEAf D (y i l) * k l j := fun i j => by
    rw [actO_apply, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.hom_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [RingHom.map_mul, hgk]
  refine ite_ne_right_iff.2 ⟨⟨fun i j => ?_, fun i j => ?_⟩, one_ne_zero⟩
  · rw [actO_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hh i l]
  · rw [RingHom.map_sub, hfin]
    unfold unitPt
    by_cases hi : i.1 < o
    · rw [if_neg (by omega), RingHom.map_zero, sub_zero]
      refine inId_sum _ fun l _ => ?_
      rw [mul_comm]
      exact inId_mul (hk l j) (h1 i l hi)
    · obtain ⟨i', rfl⟩ : ∃ i' : Fin S.rank, (⟨o + i'.1, hlt i'⟩ : Fin T.rank) = i :=
        ⟨⟨i.1 - o, by omega⟩, Fin.ext (by dsimp only; omega)⟩
      rw [h2]
      by_cases hij : i' = j
      · rw [if_pos hij, if_pos (by rw [hij]), sub_self]
        exact inId_zero _
      · rw [if_neg hij, if_neg (fun h => hij (Fin.ext (Nat.add_left_cancel h))), RingHom.map_zero, sub_self]
        exact inId_zero _

end GlobalTheory.BotSmallDict.Supp

end

theorem _root_.GlobalTheory.T.exists_maximalLevel_moves_standardPairSupport_to_unitCoset : ∀ {D : D7} (S T : HSp D), S.gram = 1 → T.gram = 1 → D.host.ccK = ⊤ →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank) →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    ∀ o : ℕ, o + S.rank = T.rank →
    ∀ (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) (y : WO S T), GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e (modul P c) o S T βS 1 y ≠ 0 →
    ∃ k ∈ GlobalTheory.NormSum.intG D S.rank, ∀ g : Formalism.L2.Theta.GA D S, GlobalTheory.BotFormula.IsFinPt S g k →
      cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g⁻¹ 1 y) ≠ 0 :=
  GlobalTheory.BotSmallDict.Supp.exists_intG_cosetFn_ne_zero
