import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel

variable {D : D7}

theorem cancel₂ {k l m n : ℕ} {a : Mx D k l} {b : Mx D l m} {c : Mx D k m} (h : a ⬝ b = c) (x : Mx D m n) :
    a ⬝ (b ⬝ x) = c ⬝ x := by
  rw [← h, Matrix.mul_assoc]

theorem cancel₃ {j k l m n : ℕ} {a : Mx D j k} {b : Mx D k l} {c : Mx D l m} {e : Mx D j m} (h : a ⬝ (b ⬝ c) = e)
    (x : Mx D m n) : a ⬝ (b ⬝ (c ⬝ x)) = e ⬝ x := by
  rw [← h, Matrix.mul_assoc, Matrix.mul_assoc]

theorem gram_swap (S : HSp D) {k l : ℕ} {a : Mx D S.rank k} {b : Mx D S.rank l} {c : Mx D k l}
    (h : adj a ⬝ (gA S ⬝ b) = c) : adj b ⬝ (gA S ⬝ a) = adj c := by
  rw [← h, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem gram_rat (S : HSp D) {k l : ℕ} {a : Matrix (Fin S.rank) (Fin k) D.host.E} {b : Matrix (Fin S.rank) (Fin l) D.host.E}
    {c : Matrix (Fin k) (Fin l) D.host.E} (h : aᴴ * S.gram * b = c) : adj (rat a) ⬝ (gA S ⬝ rat b) = rat c := by
  rw [← h, rat_mul, rat_mul, rat_conjTranspose, Matrix.mul_assoc]; rfl

structure OrthDec (S A B : HSp D) where

  iA : Matrix (Fin S.rank) (Fin A.rank) D.host.E

  iB : Matrix (Fin S.rank) (Fin B.rank) D.host.E
  isoA : iAᴴ * S.gram * iA = A.gram
  isoB : iBᴴ * S.gram * iB = B.gram
  orth : iBᴴ * S.gram * iA = 0
  rank_add : A.rank + B.rank = S.rank

namespace OrthDec

variable {S A B : HSp D} (d : OrthDec S A B)

theorem orth' : d.iAᴴ * S.gram * d.iB = 0 := by
  have := congrArg Matrix.conjTranspose d.orth
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
    ← Matrix.mul_assoc] at this

def symm : OrthDec S B A where
  iA := d.iB
  iB := d.iA
  isoA := d.isoB
  isoB := d.isoA
  orth := d.orth'
  rank_add := by rw [add_comm, d.rank_add]

def qA : Matrix (Fin A.rank) (Fin S.rank) D.host.E := A.gram⁻¹ * (d.iAᴴ * S.gram)

def qB : Matrix (Fin B.rank) (Fin S.rank) D.host.E := B.gram⁻¹ * (d.iBᴴ * S.gram)

def jA : Mx D S.rank A.rank := rat d.iA

def jB : Mx D S.rank B.rank := rat d.iB

def pA : Mx D A.rank S.rank := rat d.qA

def pB : Mx D B.rank S.rank := rat d.qB

theorem qA_iA : d.qA * d.iA = 1 := by
  rw [qA, Matrix.mul_assoc, d.isoA, Matrix.nonsing_inv_mul _ (gram_isUnit_det A)]

theorem qA_iB : d.qA * d.iB = 0 := by rw [qA, Matrix.mul_assoc, d.orth', Matrix.mul_zero]

theorem qB_iB : d.qB * d.iB = 1 := d.symm.qA_iA

theorem qB_iA : d.qB * d.iA = 0 := d.symm.qA_iB

theorem iA_qA_add : d.iA * d.qA + d.iB * d.qB = 1 := by
  have h : fromRows d.qA d.qB * fromCols d.iA d.iB = 1 := by
    rw [fromRows_mul_fromCols, qA_iA, qA_iB, qB_iA, qB_iB, fromBlocks_one]
  rw [← fromCols_mul_fromRows]
  exact (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [d.rank_add])).1 h

theorem pA_eq : d.pA = giA A ⬝ (adj d.jA ⬝ gA S) := by
  rw [pA, qA, rat_mul, rat_mul, rat_conjTranspose]; rfl

theorem pB_eq : d.pB = giA B ⬝ (adj d.jB ⬝ gA S) := d.symm.pA_eq

theorem gram_AA : adj d.jA ⬝ (gA S ⬝ d.jA) = gA A := gram_rat S d.isoA

theorem gram_BB : adj d.jB ⬝ (gA S ⬝ d.jB) = gA B := gram_rat S d.isoB

theorem gram_BA : adj d.jB ⬝ (gA S ⬝ d.jA) = 0 := (gram_rat S d.orth).trans rat_zero

theorem gram_AB : adj d.jA ⬝ (gA S ⬝ d.jB) = 0 := d.symm.gram_BA

@[simp] theorem pA_jA : d.pA ⬝ d.jA = 1 := by rw [pA, jA, ← rat_mul, qA_iA, rat_one]

@[simp] theorem pA_jB : d.pA ⬝ d.jB = 0 := by rw [pA, jB, ← rat_mul, qA_iB, rat_zero]

@[simp] theorem pB_jB : d.pB ⬝ d.jB = 1 := d.symm.pA_jA

@[simp] theorem pB_jA : d.pB ⬝ d.jA = 0 := d.symm.pA_jB

theorem sum_eq_one : d.jA ⬝ d.pA + d.jB ⬝ d.pB = 1 := by
  rw [jA, jB, pA, pB, ← rat_mul, ← rat_mul, ← rat_add, iA_qA_add, rat_one]

theorem gram_images {I : Mx D S.rank A.rank} {J : Mx D S.rank B.rank} (hI : adj I ⬝ (gA S ⬝ I) = gA A)
    (hJ : adj J ⬝ (gA S ⬝ J) = gA B) (hJI : adj J ⬝ (gA S ⬝ I) = 0) :
    adj (I ⬝ d.pA + J ⬝ d.pB) ⬝ (gA S ⬝ (I ⬝ d.pA + J ⬝ d.pB)) =
      adj d.pA ⬝ (gA A ⬝ d.pA) + adj d.pB ⬝ (gA B ⬝ d.pB) := by
  have hIJ := gram_swap S hJI
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₃ hI, cancel₃ hJ, cancel₃ hJI,
    cancel₃ hIJ, adj_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gA_eq : gA S = adj d.pA ⬝ (gA A ⬝ d.pA) + adj d.pB ⬝ (gA B ⬝ d.pB) := by
  rw [← d.gram_images d.gram_AA d.gram_BB d.gram_BA, sum_eq_one, adj_one, Matrix.one_mul, Matrix.mul_one]

theorem giA_eq : giA S = d.jA ⬝ (giA A ⬝ adj d.jA) + d.jB ⬝ (giA B ⬝ adj d.jB) := by
  rw [← Matrix.one_mul (giA S), ← d.sum_eq_one, pA_eq, pB_eq]
  simp only [Matrix.add_mul, Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]

def emb : GA D A × GA D B →* GA D S where
  toFun p := ofMat S (d.jA ⬝ mt A p.1 ⬝ d.pA + d.jB ⬝ mt B p.2 ⬝ d.pB) (by
    refine (d.gram_images ?_ ?_ ?_).trans d.gA_eq.symm
    · rw [adj_mul, Matrix.mul_assoc, cancel₃ d.gram_AA, mt_unitary]
    · rw [adj_mul, Matrix.mul_assoc, cancel₃ d.gram_BB, mt_unitary]
    · rw [adj_mul, Matrix.mul_assoc, cancel₃ d.gram_BA, Matrix.zero_mul, Matrix.mul_zero])
  map_one' := mt_injective S (by
    rw [mt_ofMat, Prod.fst_one, Prod.snd_one, mt_one, mt_one, mt_one, Matrix.mul_one, Matrix.mul_one, sum_eq_one])
  map_mul' p q := mt_injective S (by
    simp only [mt_mul, mt_ofMat, Prod.fst_mul, Prod.snd_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      cancel₂ d.pA_jA, cancel₂ d.pA_jB, cancel₂ d.pB_jA, cancel₂ d.pB_jB, Matrix.one_mul, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add])

theorem mt_emb (a : GA D A) (b : GA D B) :
    mt S (d.emb (a, b)) = d.jA ⬝ mt A a ⬝ d.pA + d.jB ⬝ mt B b ⬝ d.pB := rfl

theorem emb_jA (a : GA D A) (b : GA D B) : mt S (d.emb (a, b)) ⬝ d.jA = d.jA ⬝ mt A a := by
  simp only [mt_emb, Matrix.add_mul, Matrix.mul_assoc, pA_jA, pB_jA, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem emb_jB (a : GA D A) (b : GA D B) : mt S (d.emb (a, b)) ⬝ d.jB = d.jB ⬝ mt B b := by
  simp only [mt_emb, Matrix.add_mul, Matrix.mul_assoc, pA_jB, pB_jB, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem pA_emb (a : GA D A) (b : GA D B) : d.pA ⬝ mt S (d.emb (a, b)) = mt A a ⬝ d.pA := by
  simp only [mt_emb, Matrix.mul_add, Matrix.mul_assoc, cancel₂ d.pA_jA, cancel₂ d.pA_jB, Matrix.one_mul,
    Matrix.zero_mul, add_zero]

theorem pB_emb (a : GA D A) (b : GA D B) : d.pB ⬝ mt S (d.emb (a, b)) = mt B b ⬝ d.pB := by
  simp only [mt_emb, Matrix.mul_add, Matrix.mul_assoc, cancel₂ d.pB_jA, cancel₂ d.pB_jB, Matrix.one_mul,
    Matrix.zero_mul, zero_add]

theorem emb_symm (a : GA D A) (b : GA D B) : d.symm.emb (b, a) = d.emb (a, b) :=
  mt_injective S (add_comm _ _)

theorem emb_injective : Function.Injective d.emb := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : d.pA ⬝ (mt S (d.emb (a, b)) ⬝ d.jA) = d.pA ⬝ (mt S (d.emb (a', b')) ⬝ d.jA) := by rw [h]
  have h2 : d.pB ⬝ (mt S (d.emb (a, b)) ⬝ d.jB) = d.pB ⬝ (mt S (d.emb (a', b')) ⬝ d.jB) := by rw [h]
  rw [emb_jA, emb_jA, cancel₂ d.pA_jA, cancel₂ d.pA_jA, Matrix.one_mul, Matrix.one_mul] at h1
  rw [emb_jB, emb_jB, cancel₂ d.pB_jB, cancel₂ d.pB_jB, Matrix.one_mul, Matrix.one_mul] at h2
  exact Prod.ext (mt_injective A h1) (mt_injective B h2)

theorem continuous_emb : Continuous d.emb :=
  continuous_of_mt S (((continuous_const.matrix_mul ((continuous_mt A).comp continuous_fst)).matrix_mul
    continuous_const).add ((continuous_const.matrix_mul ((continuous_mt B).comp continuous_snd)).matrix_mul
      continuous_const))

theorem emb_mem_GQ {a : GA D A} {b : GA D B} (ha : a ∈ GQ A) (hb : b ∈ GQ B) : d.emb (a, b) ∈ GQ S := by
  rw [mem_GQ_iff] at ha hb ⊢
  exact add_mem (ratMx_mul (ratMx_mul (rat_mem _) ha) (rat_mem _)) (ratMx_mul (ratMx_mul (rat_mem _) hb) (rat_mem _))

theorem embRel_left (ι : A.V →ₗ[D.host.E] S.V) (hι : frameMat S A ι = d.iA) (a : GA D A) :
    EmbRel S A ι (d.emb (a, 1)) a := by
  rw [EmbRel, hι]
  refine ⟨d.emb_jA a 1, fun x hx => ?_⟩
  have h1 : d.qA *ᵥ x = 0 := by
    rw [qA, ← Matrix.mulVec_mulVec]
    exact (congrArg (A.gram⁻¹ *ᵥ ·) hx).trans (Matrix.mulVec_zero _)
  have h2 : d.pA *ᵥ (fun i => incA D (x i)) = 0 := by
    funext i
    have := RingHom.map_mulVec (incA D) d.qA x i
    rw [h1, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h3 := congrArg (· *ᵥ fun i => incA D (x i)) d.sum_eq_one
  change mt S (d.emb (a, 1)) *ᵥ _ = _
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero, Matrix.one_mulVec] at h3
  rw [mt_emb, mt_one, Matrix.mul_one, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero,
    ← Matrix.mulVec_mulVec, h3]

theorem embRel_right (ι : B.V →ₗ[D.host.E] S.V) (hι : frameMat S B ι = d.iB) (b : GA D B) :
    EmbRel S B ι (d.emb (1, b)) b := by
  rw [← emb_symm]; exact d.symm.embRel_left ι hι b

def resS (T : HSp D) : WO S T ≃+ WO A T × WO B T where
  toFun x := (x ⬝ d.jA, x ⬝ d.jB)
  invFun p := p.1 ⬝ d.pA + p.2 ⬝ d.pB
  left_inv x := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_add, sum_eq_one, Matrix.mul_one]
  right_inv p := by
    simp only [Matrix.add_mul, Matrix.mul_assoc, pA_jA, pA_jB, pB_jA, pB_jB, Matrix.mul_one, Matrix.mul_zero, add_zero,
      zero_add]
  map_add' x y := Prod.ext (Matrix.add_mul _ _ _) (Matrix.add_mul _ _ _)

theorem resS_apply (T : HSp D) (x : WO S T) : d.resS T x = (x ⬝ d.jA, x ⬝ d.jB) := rfl

theorem resS_symm_apply (T : HSp D) (u : WO A T) (v : WO B T) :
    (d.resS T).symm (u, v) = u ⬝ d.pA + v ⬝ d.pB := rfl

theorem hO_resS (T : HSp D) (x y : WO S T) :
    hO S T x y = hO A T (d.resS T x).1 (d.resS T y).1 + hO B T (d.resS T x).2 (d.resS T y).2 := by
  simp only [hO_eq_trace, resS_apply, adj_mul]
  rw [d.giA_eq, Matrix.add_mul, trace_add, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc d.jB,
    trace_mul_comm d.jB]
  simp only [Matrix.mul_assoc]

theorem symplOH_resS (T : HSp D) (x y : WO S T) :
    symplOH S T x y = symplOH A T (d.resS T x).1 (d.resS T y).1 + symplOH B T (d.resS T x).2 (d.resS T y).2 := by
  rw [symplOH_eq, hO_resS d, map_add]; rfl

theorem symplO_resS (T : HSp D) (x y : WO S T) :
    symplO S T x y = symplO A T (d.resS T x).1 (d.resS T y).1 + symplO B T (d.resS T x).2 (d.resS T y).2 := by
  rw [symplO_eq, hO_resS d, mul_add, map_add]; rfl

theorem resS_actO (T : HSp D) (a : GA D A) (b : GA D B) (h : GA D T) (x : WO S T) :
    d.resS T (actO S T (d.emb (a, b)) h x) = (actO A T a h (d.resS T x).1, actO B T b h (d.resS T x).2) := by
  simp only [resS_apply, actO_eq, ← map_inv, Prod.inv_mk, Matrix.mul_assoc, emb_jA, emb_jB]

theorem mem_ratL_resS (T : HSp D) (x : WO S T) :
    x ∈ ratL T S ↔ (d.resS T x).1 ∈ ratL T A ∧ (d.resS T x).2 ∈ ratL T B := by
  refine ⟨fun h => ⟨ratMx_mul h (rat_mem _), ratMx_mul h (rat_mem _)⟩, fun h => ?_⟩
  rw [← (d.resS T).symm_apply_apply x]
  exact add_mem (ratMx_mul h.1 (rat_mem _)) (ratMx_mul h.2 (rat_mem _))

theorem continuous_resS (T : HSp D) : Continuous (d.resS T) :=
  (continuous_id.matrix_mul continuous_const).prodMk (continuous_id.matrix_mul continuous_const)

theorem continuous_resS_symm (T : HSp D) : Continuous (d.resS T).symm :=
  (continuous_fst.matrix_mul continuous_const).add (continuous_snd.matrix_mul continuous_const)

def boxS (T : HSp D) (fA : WO A T → ℂ) (fB : WO B T → ℂ) : WO S T → ℂ :=
  fun w => fA (d.resS T w).1 * fB (d.resS T w).2

theorem boxS_zero (T : HSp D) (fA : WO A T → ℂ) (fB : WO B T → ℂ) : d.boxS T fA fB 0 = fA 0 * fB 0 := by
  rw [boxS, map_zero]; rfl

theorem heisO_boxS (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (fA : WO A T → ℂ) (fB : WO B T → ℂ) (u : WO S T) :
    heisO ψ S T u (d.boxS T fA fB) = d.boxS T (heisO ψ A T (d.resS T u).1 fA) (heisO ψ B T (d.resS T u).2 fB) := by
  funext w
  simp only [heisO, boxS]
  rw [d.symplOH_resS, AddChar.map_add_eq_mul, map_add, Prod.fst_add, Prod.snd_add]
  ring

theorem isThetaFunO_boxS {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {fA : WO A T → ℂ} {fB : WO B T → ℂ}
    (hA : IsThetaFunO ψ A T fA) (hB : IsThetaFunO ψ B T fB) : IsThetaFunO ψ S T (d.boxS T fA fB) := by
  have h := isThetaFunO_prod (S := S) (T := T) 1 d.iA 1 d.iB (fun x y => by
    simp only [sandwich_apply, rat_one, Matrix.one_mul]
    exact d.symplOH_resS T x y) hA hB
  simp only [sandwich_apply, rat_one, Matrix.one_mul] at h
  exact h

end OrthDec

namespace OrthDec

variable {T A B : HSp D} (d : OrthDec T A B)

def resT (S : HSp D) : WO S T ≃+ WO S A × WO S B where
  toFun x := (d.pA ⬝ x, d.pB ⬝ x)
  invFun p := d.jA ⬝ p.1 + d.jB ⬝ p.2
  left_inv x := by
    simp only [← Matrix.mul_assoc]
    rw [← Matrix.add_mul, sum_eq_one, Matrix.one_mul]
  right_inv p := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, pA_jA, pA_jB, pB_jA, pB_jB, Matrix.one_mul, Matrix.zero_mul,
      add_zero, zero_add]
  map_add' x y := Prod.ext (Matrix.mul_add _ _ _) (Matrix.mul_add _ _ _)

theorem resT_apply (S : HSp D) (x : WO S T) : d.resT S x = (d.pA ⬝ x, d.pB ⬝ x) := rfl

theorem resT_symm_apply (S : HSp D) (u : WO S A) (v : WO S B) :
    (d.resT S).symm (u, v) = d.jA ⬝ u + d.jB ⬝ v := rfl

theorem hO_resT (S : HSp D) (x y : WO S T) :
    hO S T x y = hO S A (d.resT S x).1 (d.resT S y).1 + hO S B (d.resT S x).2 (d.resT S y).2 := by
  simp only [hO_eq_trace, resT_apply, adj_mul]
  rw [d.gA_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, trace_add, Matrix.mul_assoc]

theorem symplOH_resT (S : HSp D) (x y : WO S T) :
    symplOH S T x y = symplOH S A (d.resT S x).1 (d.resT S y).1 + symplOH S B (d.resT S x).2 (d.resT S y).2 := by
  rw [symplOH_eq, hO_resT d, map_add]; rfl

theorem symplO_resT (S : HSp D) (x y : WO S T) :
    symplO S T x y = symplO S A (d.resT S x).1 (d.resT S y).1 + symplO S B (d.resT S x).2 (d.resT S y).2 := by
  rw [symplO_eq, hO_resT d, mul_add, map_add]; rfl

theorem resT_actO (S : HSp D) (g : GA D S) (a : GA D A) (b : GA D B) (x : WO S T) :
    d.resT S (actO S T g (d.emb (a, b)) x) = (actO S A g a (d.resT S x).1, actO S B g b (d.resT S x).2) := by
  simp only [resT_apply, actO_eq, ← Matrix.mul_assoc, pA_emb, pB_emb]

theorem mem_ratL_resT (S : HSp D) (x : WO S T) :
    x ∈ ratL T S ↔ (d.resT S x).1 ∈ ratL A S ∧ (d.resT S x).2 ∈ ratL B S := by
  refine ⟨fun h => ⟨ratMx_mul (rat_mem _) h, ratMx_mul (rat_mem _) h⟩, fun h => ?_⟩
  rw [← (d.resT S).symm_apply_apply x]
  exact add_mem (ratMx_mul (rat_mem _) h.1) (ratMx_mul (rat_mem _) h.2)

theorem continuous_resT (S : HSp D) : Continuous (d.resT S) :=
  (continuous_const.matrix_mul continuous_id).prodMk (continuous_const.matrix_mul continuous_id)

theorem continuous_resT_symm (S : HSp D) : Continuous (d.resT S).symm :=
  (continuous_const.matrix_mul continuous_fst).add (continuous_const.matrix_mul continuous_snd)

def boxT (S : HSp D) (fA : WO S A → ℂ) (fB : WO S B → ℂ) : WO S T → ℂ :=
  fun w => fA (d.resT S w).1 * fB (d.resT S w).2

theorem boxT_zero (S : HSp D) (fA : WO S A → ℂ) (fB : WO S B → ℂ) : d.boxT S fA fB 0 = fA 0 * fB 0 := by
  rw [boxT, map_zero]; rfl

theorem heisO_boxT (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) (fA : WO S A → ℂ) (fB : WO S B → ℂ) (u : WO S T) :
    heisO ψ S T u (d.boxT S fA fB) = d.boxT S (heisO ψ S A (d.resT S u).1 fA) (heisO ψ S B (d.resT S u).2 fB) := by
  funext w
  simp only [heisO, boxT]
  rw [d.symplOH_resT, AddChar.map_add_eq_mul, map_add, Prod.fst_add, Prod.snd_add]
  ring

theorem isThetaFunO_boxT {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {fA : WO S A → ℂ} {fB : WO S B → ℂ}
    (hA : IsThetaFunO ψ S A fA) (hB : IsThetaFunO ψ S B fB) : IsThetaFunO ψ S T (d.boxT S fA fB) := by
  have h := isThetaFunO_prod (S := S) (T := T) d.qA 1 d.qB 1 (fun x y => by
    simp only [sandwich_apply, rat_one, Matrix.mul_one]
    exact d.symplOH_resT S x y) hA hB
  simp only [sandwich_apply, rat_one, Matrix.mul_one] at h
  exact h

end OrthDec

end GlobalTheory.MixModel

end
