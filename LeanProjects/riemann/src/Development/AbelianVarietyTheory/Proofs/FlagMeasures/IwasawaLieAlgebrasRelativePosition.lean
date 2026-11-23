import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagRadicalLowersLeviKeepsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraOfIsCutOutByRealMatrixAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceLoweringMulKeepingIsotropicFlagStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.LiePos

variable {n : ℕ} {ε : Fin n → Bool}

theorem J_mul_J : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem inG_conjTranspose {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) : Formalism.REAL.inG ε Xᴴ := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have hJ' : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y := fun Y => by
    rw [← mul_assoc, hJ, one_mul]
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_conjTranspose]
  have e := congrArg (fun M => Formalism.REAL.Jm ε * M * Formalism.REAL.Jm ε) h
  simp only [mul_add, add_mul, mul_assoc, hJ, hJ', mul_one, mul_zero, zero_mul] at e
  rw [add_comm]
  exact e

theorem inG_sub {X Y : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) (k : Formalism.REAL.inG ε Y) :
    Formalism.REAL.inG ε (X - Y) := by
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_sub, sub_mul, mul_sub]
  rw [show Xᴴ * Formalism.REAL.Jm ε - Yᴴ * Formalism.REAL.Jm ε + (Formalism.REAL.Jm ε * X - Formalism.REAL.Jm ε * Y) =
      (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X) - (Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y) by abel, h, k, sub_zero]

theorem comm_of_maxK {g : Formalism.REAL.UJ ε} (hg : g ∈ maxK ε) :
    uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g := by
  have hU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp hg
  calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hU]
    _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε * uMat g := by rw [h1, one_mul]

theorem skew_of_comm {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X)
    (hc : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X) : Xᴴ = -X := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have h' : Xᴴ * Formalism.REAL.Jm ε = -(X * Formalism.REAL.Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = -(X * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by rw [h']
    _ = -X := by rw [neg_mul, mul_assoc, hJ, mul_one]

theorem exp_unitary {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ = -Z) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Z))ᴴ * NormedSpace.exp ((t : ℂ) • Z) = 1 := by
  have hA : ((t : ℂ) • Z)ᴴ = -((t : ℂ) • Z) := by
    rw [conjTranspose_smul, hZ, smul_neg, Complex.star_def, Complex.conj_ofReal]
  have hc : Commute (-((t : ℂ) • Z)) ((t : ℂ) • Z) := (Commute.refl _).neg_left
  rw [← Matrix.exp_conjTranspose, hA, ← Matrix.exp_add_of_commute _ _ hc, neg_add_cancel, NormedSpace.exp_zero]

theorem mem_span_of_subset {S S' : Set (Formalism.REAL.UJ ε)} {d d' : ℕ} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    {E' : Fin d' → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) (h' : IsCut ε S' E') (hS : S ⊆ S') (i : Fin d) :
    E i ∈ Submodule.span ℝ (Set.range E') := by
  obtain ⟨A', -, -, hA', hS'⟩ := h'
  have hT : E i ∈ A' := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε S d E h).2.1 A' (fun g hg => by
    have hg' : g ∈ S' := hS hg
    rw [hS'] at hg'
    exact hg') i
  exact (hA' _).1 ⟨hT, h.inG (Submodule.subset_span ⟨i, rfl⟩)⟩

theorem lieRel : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsCut ε (maxK ε ∩ flagM ε W) EL → LieRel EN EM EK EL := by
  intro n ε a j W hW dN dM dK dL EN EM EK EL hN hM hK hL
  obtain ⟨hlow, hkeep⟩ := GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps n ε a j W hW
  obtain ⟨htr, hle, hone, -⟩ := GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag n ε a j W hW
  have hENlow : ∀ i, EN i ∈ lowers ε W := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dN EN hN).2.1 (lowers ε W) hlow
  have hEMkeep : ∀ k, EM k ∈ keeps ε W :=
    (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dM EM hM).2.1 (keeps ε W) (fun m hm => sub_mem (hkeep m hm).1 hone)
  have hEMstar : ∀ k, (EM k)ᴴ ∈ keeps ε W := by
    let T2 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
      { carrier := {Y | Yᴴ ∈ keeps ε W}
        add_mem' := fun {A B} hA hB => by
          simp only [Set.mem_ofPred_eq, conjTranspose_add] at *
          exact add_mem hA hB
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, conjTranspose_zero]
          exact zero_mem _
        smul_mem' := fun c Y hY => by
          simp only [Set.mem_ofPred_eq] at *
          rw [conjTranspose_smul, star_trivial]
          exact Submodule.smul_mem _ c hY }
    exact (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dM EM hM).2.1 T2 (fun m hm => by
      change (uMat m - 1)ᴴ ∈ keeps ε W
      rw [conjTranspose_sub, conjTranspose_one]
      exact sub_mem (hkeep m hm).2 hone)
  let TC : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {Y | Y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Y}
      add_mem' := fun {A B} hA hB => by
        simp only [Set.mem_ofPred_eq] at *
        rw [add_mul, mul_add, hA, hB]
      zero_mem' := by simp
      smul_mem' := fun c Y hY => by
        simp only [Set.mem_ofPred_eq] at *
        rw [smul_mul_assoc, mul_smul_comm, hY] }
  have hEK : ∀ i, EK i ∈ TC := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dK EK hK).2.1 TC (fun g hg => by
    change (uMat g - 1) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (uMat g - 1)
    rw [sub_mul, mul_sub, one_mul, mul_one, comm_of_maxK hg])
  have hspan : Submodule.span ℝ (Set.range EK) ≤ TC :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hEK i)
  have hELK : ∀ i, EL i ∈ Submodule.span ℝ (Set.range EK) :=
    mem_span_of_subset hL hK Set.inter_subset_left
  refine ⟨fun i k => htr _ (hENlow i) _ (hEMstar k), fun i k => htr _ (hENlow i) _ (hEMkeep k),
    fun i k => htr _ (hENlow i) _ (hle (hENlow k)), mem_span_of_subset hL hM Set.inter_subset_right, hELK,
    fun i => skew_of_comm (hK.inG (hELK i)) (hspan (hELK i)), fun i => ?_⟩
  have hG : Formalism.REAL.inG ε (EN i) := hN.inG (Submodule.subset_span ⟨i, rfl⟩)
  have hY : Formalism.REAL.inG ε (EN i - (EN i)ᴴ) := inG_sub hG (inG_conjTranspose hG)
  have hskew : (EN i - (EN i)ᴴ)ᴴ = -(EN i - (EN i)ᴴ) := by
    rw [conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]
  refine (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dK EK hK).2.2 _ hY (fun t g hg => ?_)
  change (uMat g)ᴴ * uMat g = 1
  rw [hg]
  exact exp_unitary hskew t

end GlobalTheory.IwConst.LiePos
