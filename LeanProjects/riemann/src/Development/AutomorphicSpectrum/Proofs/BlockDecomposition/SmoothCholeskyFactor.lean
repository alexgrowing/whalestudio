import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeHaar.Chol

variable {n m k : ℕ}

def invRoot (P : Mat (n + 1)) : ℝ := (Real.sqrt (P 0 0).re)⁻¹

def col (P : Mat (n + 1)) (i : Fin n) : ℂ := P i.succ 0 * (invRoot P : ℂ)

def schur (P : Mat (n + 1)) : Mat n :=
  Matrix.of fun i j => P i.succ j.succ - col P i * star (col P j)

def step (σ : Mat n → Mat n) (P : Mat (n + 1)) : Mat (n + 1) :=
  Matrix.of fun i j =>
    Fin.cases (motive := fun _ => ℂ)
      (Fin.cases (motive := fun _ => ℂ) ((Real.sqrt (P 0 0).re : ℝ) : ℂ) (fun _ => 0) j)
      (fun i' => Fin.cases (motive := fun _ => ℂ) (col P i') (fun j' => σ (schur P) i' j') j) i

lemma step_zero_zero (σ : Mat n → Mat n) (P : Mat (n + 1)) :
    step σ P 0 0 = ((Real.sqrt (P 0 0).re : ℝ) : ℂ) := rfl

lemma step_zero_succ (σ : Mat n → Mat n) (P : Mat (n + 1)) (j : Fin n) :
    step σ P 0 j.succ = 0 := rfl

lemma step_succ_zero (σ : Mat n → Mat n) (P : Mat (n + 1)) (i : Fin n) :
    step σ P i.succ 0 = col P i := rfl

lemma step_succ_succ (σ : Mat n → Mat n) (P : Mat (n + 1)) (i j : Fin n) :
    step σ P i.succ j.succ = σ (schur P) i j := rfl

lemma lead_pos {P : Mat (n + 1)} (hP : P.PosDef) : 0 < (P 0 0).re :=
  (Complex.pos_iff.1 (hP.diag_pos (i := 0))).1

lemma lead_eq {P : Mat (n + 1)} (hP : P.PosDef) : (((P 0 0).re : ℝ) : ℂ) = P 0 0 := by
  apply Complex.ext
  · simp
  · simpa using (Complex.pos_iff.1 (hP.diag_pos (i := 0))).2

lemma root_mul_invRoot {P : Mat (n + 1)} (hP : P.PosDef) :
    Real.sqrt (P 0 0).re * invRoot P = 1 :=
  mul_inv_cancel₀ (Real.sqrt_pos.2 (lead_pos hP)).ne'

lemma lead_mul_invRoot {P : Mat (n + 1)} (hP : P.PosDef) :
    P 0 0 * ((invRoot P : ℂ) * (invRoot P : ℂ)) = 1 := by
  have h : (P 0 0).re * (invRoot P * invRoot P) = 1 := by
    have h1 := root_mul_invRoot hP
    have h2 := Real.mul_self_sqrt (lead_pos hP).le
    calc (P 0 0).re * (invRoot P * invRoot P)
        = (Real.sqrt (P 0 0).re * Real.sqrt (P 0 0).re) * (invRoot P * invRoot P) := by rw [h2]
      _ = (Real.sqrt (P 0 0).re * invRoot P) * (Real.sqrt (P 0 0).re * invRoot P) := by ring
      _ = 1 := by rw [h1]; ring
  rw [← lead_eq hP]
  exact_mod_cast h

lemma schur_posDef {P : Mat (n + 1)} (hP : P.PosDef) : (schur P).PosDef := by
  have hH : ∀ i j, star (P j i) = P i j := fun i j => hP.isHermitian.apply i j
  have hcs : star ((invRoot P : ℝ) : ℂ) = (invRoot P : ℂ) := by simp
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp only [conjTranspose_apply, schur, of_apply, star_sub, star_mul', star_star, hH]
    ring
  · intro x hx
    set c : ℂ := (invRoot P : ℂ) with hc
    set w : ℂ := ∑ j, P 0 j.succ * x j with hw
    set u : ℂ := ∑ i, star (x i) * P i.succ 0 with hu
    set q : ℂ := ∑ i, star (x i) * ∑ j, P i.succ j.succ * x j with hq
    set t : ℂ := -(w * (c * c)) with ht
    let y : Fin (n + 1) → ℂ := Fin.cons t x
    have y0 : y 0 = t := rfl
    have ys : ∀ i : Fin n, y i.succ = x i := fun i => rfl
    have hy : y ≠ 0 := fun h => hx (funext fun i => by simpa [ys] using congrFun h i.succ)
    have hpos := hP.dotProduct_mulVec_pos hy
    have hW : ∑ j, star (col P j) * x j = w * c := by
      rw [hw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [col, star_mul', hH, hcs, ← hc]
      ring
    have hrow : ∀ i, (schur P *ᵥ x) i = (∑ j, P i.succ j.succ * x j) - col P i * (w * c) := by
      intro i
      rw [← hW]
      simp only [mulVec, dotProduct, schur, of_apply, sub_mul, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    have hU : ∑ i, star (x i) * col P i = u * c := by
      rw [hu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [col, ← hc]
      ring
    have hL : star x ⬝ᵥ (schur P *ᵥ x) = q - (u * c) * (w * c) := by
      simp only [dotProduct, hrow, Pi.star_apply, mul_sub, Finset.sum_sub_distrib]
      congr 1
      generalize w * c = v
      rw [← hU, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h0 : (P *ᵥ y) 0 = P 0 0 * t + w := by
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, y0, ys, hw]
    have hs : ∀ i : Fin n, (P *ᵥ y) i.succ = P i.succ 0 * t + ∑ j, P i.succ j.succ * x j := by
      intro i
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, y0, ys]
    have hz : P 0 0 * t + w = 0 := by
      have := lead_mul_invRoot hP
      rw [← hc] at this
      rw [ht]
      linear_combination (-w) * this
    have hR : star y ⬝ᵥ (P *ᵥ y) = u * t + q := by
      rw [dotProduct, Fin.sum_univ_succ]
      simp only [Pi.star_apply, h0, hs, y0, ys, hz, mul_zero, zero_add, mul_add,
        Finset.sum_add_distrib]
      congr 1
      rw [hu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hk : star x ⬝ᵥ (schur P *ᵥ x) = star y ⬝ᵥ (P *ᵥ y) := by
      rw [hL, hR, ht]
      ring
    rw [hk]
    exact hpos

lemma step_mul {σ : Mat n → Mat n} {P : Mat (n + 1)} (hP : P.PosDef)
    (hσ : σ (schur P) * (σ (schur P))ᴴ = schur P) : step σ P * (step σ P)ᴴ = P := by
  have hH : ∀ i j, star (P j i) = P i j := fun i j => hP.isHermitian.apply i j
  have hr : ((Real.sqrt (P 0 0).re : ℝ) : ℂ) * (invRoot P : ℂ) = 1 := by
    exact_mod_cast root_mul_invRoot hP
  have hrr : ((Real.sqrt (P 0 0).re : ℝ) : ℂ) * ((Real.sqrt (P 0 0).re : ℝ) : ℂ) = P 0 0 := by
    rw [← lead_eq hP]
    exact_mod_cast Real.mul_self_sqrt (lead_pos hP).le
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_zero_zero, step_zero_succ]
    simp [hrr]
  · simp only [mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_zero_zero, step_zero_succ,
      step_succ_zero]
    simp only [col, star_mul', hH]
    simp
    linear_combination (P 0 j.succ) * hr
  · simp only [mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_zero_zero, step_zero_succ,
      step_succ_zero, step_succ_succ]
    simp [col]
    linear_combination (P i.succ 0) * hr
  · have h := congrFun (congrFun hσ i) j
    simp only [mul_apply, conjTranspose_apply] at h
    simp only [mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_succ_zero, step_succ_succ, h]
    simp [schur]

lemma contDiff_entry (i j : Fin m) : ContDiff ℝ ∞ (fun P : Mat m => P i j) :=
  contDiff_apply_apply ℝ ℂ i j

lemma contDiffOn_mat {s : Set (Mat k)} {f : Mat k → Mat m}
    (h : ∀ i j, ContDiffOn ℝ ∞ (fun P => f P i j) s) : ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => h i j

lemma contDiffOn_entry {s : Set (Mat k)} {f : Mat k → Mat m} (h : ContDiffOn ℝ ∞ f s)
    (i j : Fin m) : ContDiffOn ℝ ∞ (fun P => f P i j) s :=
  (contDiff_entry i j).comp_contDiffOn h

lemma contDiffOn_root :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => Real.sqrt (P 0 0).re) {P | P.PosDef} :=
  ContDiffOn.sqrt (Complex.reCLM.contDiff.comp (contDiff_entry 0 0)).contDiffOn
    fun _ hP => (lead_pos hP).ne'

lemma contDiffOn_invRoot :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => ((invRoot P : ℝ) : ℂ)) {P | P.PosDef} :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_root.inv fun _ hP => (Real.sqrt_pos.2 (lead_pos hP)).ne')

lemma contDiffOn_col (i : Fin n) :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => col P i) {P | P.PosDef} :=
  (contDiff_entry i.succ 0).contDiffOn.mul contDiffOn_invRoot

lemma contDiffOn_star_col (i : Fin n) :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => star (col P i)) {P | P.PosDef} :=
  Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_col i)

lemma contDiffOn_schur : ContDiffOn ℝ ∞ (schur (n := n)) {P | P.PosDef} :=
  contDiffOn_mat fun i j =>
    (contDiff_entry i.succ j.succ).contDiffOn.sub ((contDiffOn_col i).mul (contDiffOn_star_col j))

lemma contDiffOn_step {σ : Mat n → Mat n} (hσ : ContDiffOn ℝ ∞ σ {P | P.PosDef}) :
    ContDiffOn ℝ ∞ (step σ) {P | P.PosDef} := by
  refine contDiffOn_mat fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_root
  · exact contDiffOn_const
  · exact contDiffOn_col i
  · exact contDiffOn_entry (hσ.comp contDiffOn_schur fun _ hP => schur_posDef hP) i j

theorem exists_smooth_section :
    ∀ n : ℕ, ∃ σ₀ : Mat n → Mat n, ContDiffOn ℝ ∞ σ₀ {P | P.PosDef} ∧
      ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P := by
  intro n
  induction n with
  | zero => exact ⟨id, contDiffOn_id, fun P _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨σ, hσ, hf⟩ := ih
    exact ⟨step σ, contDiffOn_step hσ, fun P hP => step_mul hP (hf _ (schur_posDef hP))⟩

end GlobalTheory.CompanionTheory.ConeHaar.Chol
