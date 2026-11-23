import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section smoothAt

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}

lemma sm_iff {ι κ : Type*} [Fintype ι] [Fintype κ] {F : X → Matrix ι κ ℂ} :
    ContDiffAt ℝ n F x₀ ↔ ∀ i j, ContDiffAt ℝ n (fun x => F x i j) x₀ := by
  exact contDiffAt_pi.trans (forall_congr' fun i => contDiffAt_pi)

lemma sm_mul {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] {F : X → Matrix ι κ ℂ} {G : X → Matrix κ μ ℂ}
    (hF : ContDiffAt ℝ n F x₀) (hG : ContDiffAt ℝ n G x₀) : ContDiffAt ℝ n (fun x => F x * G x) x₀ := by
  rw [sm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hF i l).mul (hG l j)

lemma sm_conjT {ι κ : Type*} [Fintype ι] [Fintype κ] {F : X → Matrix ι κ ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => (F x)ᴴ) x₀ := by
  rw [sm_iff] at hF ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE.contDiff.contDiffAt).comp x₀ (hF j i)

private lemma contDiffAt_finset_prod' {ι : Type*} (s : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ s, ContDiffAt ℝ n (f i) x₀) : ContDiffAt ℝ n (fun x => ∏ i ∈ s, f i x) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (contDiffAt_const : ContDiffAt ℝ n (fun _ : X => (1 : ℂ)) x₀)
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma sm_det {ι : Type*} [Fintype ι] [DecidableEq ι] {F : X → Matrix ι ι ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => (F x).det) x₀ := by
  rw [sm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun τ _ => contDiffAt_const.mul (contDiffAt_finset_prod' _ _ fun i _ => hF (τ i) i)

lemma sm_updateRow {ι : Type*} [Fintype ι] [DecidableEq ι] {F : X → Matrix ι ι ℂ} (hF : ContDiffAt ℝ n F x₀)
    (j : ι) (b : ι → ℂ) : ContDiffAt ℝ n (fun x => (F x).updateRow j b) x₀ := by
  rw [sm_iff] at hF ⊢
  intro i l
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffAt_const
  · exact hF i l

lemma sm_inv {ι : Type*} [Fintype ι] [DecidableEq ι] {F : X → Matrix ι ι ℂ} (hF : ContDiffAt ℝ n F x₀)
    (hu : (F x₀).det ≠ 0) : ContDiffAt ℝ n (fun x => (F x)⁻¹) x₀ := by
  rw [sm_iff]
  intro i l
  simp only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((sm_det hF).inv hu).mul (sm_det (sm_updateRow hF l _))

lemma sm_fromBlocks {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι κ' ℂ} {C : X → Matrix ι' κ ℂ} {D : X → Matrix ι' κ' ℂ}
    (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) (hC : ContDiffAt ℝ n C x₀) (hD : ContDiffAt ℝ n D x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x)) x₀ := by
  rw [sm_iff] at hA hB hC hD ⊢
  rintro (i | i) (j | j)
  · simpa only [Matrix.fromBlocks_apply₁₁] using hA i j
  · simpa only [Matrix.fromBlocks_apply₁₂] using hB i j
  · simpa only [Matrix.fromBlocks_apply₂₁] using hC i j
  · simpa only [Matrix.fromBlocks_apply₂₂] using hD i j

lemma sm_fromRows {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ]
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι' κ ℂ} (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromRows (A x) (B x)) x₀ := by
  rw [sm_iff] at hA hB ⊢
  rintro (i | i) j
  · simpa only [Matrix.fromRows_apply_inl] using hA i j
  · simpa only [Matrix.fromRows_apply_inr] using hB i j

lemma sm_fromCols {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι κ' ℂ} (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromCols (A x) (B x)) x₀ := by
  rw [sm_iff] at hA hB ⊢
  rintro i (j | j)
  · simpa only [Matrix.fromCols_apply_inl] using hA i j
  · simpa only [Matrix.fromCols_apply_inr] using hB i j

lemma sm_reindex {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e₁ : ι ≃ ι') (e₂ : κ ≃ κ') {F : X → Matrix ι κ ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => Matrix.reindex e₁ e₂ (F x)) x₀ := by
  rw [sm_iff] at hF ⊢
  intro i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply] using hF (e₁.symm i) (e₂.symm j)

end smoothAt

section slice

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}

lemma sm_of {s : ℕ} (Z : G.Mat s) : ContDiffAt ℝ n (fun Z' : G.Mat s => Matrix.of Z') Z := by
  rw [sm_iff]
  intro i j
  simp only [Matrix.of_apply]
  exact (contDiff_apply_apply ℝ ℂ i j).contDiffAt

lemma mMap_sm {k j ρ : ℕ} {M : X → Matrix (Fin j) (Fin j) ℂ} (hM : ContDiffAt ℝ n M x₀)
    (hdet : (M x₀).det ≠ 0) (γ : B.Mat k ρ) : ContDiffAt ℝ n (fun x => mMap k j ρ (M x) γ) x₀ := by
  have hdet' : ((M x₀)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hdet
  simp only [mMap, blk3]
  refine sm_reindex _ _ (sm_fromBlocks contDiffAt_const ?_ ?_ contDiffAt_const)
  · exact sm_fromRows (sm_mul (sm_inv (sm_conjT hM) hdet') contDiffAt_const) contDiffAt_const
  · exact sm_fromCols (sm_mul contDiffAt_const hM) contDiffAt_const

variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}

lemma permutationMatrix_eq_permMatrix' (σ : Equiv.Perm (Fin p)) : wP σ = σ.permMatrix ℂ := by
  ext a b
  simp [wP, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

lemma det_hMat_ne (hd : ∀ i, d i ≠ 0) : (hMat σ d).det ≠ 0 := by
  rw [hMat, Matrix.det_mul, permutationMatrix_eq_permMatrix', Matrix.det_permutation, Matrix.det_diagonal]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

private lemma det_one_add_strictLower {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (h : ∀ a b, a ≤ b → M a b = 0) :
    (1 + M).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [h _ _ le_rfl]
  · intro i j hij
    have hij' : i < j := hij
    simp [Matrix.one_apply_ne hij'.ne, h i j hij'.le]

private lemma det_one_add_strictUpper' {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (h : ∀ a b, b ≤ a → M a b = 0) :
    (1 + M).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [h _ _ le_rfl]
  · intro i j hij
    have hij' : j < i := hij
    simp [Matrix.one_apply_ne hij'.ne', h i j hij'.le]

lemma det_zjH_ne (hd : ∀ i, d i ≠ 0) (η : XiH p s σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) :
    (ZjH σ d η Z).det ≠ 0 := by
  simp only [ZjH, Zj, blk2, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, headH, G.detM] at hZ ⊢
  simp only [lowW, G.upper]
  rw [det_one_add_strictLower _ (fun a b hab => ?_), det_one_add_strictUpper' _ (fun a b hab => ?_)]
  · rw [permutationMatrix_eq_permMatrix', Matrix.det_permutation, Matrix.det_diagonal]
    simp only [one_mul, mul_one]
    refine mul_ne_zero (mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hd i)) hZ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · simp [G.strictUpper, not_lt.2 hab]
  · simp [not_lt.2 hab]

lemma rn_mem' (hRP : RadicalParam) (j : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  have hr : Rn k j ρ x ∈ Rset k j ρ := (hRP k j ρ).2.1 ▸ Set.mem_range_self x
  exact ((hRP k j ρ).2.2 hr).1

private lemma mul_mem_GV' {k r : ℕ} {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) :
    a * b ∈ B.GV k r := by
  simp only [B.GV, Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at ha hb ⊢
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha, hb]

lemma gaXi_mem (hSM : SliceMem) (hRP : RadicalParam) (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) {Z : G.Mat s}
    (γ : B.Mat k ρ) (hZ : G.detM Z ≠ 0) (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  exact mul_mem_GV' (mul_mem_GV' (P.BetaSesquilinearity.gv_inv (rn_mem' hRP (p + s) ξ.1.1))
    ((hSM k (p + s) ρ).1 _ γ (det_zjH_ne hd ξ.2 hZ) hγ)) (rn_mem' hRP (p + s) ξ.1.2)

lemma zjH_sm (η : XiH p s σ) (Z : G.Mat s) : ContDiffAt ℝ n (fun Z' : G.Mat s => ZjH σ d η Z') Z := by
  simp only [ZjH, Zj, blk2]
  refine sm_mul (sm_mul contDiffAt_const ?_) contDiffAt_const
  exact sm_reindex _ _ (sm_fromBlocks contDiffAt_const contDiffAt_const contDiffAt_const (sm_of Z))

lemma gaXi_sm (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) (γ : B.Mat k ρ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) :
    ContDiffAt ℝ n (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by
  have hz := zjH_sm (n := n) (d := d) ξ.2 Z
  simp only [gaXi]
  exact sm_mul (sm_mul contDiffAt_const (mMap_sm hz (det_zjH_ne hd ξ.2 hZ) γ)) contDiffAt_const

end slice

theorem zSmooth : ZSmooth := by
  intro hSM hRP k p s ρ σ d hd E _ _ H m hH ξ Z γ hZ hγ
  have hmem := gaXi_mem hSM hRP hd ξ γ hZ hγ
  have hsm : ContDiffAt ℝ m (fun Z' => gaXi k ρ σ d ξ Z' γ) Z := gaXi_sm hd ξ γ hZ
  refine ⟨hmem, hsm.continuousAt, ?_⟩
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hH _ hmem
  have hcomp : ContDiffAt ℝ m (fun Z' => f' (gaXi k ρ σ d ξ Z' γ)) Z :=
    (hf'.contDiffAt (hU.mem_nhds hgU)).comp Z hsm
  refine hcomp.congr_of_eventuallyEq ?_
  have hdet : ∀ᶠ Z' in 𝓝 Z, G.detM Z' ≠ 0 := by
    have hc : ContinuousAt (fun Z' : G.Mat s => G.detM Z') Z := by
      simp only [G.detM]
      exact (sm_det (n := 0) (sm_of Z)).continuousAt
    exact hc.eventually_ne hZ
  have hU' : ∀ᶠ Z' in 𝓝 Z, gaXi k ρ σ d ξ Z' γ ∈ U :=
    hsm.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)
  filter_upwards [hdet, hU'] with Z' h1 h2
  exact hfe _ h2 (gaXi_mem hSM hRP hd ξ γ h1 hγ)

end PI.UnitaryGroupMassFormula.UsCost
