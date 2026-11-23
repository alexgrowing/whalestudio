import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WordInduction.BasePointSmoothAndMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose

open scoped ContDiff ComplexConjugate Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section es

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {s : Set P}

def ES {m n : Type} (f : P → Matrix m n ℂ) (s : Set P) : Prop := ∀ a b, ContDiffOn ℝ ∞ (fun x => f x a b) s

theorem es_const {m n : Type} (M : Matrix m n ℂ) (s : Set P) : ES (fun _ => M) s := fun _ _ => contDiffOn_const

theorem es_mul {m n o : Type} [Fintype n] {f : P → Matrix m n ℂ} {g : P → Matrix n o ℂ} (hf : ES f s) (hg : ES g s) :
    ES (fun x => f x * g x) s := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun c _ => (hf a c).mul (hg c b)

theorem es_conjTranspose {m n : Type} {f : P → Matrix m n ℂ} (hf : ES f s) : ES (fun x => (f x)ᴴ) s := by
  intro a b
  simp only [Matrix.conjTranspose_apply, Complex.star_def]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (hf b a)

theorem es_det {n : Type} [Fintype n] [DecidableEq n] {f : P → Matrix n n ℂ} (hf : ES f s) :
    ContDiffOn ℝ ∞ (fun x => (f x).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ => hf (σ i) i

theorem es_updateRow {n : Type} [Fintype n] [DecidableEq n] {f : P → Matrix n n ℂ} (hf : ES f s) (r : n) (v : n → ℂ) :
    ES (fun x => (f x).updateRow r v) s := fun a b => by
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf a b

theorem es_inv {n : Type} [Fintype n] [DecidableEq n] {f : P → Matrix n n ℂ} (hf : ES f s)
    (hd : ∀ x ∈ s, (f x).det ≠ 0) : ES (fun x => (f x)⁻¹) s := fun a b => by
  have hd' : ContDiffOn ℝ ∞ (fun x => ((f x).det)⁻¹) s := (es_det hf).inv hd
  have hu : ES (fun x => (f x).updateRow b (Pi.single a 1)) s := es_updateRow hf b _
  have hm := hd'.mul (es_det hu)
  refine hm.congr fun x hx => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]

theorem es_reindex {m n m' n' : Type} (e : m ≃ m') (e' : n ≃ n') {f : P → Matrix m n ℂ} (hf : ES f s) :
    ES (fun x => Matrix.reindex e e' (f x)) s := by
  intro a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact hf _ _

theorem es_fromBlocks {l m n o : Type} {A : P → Matrix n l ℂ} {B' : P → Matrix n m ℂ} {C : P → Matrix o l ℂ}
    {D' : P → Matrix o m ℂ} (hA : ES A s) (hB : ES B' s) (hC : ES C s) (hD : ES D' s) :
    ES (fun x => Matrix.fromBlocks (A x) (B' x) (C x) (D' x)) s := fun a b => by
  rcases a with a | a <;> rcases b with b | b
  · simpa using hA a b
  · simpa using hB a b
  · simpa using hC a b
  · simpa using hD a b

theorem es_fromRows {m₁ m₂ n : Type} {A : P → Matrix m₁ n ℂ} {B' : P → Matrix m₂ n ℂ} (hA : ES A s) (hB : ES B' s) :
    ES (fun x => Matrix.fromRows (A x) (B' x)) s := fun a b => by
  rcases a with a | a
  · simpa using hA a b
  · simpa using hB a b

theorem es_fromCols {m n₁ n₂ : Type} {A : P → Matrix m n₁ ℂ} {B' : P → Matrix m n₂ ℂ} (hA : ES A s) (hB : ES B' s) :
    ES (fun x => Matrix.fromCols (A x) (B' x)) s := fun a b => by
  rcases b with b | b
  · simpa using hA a b
  · simpa using hB a b

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem es_contDiffOn {m n : Type} [Fintype m] [Fintype n] {f : P → Matrix m n ℂ} (hf : ES f s) :
    ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr fun b => hf a b

end es

section x0

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem det_zfull {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : (zfull Z τ).det = Z.det * τ := by
  simp [zfull, U.blk2, Matrix.det_fromBlocks_zero₂₁]

theorem es_zfull (j : ℕ) (s : Set (ℂ × (Fin j → Fin j → ℂ))) :
    ES (fun q : ℂ × (Fin j → Fin j → ℂ) => zfull (Matrix.of q.2) q.1) s := by
  have h1 : ES (fun q : ℂ × (Fin j → Fin j → ℂ) => Matrix.of q.2) s := fun a b => by
    simp only [Matrix.of_apply]
    fun_prop
  have h4 : ES (fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of fun _ _ : Fin 1 => q.1)) s := fun a b => by
    simp only [Matrix.of_apply]
    exact contDiff_fst.contDiffOn
  simp only [zfull, U.blk2]
  exact es_reindex _ _ (es_fromBlocks h1 (es_const _ _) (es_const _ _) h4)

theorem castM_mem {k a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ B.GV k a) : D.castM h g ∈ B.GV k b := by
  subst h
  have e : D.castM rfl g = g := by
    ext i j
    simp [D.castM]
  rw [e]
  exact hg

private theorem mMap_mem_GV {k j ρ : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : Z.det ≠ 0) {γ : B.Mat k ρ}
    (hγ : γ ∈ B.GV k ρ) : U.mMap k j ρ Z γ ∈ B.GV k (j + ρ) := by
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
  have hu' : IsUnit Zᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hZ)
  have hγ' : γᴴ * Hpk k ρ * γ = Hpk k ρ := hγ
  have hW : ∀ M : Matrix (Fin j) (Fin j) ℂ, G.wMat j * (G.wMat j * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Ux2.wMat_sq, Matrix.one_mul]
  show (U.mMap k j ρ Z γ)ᴴ * Hpk k (j + ρ) * U.mMap k j ρ Z γ = Hpk k (j + ρ)
  rw [Ux2.hpkBlocks k j ρ]
  simp only [U.mMap, Ux2.block3_conjTranspose, Ux2.block3_mul]
  refine Ux2.block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.conjTranspose_mul, Ux2.wMat_ct, Matrix.mul_assoc, Matrix.conjTranspose_nonsing_inv, hγ', hW,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu', Matrix.nonsing_inv_mul _ hu]

theorem base_point_facts_holds : BasePointSmoothAndMem := by
  intro k r j hj γ hγ
  refine ⟨?_, ?_⟩
  · have hZ := es_zfull j {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0}
    have hdet : ∀ q ∈ {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0},
        (zfull (Matrix.of q.2) q.1)ᴴ.det ≠ 0 := by
      rintro q ⟨h1, h2⟩
      rw [Matrix.det_conjTranspose, det_zfull]
      exact star_ne_zero.mpr (mul_ne_zero h2 h1)
    have hI := es_inv (es_conjTranspose hZ) hdet
    have hM : ES (fun q : ℂ × (Fin j → Fin j → ℂ) => U.mMap k (j + 1) (r - (j + 1)) (zfull (Matrix.of q.2) q.1) γ)
        {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} := by
      simp only [U.mMap, U.blk3]
      exact es_reindex _ _ (es_fromBlocks (es_const _ _) (es_fromRows (es_mul hI (es_const _ _)) (es_const _ _))
        (es_fromCols (es_mul (es_const _ _) hZ) (es_const _ _)) (es_const _ _))
    have hX : ES (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ)
        {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} := by
      simp only [x0, D.castM]
      exact es_reindex _ _ hM
    exact es_contDiffOn hX
  · intro q h1 h2
    apply PBF.mem_level_zero_of_mem_group
    simp only [x0]
    apply castM_mem
    apply mMap_mem_GV _ _ hγ
    rw [det_zfull]
    exact mul_ne_zero h2 h1

end x0

theorem word_induction_of_parts_holds : WordIndOfParts := wordIndOfParts_of base_point_facts_holds

end Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf
