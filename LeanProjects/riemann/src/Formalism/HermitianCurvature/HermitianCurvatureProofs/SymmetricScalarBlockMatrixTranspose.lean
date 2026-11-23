import Formalism.HermitianCurvature.StatementU
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulDiagOfTriangular

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.Ux2
section blocks3

variable {k j ρ : ℕ}

lemma eB_ll (a : Fin j) : (eB k j ρ (Sum.inl (Sum.inl a))).val = a.val := by simp [eB]
lemma eB_lr (v : Fin (2 * ρ + k + 1)) : (eB k j ρ (Sum.inl (Sum.inr v))).val = j + v.val := by simp [eB]
lemma eB_r (a : Fin j) : (eB k j ρ (Sum.inr a)).val = j + (2 * ρ + k + 1) + a.val := by simp [eB]

lemma block3_apply (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (x y : Ix k j ρ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 (eB k j ρ x) (eB k j ρ y) =
      Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23) (Matrix.fromCols A31 A32) A33 x y := by
  simp [blk3, Matrix.reindex_apply]

lemma mat_ext_eB {M N : B.Mat k (j + ρ)}
    (h : ∀ x y, M (eB k j ρ x) (eB k j ρ y) = N (eB k j ρ x) (eB k j ρ y)) : M = N := by
  ext a b
  simpa using h ((eB k j ρ).symm a) ((eB k j ρ).symm b)

lemma mul_eB (M N : B.Mat k (j + ρ)) (x y : Ix k j ρ) :
    (M * N) (eB k j ρ x) (eB k j ρ y) =
      ∑ z : Ix k j ρ, M (eB k j ρ x) (eB k j ρ z) * N (eB k j ρ z) (eB k j ρ y) := by
  rw [Matrix.mul_apply]
  exact (Equiv.sum_comp (eB k j ρ) (fun z => M (eB k j ρ x) z * N z (eB k j ρ y))).symm

lemma block3_mul (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 * blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 =
      blk3 (A11 * ToralGalois + A12 * B21 + A13 * B31) (A11 * cocyclesToWachVectorsExponent + A12 * B22 + A13 * B32) (A11 * B13 + A12 * B23 + A13 * B33)
        (A21 * ToralGalois + A22 * B21 + A23 * B31) (A21 * cocyclesToWachVectorsExponent + A22 * B22 + A23 * B32) (A21 * B13 + A22 * B23 + A23 * B33)
        (A31 * ToralGalois + A32 * B21 + A33 * B31) (A31 * cocyclesToWachVectorsExponent + A32 * B22 + A33 * B32) (A31 * B13 + A32 * B23 + A33 * B33) := by
  apply mat_ext_eB; intro x y
  rw [mul_eB]; simp only [block3_apply, Fintype.sum_sum_type]
  rcases x with (x|x)|x <;> rcases y with (y|y)|y <;> simp [Matrix.mul_apply, add_assoc]

lemma block3_conjTranspose (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) :
    (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33)ᴴ = blk3 A11ᴴ A21ᴴ A31ᴴ A12ᴴ A22ᴴ A32ᴴ A13ᴴ A23ᴴ A33ᴴ := by
  apply mat_ext_eB; intro x y
  rw [conjTranspose_apply, block3_apply, block3_apply]
  rcases x with (x|x)|x <;> rcases y with (y|y)|y <;> simp

lemma wMat_ct (d : ℕ) : (G.wMat d)ᴴ = G.wMat d := by
  ext a b
  by_cases h : b = a.rev
  · subst h; simp [G.wMat, conjTranspose_apply]
  · have h' : a ≠ b.rev := fun e => h (by rw [e, Fin.rev_rev])
    simp [G.wMat, conjTranspose_apply, h, h']

lemma wMat_mul_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (G.wMat d * M) i j = M i.rev j := by
  simp [Matrix.mul_apply, G.wMat]

lemma wMat_sq (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext a b
  rw [wMat_mul_apply]
  by_cases h : a = b
  · subst h; simp [G.wMat]
  · have h' : b ≠ a.rev.rev := by rw [Fin.rev_rev]; exact Ne.symm h
    simp [G.wMat, h, h'] <;> exact fun e => h e.symm

theorem hpkBlocks : HpkBlocks := by
  intro k j ρ
  apply mat_ext_eB; intro x y
  rw [block3_apply]
  rcases x with (x|x)|x <;> rcases y with (y|y)|y <;>
    (have hx := x.isLt; have hy := y.isLt
     simp [Hpk, G.wMat, Fin.ext_iff, eB_ll, eB_lr, eB_r, Fin.val_rev] <;> split_ifs <;> first | rfl | omega)

lemma block3_congr {A11 ToralGalois : Matrix (Fin j) (Fin j) ℂ} {A12 cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 B13 : Matrix (Fin j) (Fin j) ℂ} {A21 B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 B22 : B.Mat k ρ}
    {A23 B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 B31 : Matrix (Fin j) (Fin j) ℂ}
    {A32 B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 B33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : A11 = ToralGalois) (h12 : A12 = cocyclesToWachVectorsExponent) (h13 : A13 = B13) (h21 : A21 = B21) (h22 : A22 = B22) (h23 : A23 = B23)
    (h31 : A31 = B31) (h32 : A32 = B32) (h33 : A33 = B33) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 = blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 := by
  subst_vars; rfl

lemma wMat_sq_assoc (d : ℕ) {n : Type*} (M : Matrix (Fin d) n ℂ) : G.wMat d * (G.wMat d * M) = M := by
  rw [← Matrix.mul_assoc, wMat_sq, Matrix.one_mul]

theorem sliceMem : SliceMem := by
  intro k j ρ
  refine ⟨?_, ?_, ?_⟩
  · intro Z γ hZ hγ
    have hγ' : γᴴ * Hpk k ρ * γ = Hpk k ρ := hγ
    have hZu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
    have hu : IsUnit Zᴴ.det := by
      rw [det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hZ)
    show (mMap k j ρ Z γ)ᴴ * Hpk k (j + ρ) * mMap k j ρ Z γ = Hpk k (j + ρ)
    rw [hpkBlocks k j ρ]; unfold mMap
    rw [block3_conjTranspose, block3_mul, block3_mul]
    refine block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [Matrix.mul_assoc, wMat_ct, Matrix.conjTranspose_nonsing_inv, wMat_sq_assoc, hγ', Matrix.nonsing_inv_mul _ hZu, Matrix.mul_nonsing_inv _ hu,
        Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hZu]
  · intro q hq
    have hqu : IsUnit q.det := isUnit_iff_ne_zero.mpr hq
    have hu : IsUnit qᴴ.det := by
      rw [det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hq)
    show (muP k j ρ q)ᴴ * Hpk k (j + ρ) * muP k j ρ q = Hpk k (j + ρ)
    rw [hpkBlocks k j ρ]; unfold muP
    rw [block3_conjTranspose, block3_mul, block3_mul]
    refine block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [Matrix.mul_assoc, wMat_ct, Matrix.conjTranspose_nonsing_inv, wMat_sq_assoc, Matrix.nonsing_inv_mul _ hqu, Matrix.mul_nonsing_inv _ hu,
        Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hqu]
  · intro y hy
    have hy' : yᴴ * Hpk k ρ * y = Hpk k ρ := hy
    show (embG k j ρ y)ᴴ * Hpk k (j + ρ) * embG k j ρ y = Hpk k (j + ρ)
    rw [hpkBlocks k j ρ]; unfold embG
    rw [block3_conjTranspose, block3_mul, block3_mul]
    refine block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [hy']

section blocks
variable (M : B.Mat k (j + ρ))
def b11 : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inl a))) (eB k j ρ (Sum.inl (Sum.inl b)))
def b12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inl a))) (eB k j ρ (Sum.inl (Sum.inr b)))
def b13 : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inl a))) (eB k j ρ (Sum.inr b))
def b21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inl (Sum.inl b)))
def b22 : B.Mat k ρ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inl (Sum.inr b)))
def b23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inr b))
def b31 : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inl (Sum.inl b)))
def b32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inl (Sum.inr b)))
def b33 : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inr b))

lemma block3_eta : M = blk3 (b11 M) (b12 M) (b13 M) (b21 M) (b22 M) (b23 M) (b31 M) (b32 M) (b33 M) := by
  apply mat_ext_eB; intro x y; rw [block3_apply]
  rcases x with (x|x)|x <;> rcases y with (y|y)|y <;> rfl
end blocks

lemma block3_injective {A11 ToralGalois : Matrix (Fin j) (Fin j) ℂ} {A12 cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 B13 : Matrix (Fin j) (Fin j) ℂ} {A21 B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 B22 : B.Mat k ρ}
    {A23 B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 B31 : Matrix (Fin j) (Fin j) ℂ}
    {A32 B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 B33 : Matrix (Fin j) (Fin j) ℂ}
    (h : blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 = blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33) :
    A11 = ToralGalois ∧ A12 = cocyclesToWachVectorsExponent ∧ A13 = B13 ∧ A21 = B21 ∧ A22 = B22 ∧ A23 = B23 ∧ A31 = B31 ∧ A32 = B32 ∧ A33 = B33 := by
  have e : ∀ x y, blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 (eB k j ρ x) (eB k j ρ y) =
      blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 (eB k j ρ x) (eB k j ρ y) := fun x y => by rw [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext a b
  · simpa [block3_apply] using e (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b))
  · simpa [block3_apply] using e (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inr b))
  · simpa [block3_apply] using e (Sum.inl (Sum.inl a)) (Sum.inr b)
  · simpa [block3_apply] using e (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inl b))
  · simpa [block3_apply] using e (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inr b))
  · simpa [block3_apply] using e (Sum.inl (Sum.inr a)) (Sum.inr b)
  · simpa [block3_apply] using e (Sum.inr a) (Sum.inl (Sum.inl b))
  · simpa [block3_apply] using e (Sum.inr a) (Sum.inl (Sum.inr b))
  · simpa [block3_apply] using e (Sum.inr a) (Sum.inr b)

lemma rset_blocks {g : B.Mat k (j + ρ)} (hg : g ∈ Rset k j ρ) :
    b11 g = 1 ∧ b21 g = 0 ∧ b31 g = 0 ∧ b22 g = 1 ∧ b32 g = 0 := by
  obtain ⟨_, h1, h2⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext a b
  · have := h1 (eB k j ρ (Sum.inl (Sum.inl a))) (eB k j ρ (Sum.inl (Sum.inl b))) (by rw [eB_ll]; exact b.isLt)
    simpa [b11, Matrix.one_apply] using this
  · have := h1 (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inl (Sum.inl b))) (by rw [eB_ll]; exact b.isLt)
    simpa [b21] using this
  · have := h1 (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inl (Sum.inl b))) (by rw [eB_ll]; exact b.isLt)
    simpa [b31] using this
  · have hb := b.isLt
    have := h2 (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inl (Sum.inr b))) (by rw [eB_lr]; omega)
      (by rw [eB_lr]; omega) (by rw [eB_lr]; omega)
    simpa [b22, Matrix.one_apply] using this
  · have hb := b.isLt
    have := h2 (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inl (Sum.inr b))) (by rw [eB_lr]; omega)
      (by rw [eB_lr]; omega) (by rw [eB_r]; omega)
    simpa [b32] using this

lemma rset_of_blocks {g : B.Mat k (j + ρ)} (hG : g ∈ B.GV k (j + ρ)) (h11 : b11 g = 1) (h21 : b21 g = 0)
    (h31 : b31 g = 0) (h22 : b22 g = 1) (h32 : b32 g = 0) : g ∈ Rset k j ρ := by
  refine ⟨hG, ?_, ?_⟩
  · intro i b hb
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective b
    rcases y with (y|y)|y
    · rcases x with (x|x)|x
      · have := congrFun (congrFun h11 x) y; simpa [b11, Matrix.one_apply] using this
      · have := congrFun (congrFun h21 x) y; simpa [b21] using this
      · have := congrFun (congrFun h31 x) y; simpa [b31] using this
    · rw [eB_lr] at hb; omega
    · rw [eB_r] at hb; omega
  · intro i b hb1 hb2 hi
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective b
    rcases y with (y|y)|y
    · rw [eB_ll] at hb1; have := y.isLt; omega
    · rcases x with (x|x)|x
      · rw [eB_ll] at hi; have := x.isLt; omega
      · have := congrFun (congrFun h22 x) y; simpa [b22, Matrix.one_apply] using this
      · have := congrFun (congrFun h32 x) y; simpa [b32] using this
    · rw [eB_r] at hb2; omega

lemma rset_sub_nset : Rset k j ρ ⊆ Nset k (j + ρ) := by
  rintro g ⟨hG, h1, h2⟩
  refine ⟨hG, ?_, ?_⟩
  · intro a i hai
    by_cases ha : a.val < j
    · exact h1 i (eI k (j + ρ) a) ha
    · have hai' : a.val ≤ i.val := hai
      have := a.isLt
      exact h2 i (eI k (j + ρ) a) (show j ≤ a.val by omega) (show a.val < j + (2 * ρ + k + 1) by omega) (by omega)
  · intro i b hb1 hb2 hi
    exact h2 i b (by omega) (by omega) (by omega)

lemma skewOf_ct (q : (G.UT j → ℂ) × (Fin j → ℝ)) : (skewOf q)ᴴ = -skewOf q := by
  ext a b
  by_cases h : a = b
  · subst h; simp [skewOf, G.strictUpper, conjTranspose_apply]
  · simp [skewOf, conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h]

lemma skewOf_lt (q : (G.UT j → ℂ) × (Fin j → ℝ)) {a b : Fin j} (h : a < b) : skewOf q a b = q.1 ⟨(a, b), h⟩ := by
  simp [skewOf, G.strictUpper, h, not_lt.mpr h.le, ne_of_lt h, conjTranspose_apply]

lemma skewOf_diag (q : (G.UT j → ℂ) × (Fin j → ℝ)) (a : Fin j) : skewOf q a a = Complex.I * q.2 a := by
  simp [skewOf, G.strictUpper, conjTranspose_apply]

lemma rn_mem (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  have hH : (Hpk k ρ)ᴴ = Hpk k ρ := (hpkFacts k ρ).1
  have hS := skewOf_ct x.2
  show (Rn k j ρ x)ᴴ * Hpk k (j + ρ) * Rn k j ρ x = Hpk k (j + ρ)
  rw [hpkBlocks k j ρ]; unfold Rn
  rw [block3_conjTranspose, block3_mul, block3_mul]
  refine block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mul_assoc, wMat_ct, wMat_sq_assoc, wMat_sq, hH, hS, Matrix.conjTranspose_smul] <;> module

lemma rn_rset (x : RC k j ρ) : Rn k j ρ x ∈ Rset k j ρ :=
  rset_of_blocks (rn_mem x) (by ext a b; simp [b11, Rn, block3_apply]) (by ext a b; simp [b21, Rn, block3_apply])
    (by ext a b; simp [b31, Rn, block3_apply]) (by ext a b; simp [b22, Rn, block3_apply]) (by ext a b; simp [b32, Rn, block3_apply])

lemma rn_injective : Function.Injective (Rn k j ρ) := by
  intro x y h
  unfold Rn at h
  obtain ⟨-, -, h13, -, -, h23, -, -, -⟩ := block3_injective h
  have h1 : x.1 = y.1 := by funext i a; exact congrFun (congrFun h23 i) a
  have hw := congrArg (G.wMat j * ·) h13
  simp only [wMat_sq_assoc] at hw
  rw [h1] at hw
  have hs : skewOf x.2 = skewOf y.2 := add_left_cancel hw
  have h2 : x.2 = y.2 := by
    refine Prod.ext ?_ ?_
    · funext p
      have := congrFun (congrFun hs p.1.1) p.1.2
      rw [skewOf_lt _ p.2, skewOf_lt _ p.2] at this
      exact this
    · funext a
      have := congrArg Complex.im (congrFun (congrFun hs a) a)
      rw [skewOf_diag, skewOf_diag] at this
      simpa using this
  exact Prod.ext h1 h2

lemma rset_sub_range {g : B.Mat k (j + ρ)} (hg : g ∈ Rset k j ρ) : ∃ x, Rn k j ρ x = g := by
  obtain ⟨h11, h21, h31, h22, h32⟩ := rset_blocks hg
  have hH : (Hpk k ρ)ᴴ = Hpk k ρ := (hpkFacts k ρ).1
  have hG : gᴴ * Hpk k (j + ρ) * g = Hpk k (j + ρ) := hg.1
  have hgeta := block3_eta g
  rw [h11, h21, h31, h22, h32] at hgeta
  rw [hgeta, hpkBlocks k j ρ, block3_conjTranspose, block3_mul, block3_mul] at hG
  obtain ⟨-, -, e13, -, -, e23, -, -, e33⟩ := block3_injective hG
  simp [Matrix.mul_assoc, wMat_ct] at e13 e23 e33
  have hD : b33 g = 1 := by
    have := congrArg (G.wMat j * ·) e13
    simpa [wMat_sq_assoc, wMat_sq] using this
  rw [hD] at e23 e33 hgeta
  simp at e23 e33
  have hA1 : (b12 g)ᴴ * G.wMat j = -(Hpk k ρ * b23 g) := eq_neg_of_add_eq_zero_right e23
  have hA2 : (b12 g)ᴴ = -(Hpk k ρ * b23 g * G.wMat j) := by
    have := congrArg (· * G.wMat j) hA1
    simpa [Matrix.mul_assoc, wMat_sq] using this
  have hA : b12 g = -(G.wMat j * (b23 g)ᴴ * Hpk k ρ) := by
    have := congrArg Matrix.conjTranspose hA2
    simpa [Matrix.mul_assoc, wMat_ct, hH] using this
  set S : Matrix (Fin j) (Fin j) ℂ := G.wMat j * b13 g + (1 / 2 : ℂ) • ((b23 g)ᴴ * Hpk k ρ * b23 g) with hSdef
  have hS : Sᴴ = -S := by
    rw [eq_neg_iff_add_eq_zero, hSdef]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_smul, wMat_ct, hH, conjTranspose_conjTranspose]
    have hstar : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [hstar]
    rw [← e33]; simp only [Matrix.mul_assoc]; module
  have hSe : ∀ a b, star (S b a) = -S a b := fun a b => by
    have := congrFun (congrFun hS a) b
    simpa [conjTranspose_apply] using this
  let q : (G.UT j → ℂ) × (Fin j → ℝ) := (fun p => S p.1.1 p.1.2, fun a => (S a a).im)
  have hq : skewOf q = S := by
    ext a b
    rcases lt_trichotomy a b with h | h | h
    · rw [skewOf_lt _ h]
    · subst h
      rw [skewOf_diag]
      have hre : (S a a).re = 0 := by
        have := congrArg Complex.re (hSe a a)
        simp at this; linarith
      apply Complex.ext <;> simp [q, hre]
    · have h1 := congrFun (congrFun (skewOf_ct q) a) b
      simp only [conjTranspose_apply, Matrix.neg_apply] at h1
      rw [skewOf_lt _ h] at h1
      have h2 := hSe a b
      exact neg_inj.mp (h1.symm.trans h2)
  refine ⟨(Matrix.of.symm (b23 g), q), ?_⟩
  conv_rhs => rw [hgeta]
  unfold Rn
  refine block3_congr rfl ?_ ?_ rfl rfl ?_ rfl rfl rfl
  · simp [hA]
  · rw [hq, hSdef]
    simp only [Equiv.apply_symm_apply]
    have : (-(1 / 2 : ℂ)) • ((b23 g)ᴴ * Hpk k ρ * b23 g) +
        (G.wMat j * b13 g + (1 / 2 : ℂ) • ((b23 g)ᴴ * Hpk k ρ * b23 g)) = G.wMat j * b13 g := by module
    rw [this, wMat_sq_assoc]
  · simp

theorem radicalParam : RadicalParam := by
  intro k j ρ
  refine ⟨rn_injective, ?_, rset_sub_nset⟩
  ext g
  constructor
  · rintro ⟨x, rfl⟩; exact rn_rset x
  · intro hg; exact rset_sub_range hg

end blocks3

section tri

variable {p : ℕ}

def uniK (κ : Fin p → ℤ) (M : Matrix (Fin p) (Fin p) ℂ) : Prop :=
  (∀ i, M i i = 1) ∧ ∀ a b, κ a < κ b → M a b = 0

def kL (p : ℕ) : Fin p → ℤ := fun a => (a.val : ℤ)

def kU (p : ℕ) : Fin p → ℤ := fun a => -(a.val : ℤ)

def kS (σ : Equiv.Perm (Fin p)) : Fin p → ℤ := fun a => ((σ.symm a).val : ℤ)

lemma kL_lt {a b : Fin p} : kL p a < kL p b ↔ a < b := by
  simp only [kL, Nat.cast_lt]; exact Fin.lt_def.symm
lemma kU_lt {a b : Fin p} : kU p a < kU p b ↔ b < a := by
  simp only [kU, neg_lt_neg_iff, Nat.cast_lt]; exact Fin.lt_def.symm
lemma kS_lt (σ : Equiv.Perm (Fin p)) {a b : Fin p} : kS σ a < kS σ b ↔ σ.symm a < σ.symm b := by
  simp only [kS, Nat.cast_lt]; exact Fin.lt_def.symm
lemma kL_inj : Function.Injective (kL p) := fun a b h => Fin.ext (by simpa [kL] using h)
lemma kU_inj : Function.Injective (kU p) := fun a b h => Fin.ext (by simpa [kU] using h)
lemma kS_inj (σ : Equiv.Perm (Fin p)) : Function.Injective (kS σ) := fun a b h =>
  σ.symm.injective (Fin.ext (by simpa [kS] using h))

lemma lower_iff (l : Matrix (Fin p) (Fin p) ℂ) : G.IsLowerUni l ↔ uniK (kL p) l := by
  simp only [G.IsLowerUni, G.IsUpperUni, uniK, transpose_apply, kL_lt]
  exact ⟨fun h => ⟨h.1, fun a b hab => h.2 b a hab⟩, fun h => ⟨h.1, fun a b hab => h.2 b a hab⟩⟩

lemma upper_iff (u : Matrix (Fin p) (Fin p) ℂ) : G.IsUpperUni u ↔ uniK (kU p) u := by
  simp [G.IsUpperUni, uniK, kU_lt]

lemma diag_mul_of {κ : Fin p → ℤ} (hκ : Function.Injective κ) {M N : Matrix (Fin p) (Fin p) ℂ}
    (hM : ∀ a b, κ a < κ b → M a b = 0) (hN : ∀ a b, κ a < κ b → N a b = 0) (i : Fin p) :
    (M * N) i i = M i i * N i i := by
  first | exact GlobalTheory.TriangularDiagonal.mul_diag_of_triangular .. | (apply GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> assumption) | (intros; apply GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> assumption) | (apply @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> assumption) | (intros; apply @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> assumption) | (apply @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular <;> first | assumption | infer_instance) | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M N hM hN i | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M N hM hN | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M N hM | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M N | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ M | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ hκ | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p κ | exact @GlobalTheory.TriangularDiagonal.mul_diag_of_triangular p

lemma uniK_mul {κ : Fin p → ℤ} (hκ : Function.Injective κ) {M N : Matrix (Fin p) (Fin p) ℂ}
    (hM : uniK κ M) (hN : uniK κ N) : uniK κ (M * N) := by
  refine ⟨fun i => by rw [diag_mul_of hκ hM.2 hN.2, hM.1, hN.1, one_mul], fun a b hab => ?_⟩
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : κ a < κ c
  · rw [hM.2 a c h, zero_mul]
  · rw [hN.2 c b (lt_of_le_of_lt (not_lt.mp h) hab), mul_zero]

lemma uniK_one (κ : Fin p → ℤ) : uniK κ 1 :=
  ⟨fun i => Matrix.one_apply_eq i, fun a b hab => Matrix.one_apply_ne (fun h => by subst h; exact lt_irrefl _ hab)⟩

lemma uniK_one_add {κ : Fin p → ℤ} {N : Matrix (Fin p) (Fin p) ℂ} (hd : ∀ a, N a a = 0)
    (hz : ∀ a b, κ a < κ b → N a b = 0) : uniK κ (1 + N) ∧ uniK κ (1 - N) := by
  have hne : ∀ a b, κ a < κ b → a ≠ b := fun a b h e => by subst e; exact lt_irrefl _ h
  refine ⟨⟨fun i => by simp [hd i], fun a b hab => ?_⟩, ⟨fun i => by simp [hd i], fun a b hab => ?_⟩⟩
  · simp [Matrix.one_apply_ne (hne a b hab), hz a b hab]
  · simp [Matrix.one_apply_ne (hne a b hab), hz a b hab]

lemma lowK_unit {L : Matrix (Fin p) (Fin p) ℂ} (h : uniK (kL p) L) : IsUnit L.det := by
  rw [Matrix.det_of_isLowerTriangular L (fun i j hij => h.2 i j (kL_lt.mpr (OrderDual.toDual_lt_toDual.mp hij)))]
  simp [h.1]

lemma upK_unit {U : Matrix (Fin p) (Fin p) ℂ} (h : uniK (kU p) U) : IsUnit U.det := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h.2 i j (kU_lt.mpr hij))]
  simp [h.1]

lemma lowK_inv {L : Matrix (Fin p) (Fin p) ℂ} (h : uniK (kL p) L) :
    uniK (kL p) L⁻¹ ∧ L * L⁻¹ = 1 ∧ L⁻¹ * L = 1 := by
  have hu := lowK_unit h
  have h1 : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hu
  have h2 : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hu
  letI := L.invertibleOfIsUnitDet hu
  have hbt : L⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular
      (fun i j hij => h.2 i j (kL_lt.mpr (OrderDual.toDual_lt_toDual.mp hij)))
  have hz : ∀ a b, kL p a < kL p b → L⁻¹ a b = 0 := fun a b hab =>
    hbt (OrderDual.toDual_lt_toDual.mpr (kL_lt.mp hab))
  refine ⟨⟨fun i => ?_, hz⟩, h1, h2⟩
  have := congrFun (congrFun h1 i) i
  rw [diag_mul_of kL_inj h.2 hz, h.1, one_mul, Matrix.one_apply_eq] at this
  exact this

lemma upK_inv {U : Matrix (Fin p) (Fin p) ℂ} (h : uniK (kU p) U) :
    uniK (kU p) U⁻¹ ∧ U * U⁻¹ = 1 ∧ U⁻¹ * U = 1 := by
  have hu := upK_unit h
  have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hu
  have h2 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hu
  letI := U.invertibleOfIsUnitDet hu
  have hbt : U⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h.2 i j (kU_lt.mpr hij))
  have hz : ∀ a b, kU p a < kU p b → U⁻¹ a b = 0 := fun a b hab => hbt (kU_lt.mp hab)
  refine ⟨⟨fun i => ?_, hz⟩, h1, h2⟩
  have := congrFun (congrFun h1 i) i
  rw [diag_mul_of kU_inj h.2 hz, h.1, one_mul, Matrix.one_apply_eq] at this
  exact this

lemma permutationMatrix_mul_apply (σ : Equiv.Perm (Fin p)) (M : Matrix (Fin p) (Fin p) ℂ) (a b : Fin p) :
    (wP σ * M) a b = M (σ a) b := by
  simp [wP, Matrix.mul_apply]

lemma mul_wP_apply (σ : Equiv.Perm (Fin p)) (M : Matrix (Fin p) (Fin p) ℂ) (a b : Fin p) :
    (M * wP σ) a b = M a (σ.symm b) := by
  simp [wP, Matrix.mul_apply, ← Equiv.eq_symm_apply]

lemma permutationMatrix_mul_symm (σ : Equiv.Perm (Fin p)) : wP σ * wP σ.symm = 1 := by
  ext a b
  rw [permutationMatrix_mul_apply]
  by_cases h : a = b
  · subst h; simp [wP]
  · simp [wP, Matrix.one_apply_ne h, h]

lemma permutationMatrix_symm_mul (σ : Equiv.Perm (Fin p)) : wP σ.symm * wP σ = 1 := by
  simpa using permutationMatrix_mul_symm σ.symm

lemma permutationMatrix_inv (σ : Equiv.Perm (Fin p)) : (wP σ)⁻¹ = wP σ.symm := Matrix.inv_eq_right_inv (permutationMatrix_mul_symm σ)

lemma permutationMatrix_conj_apply (σ : Equiv.Perm (Fin p)) (M : Matrix (Fin p) (Fin p) ℂ) (a b : Fin p) :
    (wP σ * M * (wP σ)⁻¹) a b = M (σ a) (σ b) := by
  rw [permutationMatrix_inv, mul_wP_apply, permutationMatrix_mul_apply]; simp

lemma lowW_apply (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (a b : Fin p) :
    lowW σ v a b = (if a = b then 1 else 0) + (if h : b < a ∧ σ.symm b < σ.symm a then v ⟨(a, b), h⟩ else 0) := by
  simp [lowW, Matrix.one_apply]

theorem lowWSpec : LowWSpec := by
  intro p σ l
  constructor
  · rintro ⟨hl, hc⟩
    rw [lower_iff] at hl hc
    refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
    ext a b
    rw [lowW_apply]
    rcases lt_trichotomy a b with h | h | h
    · simp [hl.2 a b (kL_lt.mpr h), ne_of_lt h, not_lt.mpr h.le]
    · subst h; simp [hl.1]
    · by_cases hs : σ.symm b < σ.symm a
      · simp [h, hs, ne_of_gt h]
      · have hs' : σ.symm a < σ.symm b :=
          lt_of_le_of_ne (not_lt.mp hs) (fun e => ne_of_gt h (σ.symm.injective e))
        have := hc.2 (σ.symm a) (σ.symm b) (kL_lt.mpr hs')
        rw [permutationMatrix_conj_apply] at this
        simp at this
        simp [this, hs, ne_of_gt h]
  · rintro ⟨v, rfl⟩
    rw [lower_iff, lower_iff]
    refine ⟨⟨fun i => by simp [lowW_apply], fun a b hab => ?_⟩,
      ⟨fun i => by simp [permutationMatrix_conj_apply, lowW_apply], fun a b hab => ?_⟩⟩
    · rw [kL_lt] at hab; simp [lowW_apply, ne_of_lt hab, not_lt.mpr hab.le]
    · rw [kL_lt] at hab; rw [permutationMatrix_conj_apply, lowW_apply]
      simp [σ.injective.ne (ne_of_lt hab), not_lt.mpr hab.le]

lemma elim_step {κ : Fin p → ℤ} (hκ : Function.Injective κ) (m : Matrix (Fin p) (Fin p) ℂ) (hm : uniK κ m) :
    ∀ n : ℕ, ∃ L M : Matrix (Fin p) (Fin p) ℂ, uniK κ L ∧ uniK (kL p) L ∧ uniK κ M ∧
      (∀ a b : Fin p, b.val < n → b < a → M a b = 0) ∧ m = L * M := by
  intro n
  induction n with
  | zero => exact ⟨1, m, uniK_one κ, uniK_one _, hm, fun a b h => absurd h (Nat.not_lt_zero _), by rw [Matrix.one_mul]⟩
  | succ n ih =>
    obtain ⟨L, M, hLk, hLl, hMk, hMz, hm'⟩ := ih
    by_cases hn : n < p
    · let c : Fin p := ⟨n, hn⟩
      let Nm : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun a b => if b = c ∧ c < a then M a c else 0
      have hNN : Nm * Nm = 0 := by
        ext a b
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun e _ => ?_
        by_cases he : e = c
        · subst he; simp [Nm]
        · simp [Nm, he]
      have hEF : (1 + Nm) * (1 - Nm) = 1 := by
        rw [add_mul, mul_sub, mul_sub, hNN]; simp
      have hNd : ∀ a, Nm a a = 0 := fun a => by
        simp only [Nm, Matrix.of_apply]
        split_ifs with h
        · exact absurd (h.1 ▸ h.2) (lt_irrefl _)
        · rfl
      have hNk : ∀ a b, κ a < κ b → Nm a b = 0 := by
        intro a b hab
        simp only [Nm, Matrix.of_apply]
        split_ifs with h
        · rw [← h.1]; exact hMk.2 a b hab
        · rfl
      have hNl : ∀ a b, kL p a < kL p b → Nm a b = 0 := by
        intro a b hab
        rw [kL_lt] at hab
        simp only [Nm, Matrix.of_apply]
        split_ifs with h
        · exact absurd (h.1 ▸ h.2) (not_lt.mpr hab.le)
        · rfl
      have hNM : ∀ a b, (Nm * M) a b = (if c < a then M a c else 0) * M c b := by
        intro a b
        rw [Matrix.mul_apply, Finset.sum_eq_single c]
        · simp [Nm]
        · intro e _ he; simp [Nm, he]
        · simp
      refine ⟨L * (1 + Nm), (1 - Nm) * M, uniK_mul hκ hLk (uniK_one_add hNd hNk).1,
        uniK_mul kL_inj hLl (uniK_one_add hNd hNl).1, uniK_mul hκ (uniK_one_add hNd hNk).2 hMk, ?_, ?_⟩
      · intro a b hb hba
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, hNM]
        rcases Nat.lt_or_ge b.val n with h | h
        · have hcb : b < c := Fin.lt_def.mpr h
          rw [hMz a b h hba, hMz c b h hcb]; simp
        · have hbc : b = c := Fin.ext (by simp [c]; omega)
          rw [hbc] at hba ⊢
          rw [if_pos hba, hMk.1 c]; ring
      · rw [hm', Matrix.mul_assoc L, ← Matrix.mul_assoc (1 + Nm), hEF, Matrix.one_mul]
    · exact ⟨L, M, hLk, hLl, hMk, fun a b hb hba => hMz a b (by have := b.isLt; omega) hba, hm'⟩

lemma factor {κ : Fin p → ℤ} (hκ : Function.Injective κ) (m : Matrix (Fin p) (Fin p) ℂ) (hm : uniK κ m) :
    ∃ L N : Matrix (Fin p) (Fin p) ℂ, uniK κ L ∧ uniK (kL p) L ∧ uniK (kU p) N ∧ m = L * N := by
  obtain ⟨L, M, h1, h2, h3, h4, h5⟩ := elim_step hκ m hm p
  exact ⟨L, M, h1, h2, ⟨h3.1, fun a b hab => h4 a b b.isLt (kU_lt.mp hab)⟩, h5⟩

lemma upper_eq {u : Matrix (Fin p) (Fin p) ℂ} (hu : uniK (kU p) u) : u = G.upper (fun q => u q.1.1 q.1.2) := by
  ext a b
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply]
  rcases lt_trichotomy a b with h | h | h
  · simp [h, ne_of_lt h]
  · subst h; simp [hu.1]
  · simp [not_lt.mpr h.le, ne_of_gt h, hu.2 a b (kU_lt.mpr h)]

lemma upper_uni (u : G.UT p → ℂ) : uniK (kU p) (G.upper u) := by
  refine ⟨fun i => by simp [G.upper, G.strictUpper], fun a b hab => ?_⟩
  rw [kU_lt] at hab
  simp [G.upper, G.strictUpper, not_lt.mpr hab.le, ne_of_gt hab]

lemma lowW_uni (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) : uniK (kL p) (lowW σ v) :=
  (lower_iff _).mp ((lowWSpec p σ _).mpr ⟨v, rfl⟩).1

lemma lowW_inj (σ : Equiv.Perm (Fin p)) : Function.Injective (lowW σ) := by
  intro v1 v2 h
  funext q
  have := congrFun (congrFun h q.1.1) q.1.2
  rw [lowW_apply, lowW_apply, dif_pos q.2, dif_pos q.2] at this
  simpa using this

lemma upper_inj : Function.Injective (G.upper (d := p)) := by
  intro u1 u2 h
  funext q
  have := congrFun (congrFun h q.1.1) q.1.2
  simpa [G.upper, G.strictUpper, q.2, ne_of_lt q.2] using this

lemma lu_unique {L1 L2 U1 U2 : Matrix (Fin p) (Fin p) ℂ} (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (hL1 : uniK (kL p) L1) (hL2 : uniK (kL p) L2) (hU1 : uniK (kU p) U1) (hU2 : uniK (kU p) U2)
    (h : L1 * diagonal d * U1 = L2 * diagonal d * U2) : L1 = L2 ∧ U1 = U2 := by
  obtain ⟨hL2i, hL2a, hL2b⟩ := lowK_inv hL2
  obtain ⟨hU1i, hU1a, hU1b⟩ := upK_inv hU1
  have hYX : (L2⁻¹ * L1) * diagonal d = diagonal d * (U2 * U1⁻¹) := by
    have := congrArg (fun M => L2⁻¹ * M * U1⁻¹) h
    calc (L2⁻¹ * L1) * diagonal d = L2⁻¹ * (L1 * diagonal d * U1) * U1⁻¹ := by
          simp [Matrix.mul_assoc, hU1a]
      _ = L2⁻¹ * (L2 * diagonal d * U2) * U1⁻¹ := this
      _ = diagonal d * (U2 * U1⁻¹) := by simp [← Matrix.mul_assoc, hL2b]
  have hY := uniK_mul kL_inj hL2i hL1
  have hX := uniK_mul kU_inj hU2 hU1i
  have hY1 : L2⁻¹ * L1 = 1 := by
    ext a b
    have e := congrFun (congrFun hYX a) b
    rw [mul_diagonal, diagonal_mul] at e
    rcases lt_trichotomy a b with hab | hab | hab
    · rw [hY.2 a b (kL_lt.mpr hab), Matrix.one_apply_ne (ne_of_lt hab)]
    · subst hab; rw [hY.1, Matrix.one_apply_eq]
    · rw [hX.2 a b (kU_lt.mpr hab), mul_zero] at e
      rw [Matrix.one_apply_ne (ne_of_gt hab)]
      exact (mul_eq_zero.mp e).resolve_right (hd b)
  have hX1 : U2 * U1⁻¹ = 1 := by
    ext a b
    have e := congrFun (congrFun hYX a) b
    rw [mul_diagonal, diagonal_mul] at e
    rcases lt_trichotomy a b with hab | hab | hab
    · rw [hY.2 a b (kL_lt.mpr hab), zero_mul] at e
      rw [Matrix.one_apply_ne (ne_of_lt hab)]
      exact ((mul_eq_zero.mp e.symm).resolve_left (hd a))
    · subst hab; rw [hX.1, Matrix.one_apply_eq]
    · rw [hX.2 a b (kU_lt.mpr hab), Matrix.one_apply_ne (ne_of_gt hab)]
  constructor
  · calc L1 = (L2 * L2⁻¹) * L1 := by rw [hL2a, Matrix.one_mul]
      _ = L2 * (L2⁻¹ * L1) := Matrix.mul_assoc _ _ _
      _ = L2 := by rw [hY1, Matrix.mul_one]
  · symm
    calc U2 = U2 * (U1⁻¹ * U1) := by rw [hU1b, Matrix.mul_one]
      _ = (U2 * U1⁻¹) * U1 := (Matrix.mul_assoc _ _ _).symm
      _ = U1 := by rw [hX1, Matrix.one_mul]

lemma headH_inj (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) {v1 v2 : LW σ → ℂ}
    {u1 u2 : G.UT p → ℂ} (h : headH σ d v1 u1 = headH σ d v2 u2) : v1 = v2 ∧ u1 = u2 := by
  have h' := congrArg (wP σ.symm * ·) h
  simp only [headH, Matrix.mul_assoc] at h'
  rw [← Matrix.mul_assoc (wP σ.symm), ← Matrix.mul_assoc (wP σ.symm), permutationMatrix_symm_mul, Matrix.one_mul,
    Matrix.one_mul] at h'
  simp only [← Matrix.mul_assoc] at h'
  obtain ⟨e1, e2⟩ := lu_unique d hd (lowW_uni σ v1) (lowW_uni σ v2) (upper_uni u1) (upper_uni u2) h'
  exact ⟨lowW_inj σ e1, upper_inj e2⟩

theorem headOrbit : HeadOrbit := by
  intro p σ d hd
  refine ⟨fun l u hl hu => ?_, fun q => ?_⟩
  · rw [lower_iff] at hl
    rw [upper_iff] at hu
    have hc : ∀ a b, (wP σ.symm * l * wP σ) a b = l (σ.symm a) (σ.symm b) := by
      intro a b; rw [mul_wP_apply, permutationMatrix_mul_apply]
    have hm : uniK (kS σ) (wP σ.symm * l * wP σ) :=
      ⟨fun i => by rw [hc, hl.1], fun a b hab => by rw [hc]; exact hl.2 _ _ (kL_lt.mpr ((kS_lt σ).mp hab))⟩
    obtain ⟨L, N, hLk, hLl, hNu, hmLN⟩ := factor (kS_inj σ) _ hm
    obtain ⟨v, hv⟩ : ∃ v, L = lowW σ v := by
      apply (lowWSpec p σ L).mp
      refine ⟨(lower_iff L).mpr hLl, (lower_iff _).mpr ⟨fun i => by rw [permutationMatrix_conj_apply, hLk.1], fun a b hab => ?_⟩⟩
      rw [permutationMatrix_conj_apply]
      exact hLk.2 _ _ ((kS_lt σ).mpr (by simpa using kL_lt.mp hab))
    have hconj : uniK (kU p) (diagonal (fun i => (d i)⁻¹) * N * diagonal d) := by
      refine ⟨fun i => ?_, fun a b hab => ?_⟩
      · rw [mul_diagonal, diagonal_mul, hNu.1]; field_simp [hd i]
      · rw [mul_diagonal, diagonal_mul, hNu.2 a b hab]; simp
    have hU' := uniK_mul kU_inj hconj hu
    have hl' : l * wP σ = wP σ * (L * N) := by
      rw [← hmLN]; simp only [← Matrix.mul_assoc, permutationMatrix_mul_symm, Matrix.one_mul]
    have hdd : diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd i)
    have hex : l * hMat σ d * u = headH σ d v (fun q => (diagonal (fun i => (d i)⁻¹) * N * diagonal d * u) q.1.1 q.1.2) := by
      unfold headH hMat
      rw [← upper_eq hU', ← hv]
      calc l * (wP σ * diagonal d) * u = (l * wP σ) * diagonal d * u := by simp [Matrix.mul_assoc]
        _ = wP σ * (L * N) * diagonal d * u := by rw [hl']
        _ = wP σ * L * diagonal d * (diagonal (fun i => (d i)⁻¹) * N * diagonal d * u) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (diagonal d) (diagonal _), hdd, Matrix.one_mul]
    refine ⟨(v, fun q => (diagonal (fun i => (d i)⁻¹) * N * diagonal d * u) q.1.1 q.1.2), hex, fun y hy => ?_⟩
    obtain ⟨e1, e2⟩ := headH_inj σ d hd (hy.symm.trans hex)
    exact Prod.ext e1 e2
  · refine ⟨wP σ * lowW σ q.1 * (wP σ)⁻¹, G.upper q.2, ((lowWSpec p σ _).mpr ⟨q.1, rfl⟩).2,
      (upper_iff _).mpr (upper_uni q.2), ?_⟩
    rw [permutationMatrix_inv]
    simp only [hMat, headH, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (wP σ.symm) (wP σ), permutationMatrix_symm_mul, Matrix.one_mul]

end tri

section twoBlocks

variable {p s : ℕ}

lemma symmetricScalarBlockMatrix_mul (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D * blk2 A' B' C' D' = blk2 (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  unfold blk2
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

lemma symmetricScalarBlockMatrix_transpose (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    (blk2 A B C D)ᵀ = blk2 Aᵀ Cᵀ Bᵀ Dᵀ := by
  unfold blk2
  rw [Matrix.transpose_reindex, Matrix.fromBlocks_transpose]

lemma block2_apply_upper_left (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) (x y : Fin p) :
    blk2 A B C D (Fin.castAdd s x) (Fin.castAdd s y) = A x y := by simp [blk2]

lemma block2_apply_lower_left (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) (x : Fin s) (y : Fin p) :
    blk2 A B C D (Fin.natAdd p x) (Fin.castAdd s y) = C x y := by simp [blk2]

lemma block2_apply_lower_right (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) (x y : Fin s) :
    blk2 A B C D (Fin.natAdd p x) (Fin.natAdd p y) = D x y := by simp [blk2]

lemma supS_eq (M : Matrix (Fin p) (Fin p) ℂ) : supS M = subS Mᵀ := by
  simp [subS, supS, transpose_apply]

lemma subdiagonal_sum_block2 (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    subS (blk2 A B C D) = subS A + (if h : 0 < s ∧ 0 < p then C ⟨0, h.1⟩ ⟨p - 1, by omega⟩ else 0) + subS D := by
  unfold subS
  rw [Fin.sum_univ_add]
  have h1 : ∀ i : Fin p, (if h : (Fin.castAdd s i).val + 1 < p + s then blk2 A B C D ⟨(Fin.castAdd s i).val + 1, h⟩ (Fin.castAdd s i) else 0) =
      (if h : i.val + 1 < p then A ⟨i.val + 1, h⟩ i else 0) +
        (if h : i.val + 1 = p ∧ 0 < s then C ⟨0, h.2⟩ i else 0) := by
    intro i
    have hi := i.isLt
    by_cases ha : i.val + 1 < p
    · have hlt : (Fin.castAdd s i).val + 1 < p + s := by simp; omega
      rw [dif_pos hlt, dif_pos ha, dif_neg (by omega), add_zero]
      have e : (⟨(Fin.castAdd s i).val + 1, hlt⟩ : Fin (p + s)) = Fin.castAdd s ⟨i.val + 1, ha⟩ := Fin.ext (by simp)
      rw [e, block2_apply_upper_left]
    · by_cases hs : 0 < s
      · have hlt : (Fin.castAdd s i).val + 1 < p + s := by simp; omega
        rw [dif_pos hlt, dif_neg ha, dif_pos ⟨by omega, hs⟩, zero_add]
        have e : (⟨(Fin.castAdd s i).val + 1, hlt⟩ : Fin (p + s)) = Fin.natAdd p ⟨0, hs⟩ := Fin.ext (by simp; omega)
        rw [e, block2_apply_lower_left]
      · rw [dif_neg (by simp; omega), dif_neg ha, dif_neg (by omega), add_zero]
  have h2 : ∀ i : Fin s, (if h : (Fin.natAdd p i).val + 1 < p + s then blk2 A B C D ⟨(Fin.natAdd p i).val + 1, h⟩ (Fin.natAdd p i) else 0) =
      (if h : i.val + 1 < s then D ⟨i.val + 1, h⟩ i else 0) := by
    intro i
    by_cases ha : i.val + 1 < s
    · have hlt : (Fin.natAdd p i).val + 1 < p + s := by simp; omega
      rw [dif_pos hlt, dif_pos ha]
      have e : (⟨(Fin.natAdd p i).val + 1, hlt⟩ : Fin (p + s)) = Fin.natAdd p ⟨i.val + 1, ha⟩ := Fin.ext (by simp; omega)
      rw [e, block2_apply_lower_right]
    · rw [dif_neg (by simp; omega), dif_neg ha]
  simp only [h1, h2, Finset.sum_add_distrib]
  congr 2
  by_cases hps : 0 < s ∧ 0 < p
  · rw [dif_pos hps, Finset.sum_eq_single ⟨p - 1, by omega⟩]
    · rw [dif_pos ⟨by simp; omega, hps.1⟩]
    · intro i _ hi
      rw [dif_neg]
      rintro ⟨h, -⟩
      exact hi (Fin.ext (by simp; omega))
    · simp
  · rw [dif_neg hps]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [dif_neg]
    rintro ⟨h, h'⟩
    exact hps ⟨h', by omega⟩

theorem charBlock : CharBlock := by
  intro p s a b lh uh l u hlh hl huh hu
  rw [lower_iff] at hlh hl
  rw [upper_iff] at huh hu
  constructor
  · rw [symmetricScalarBlockMatrix_mul, subdiagonal_sum_block2]
    simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
    congr 2
    unfold cornerA
    by_cases hps : 0 < s ∧ 0 < p
    · rw [dif_pos hps, dif_pos hps, Matrix.mul_apply, Finset.sum_eq_single ⟨p - 1, by omega⟩]
      · rw [hlh.1, mul_one]; rfl
      · intro c _ hc
        have : c.val < p - 1 := by have := c.isLt; have : c.val ≠ p - 1 := fun e => hc (Fin.ext e); omega
        rw [hlh.2 c ⟨p - 1, by omega⟩ (kL_lt.mpr (Fin.lt_def.mpr this)), mul_zero]
      · simp
    · rw [dif_neg hps, dif_neg hps]
  · rw [symmetricScalarBlockMatrix_mul, supS_eq, supS_eq, supS_eq]
    simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
    rw [symmetricScalarBlockMatrix_transpose, subdiagonal_sum_block2]
    congr 2
    unfold cornerB
    by_cases hps : 0 < s ∧ 0 < p
    · rw [dif_pos hps, dif_pos hps, transpose_apply, Matrix.mul_apply, Finset.sum_eq_single ⟨p - 1, by omega⟩]
      · rw [huh.1, one_mul]; rfl
      · intro c _ hc
        have : c.val < p - 1 := by have := c.isLt; have : c.val ≠ p - 1 := fun e => hc (Fin.ext e); omega
        rw [huh.2 ⟨p - 1, by omega⟩ c (kU_lt.mpr (Fin.lt_def.mpr this)), zero_mul]
      · simp
    · rw [dif_neg hps, dif_neg hps]

theorem cornerInv : CornerInv := by
  intro p s a b lh uh l u hlh hl huh hu
  rw [lower_iff] at hlh hl
  rw [upper_iff] at huh hu
  obtain ⟨hlhi, -, -⟩ := lowK_inv hlh
  obtain ⟨huhi, -, -⟩ := upK_inv huh
  constructor
  · unfold cornerA
    by_cases hps : 0 < s ∧ 0 < p
    · rw [dif_pos hps, dif_pos hps, Matrix.mul_apply, Finset.sum_eq_single ⟨p - 1, by omega⟩]
      · rw [hlhi.1, mul_one, Matrix.mul_apply, Finset.sum_eq_single ⟨0, hps.1⟩]
        · rw [hl.1, one_mul]; rfl
        · intro c _ hc
          have : 0 < c.val := by have : c.val ≠ 0 := fun e => hc (Fin.ext e); omega
          rw [hl.2 ⟨0, hps.1⟩ c (kL_lt.mpr (Fin.lt_def.mpr this)), zero_mul]
        · simp
      · intro c _ hc
        have : c.val < p - 1 := by have := c.isLt; have : c.val ≠ p - 1 := fun e => hc (Fin.ext e); omega
        rw [hlhi.2 c ⟨p - 1, by omega⟩ (kL_lt.mpr (Fin.lt_def.mpr this)), mul_zero]
      · simp
    · rw [dif_neg hps, dif_neg hps]
  · unfold cornerB
    by_cases hps : 0 < s ∧ 0 < p
    · rw [dif_pos hps, dif_pos hps, Matrix.mul_apply, Finset.sum_eq_single ⟨0, hps.1⟩]
      · rw [hu.1, mul_one, Matrix.mul_apply, Finset.sum_eq_single ⟨p - 1, by omega⟩]
        · rw [huhi.1, one_mul]; rfl
        · intro c _ hc
          have : c.val < p - 1 := by have := c.isLt; have : c.val ≠ p - 1 := fun e => hc (Fin.ext e); omega
          rw [huhi.2 ⟨p - 1, by omega⟩ c (kU_lt.mpr (Fin.lt_def.mpr this)), zero_mul]
        · simp
      · intro c _ hc
        have : 0 < c.val := by have : c.val ≠ 0 := fun e => hc (Fin.ext e); omega
        rw [hu.2 c ⟨0, hps.1⟩ (kU_lt.mpr (Fin.lt_def.mpr this)), mul_zero]
      · simp
    · rw [dif_neg hps, dif_neg hps]

end twoBlocks

end Formalism.FourierDecayAlt.P.Ux2

namespace Formalism.FourierDecayAlt.P

theorem hermitian_group_blocks : Formalism.FourierDecayAlt.U.HpkBlocks := Ux2.hpkBlocks

theorem slice_membership : Formalism.FourierDecayAlt.U.SliceMem := Ux2.sliceMem

theorem radical_parametrisation : Formalism.FourierDecayAlt.U.RadicalParam := Ux2.radicalParam

theorem low_weight_specialisation : Formalism.FourierDecayAlt.U.LowWSpec := Ux2.lowWSpec

theorem head_orbit : Formalism.FourierDecayAlt.U.HeadOrbit := Ux2.headOrbit

theorem character_on_blocks : Formalism.FourierDecayAlt.U.CharBlock := Ux2.charBlock

theorem corner_inverse : Formalism.FourierDecayAlt.U.CornerInv := Ux2.cornerInv

end Formalism.FourierDecayAlt.P
