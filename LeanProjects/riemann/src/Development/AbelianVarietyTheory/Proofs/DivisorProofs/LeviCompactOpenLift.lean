import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine.LeviK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  subst hrs
  set e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i l
    simp [Matrix.mul_apply]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hdet
  intro h0
  rw [h0] at hdet
  simp [Matrix.det_neg] at hdet
  exact absurd hdet.symm (pow_ne_zero _ (by norm_num))

theorem sigma_sigma {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) (a : E) : σ (σ a) = a := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w).1
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]

end GlobalTheory.IndLine.LeviK

namespace GlobalTheory.IndLine.LeviK

theorem blk_mul {R : Type} [CommRing R] {a b : ℕ} (ι : Matrix (Fin a) (Fin b) R) (Q : Matrix (Fin b) (Fin a) R)
    (hQ : Q * ι = 1) (k k' : Matrix (Fin b) (Fin b) R) (h : k * k' = 1) :
    (1 + ι * (k - 1) * Q) * (1 + ι * (k' - 1) * Q) = 1 := by
  have hA : (k - 1) + (k' - 1) + (k - 1) * (k' - 1) = 0 := by
    have : (k - 1) + (k' - 1) + (k - 1) * (k' - 1) = k * k' - 1 := by noncomm_ring
    rw [this, h, sub_self]
  calc (1 + ι * (k - 1) * Q) * (1 + ι * (k' - 1) * Q)
      = 1 + ι * ((k - 1) + (k' - 1) + (k - 1) * (Q * ι) * (k' - 1)) * Q := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
    _ = 1 := by rw [hQ, Matrix.mul_one, hA]; simp

theorem blk_unitary {R : Type} [CommRing R] (c : R →+* R) {a b : ℕ} (ι : Matrix (Fin a) (Fin b) R)
    (Q : Matrix (Fin b) (Fin a) R) (J : Matrix (Fin a) (Fin a) R) (J₁ : Matrix (Fin b) (Fin b) R)
    (h2 : J * ι.map c = Qᵀ * J₁) (h3 : ιᵀ * J = J₁ * Q.map c) (hg : ιᵀ * J * ι.map c = J₁)
    (k : Matrix (Fin b) (Fin b) R) (hk : kᵀ * J₁ * k.map c = J₁) :
    (1 + ι * (k - 1) * Q)ᵀ * J * (1 + ι * (k - 1) * Q).map c = J := by
  have hm : (1 + ι * (k - 1) * Q).map c = 1 + ι.map c * (k.map c - 1) * Q.map c := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c)]
  have ht : (1 + ι * (k - 1) * Q)ᵀ = 1 + Qᵀ * (kᵀ - 1) * ιᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hin : J₁ * (k.map c - 1) + (kᵀ - 1) * J₁ + (kᵀ - 1) * J₁ * (k.map c - 1) = 0 := by
    have : J₁ * (k.map c - 1) + (kᵀ - 1) * J₁ + (kᵀ - 1) * J₁ * (k.map c - 1) = kᵀ * J₁ * k.map c - J₁ := by
      noncomm_ring
    rw [this, hk, sub_self]
  rw [hm, ht]
  calc (1 + Qᵀ * (kᵀ - 1) * ιᵀ) * J * (1 + ι.map c * (k.map c - 1) * Q.map c)
      = J + (J * ι.map c) * (k.map c - 1) * Q.map c + Qᵀ * (kᵀ - 1) * (ιᵀ * J)
          + Qᵀ * (kᵀ - 1) * (ιᵀ * J * ι.map c) * (k.map c - 1) * Q.map c := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
    _ = J + Qᵀ * (J₁ * (k.map c - 1) + (kᵀ - 1) * J₁ + (kᵀ - 1) * J₁ * (k.map c - 1)) * Q.map c := by
        rw [hg, h2, h3]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
        abel
    _ = J := by rw [hin]; simp

end GlobalTheory.IndLine.LeviK

namespace GlobalTheory.IndLine.LeviK

section Proj

variable {K : Type} [Field K] (c : K →+* K) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) K) (J₁ : Matrix (Fin d₁) (Fin d₁) K)
  (ι : Matrix (Fin d) (Fin d₁) K)

def proj : Matrix (Fin d₁) (Fin d) K := (J₁⁻¹)ᵀ * (J * ι.map c)ᵀ

variable {c J J₁ ι}

theorem proj_mul (hg : ιᵀ * J * ι.map c = J₁) (hd : J₁.det ≠ 0) : proj c J J₁ ι * ι = 1 := by
  have h1 : (J * ι.map c)ᵀ * ι = J₁ᵀ := by
    rw [← hg]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [proj, Matrix.mul_assoc, h1, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.transpose_one]

theorem proj_left (hd : J₁.det ≠ 0) : J * ι.map c = (proj c J J₁ ι)ᵀ * J₁ := by
  rw [proj, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), Matrix.mul_one]

theorem proj_right (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = -J i j) (hJ₁ : ∀ i j, c (J₁ j i) = -J₁ i j)
    (hd : J₁.det ≠ 0) : ιᵀ * J = J₁ * (proj c J J₁ ι).map c := by
  have hJs : J.map c = -Jᵀ := by ext i j; simp [hJ]
  have hJ₁s : J₁.map c = -J₁ᵀ := by ext i j; simp [hJ₁]
  have hιs : (ι.map c).map c = ι := by ext i j; simp [hc]
  have h := congrArg (fun M => M.map c) (proj_left (c := c) (J := J) (ι := ι) hd)
  simp only [Matrix.map_mul, hJs, hJ₁s, hιs, Matrix.transpose_map] at h
  have h2 : Jᵀ * ι = ((proj c J J₁ ι).map c)ᵀ * J₁ᵀ := by simpa [Matrix.neg_mul, Matrix.mul_neg] using h
  have h3 := congrArg Matrix.transpose h2
  simpa [Matrix.transpose_mul] using h3

theorem proj_mulVec (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = -J i j) (x : Fin d → K)
    (hx : ∀ u, ((ι *ᵥ u) ⬝ᵥ J *ᵥ fun i => c (x i)) = 0) : proj c J J₁ ι *ᵥ x = 0 := by
  have key : ∀ j, ((J * ι.map c)ᵀ *ᵥ x) j = -c ((ι *ᵥ Pi.single j 1) ⬝ᵥ J *ᵥ fun i => c (x i)) := by
    intro j
    rw [Matrix.mulVec_single_one]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.map_apply, Matrix.col_apply, map_sum, map_mul, hc, hJ]
    simp only [Finset.mul_sum, Finset.sum_mul, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have h0 : (J * ι.map c)ᵀ *ᵥ x = 0 := by
    funext j; rw [key, hx, map_zero, neg_zero]; rfl
  rw [proj, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

end Proj

end GlobalTheory.IndLine.LeviK

namespace GlobalTheory.IndLine.LeviK

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mulVec_incV {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (u : Fin b → E) :
    incM F M *ᵥ incV F u = incV F (M *ᵥ u) := by
  funext i
  simp only [incV, incM]
  rw [RingHom.map_mulVec]
  rfl

theorem incM_mul {a b e : ℕ} (M : Matrix (Fin a) (Fin b) E) (N : Matrix (Fin b) (Fin e) E) :
    incM F (M * N) = incM F M * incM F N := by
  simp only [incM, Matrix.map_mul]

theorem incM_one {a : ℕ} : incM F (1 : Matrix (Fin a) (Fin a) E) = 1 := by
  simp only [incM]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_transpose {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) : (incM F M)ᵀ = incM F Mᵀ := by
  simp only [incM, Matrix.transpose_map]

theorem incM_map_cA (σ : E →ₐ[F] E) {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) :
    (incM F M).map (cA σ) = incM F (M.map σ) := by
  ext i j
  simp [incM, cA, inclR]

theorem incM_mulVec_latHat {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (ι : Matrix (Fin d) (Fin d₁) E)
    (hlow : ∀ u, u ∈ W₁.L ↔ ι *ᵥ u ∈ W.L) : ∀ z ∈ latHat W₁, incM F ι *ᵥ z ∈ latHat W := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha0, hai, u, hu, rfl⟩ := hz
    rw [Matrix.mulVec_smul, incM_mulVec_incV]
    exact AddSubgroup.subset_closure ⟨a, ha0, hai, ι *ᵥ u, (hlow u).1 hu, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z w _ _ hz hw => rw [Matrix.mulVec_add]; exact add_mem hz hw
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end Adelic

end GlobalTheory.IndLine.LeviK

namespace GlobalTheory.IndLine.LeviK

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem blk_latHat {σ : E →ₐ[F] E} {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (Q : Matrix (Fin d₁) (Fin d) E) (hQι : Q * H'.ι = 1)
    (hQx : Q *ᵥ H'.x = 0) (hQy : Q *ᵥ H'.y = 0) (k : Matrix (Fin d₁) (Fin d₁) (AE F E))
    (hk : ∀ z ∈ latHat W₁, k *ᵥ z ∈ latHat W₁) :
    ∀ z ∈ latHat W, (1 + incM F H'.ι * (k - 1) * incM F Q) *ᵥ z ∈ latHat W := by
  have hexp : ∀ z, (1 + incM F H'.ι * (k - 1) * incM F Q) *ᵥ z =
      z + (incM F H'.ι *ᵥ (k *ᵥ (incM F Q *ᵥ z)) - incM F H'.ι *ᵥ (incM F Q *ᵥ z)) := by
    intro z
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub]
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha0, hai, w, hw, rfl⟩ := hz
    obtain ⟨s, t, u, -, -, hu, rfl⟩ := hA.split w hw
    have hQw : Q *ᵥ (s • H'.x + H'.ι *ᵥ u + t • H'.y) = u := by
      rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hQx, hQy,
        Matrix.mulVec_mulVec, hQι, Matrix.one_mulVec]
      simp
    have hg : a • incV F u ∈ latHat W₁ := AddSubgroup.subset_closure ⟨a, ha0, hai, u, hu, rfl⟩
    rw [hexp, Matrix.mulVec_smul, incM_mulVec_incV, hQw]
    refine add_mem (AddSubgroup.subset_closure ⟨a, ha0, hai, _, hw, rfl⟩) (sub_mem ?_ ?_)
    · exact incM_mulVec_latHat H'.ι hA.low _ (hk _ hg)
    · exact incM_mulVec_latHat H'.ι hA.low _ hg
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z w _ _ hz hw => rw [Matrix.mulVec_add]; exact add_mem hz hw
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem det_ne_zero_of_isSkew {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h1 := det_ne_zero_of_hasSig (h.sig w)
  have h2 : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := by rw [RingHom.map_det]; rfl
  intro h0
  apply h1
  rw [Matrix.det_smul, h2, h0, map_zero, mul_zero]

end Main

end GlobalTheory.IndLine.LeviK

namespace GlobalTheory.IndLine.LeviK

theorem levi_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F), ∀ k₁ ∈ KAt σ W₁ v, ∃ m ∈ KAt σ W v, IsLevi (W₁ := W₁) H' 1 k₁ m := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v k₁ hk₁
  have hσ : ∀ a, (σ : E →+* E) ((σ : E →+* E) a) = a := sigma_sigma hB
  have hd : W₁.J.det ≠ 0 := det_ne_zero_of_isSkew hW₁
  have hg : H'.ιᵀ * W.J * H'.ι.map (σ : E →+* E) = W₁.J := hA.gram
  set Q := proj (σ : E →+* E) W.J W₁.J H'.ι with hQdef
  have hQι : Q * H'.ι = 1 := proj_mul hg hd
  have hQl : W.J * H'.ι.map (σ : E →+* E) = Qᵀ * W₁.J := proj_left hd
  have hQr : H'.ιᵀ * W.J = W₁.J * Q.map (σ : E →+* E) := proj_right hσ hW.skew hW₁.skew hd
  have hQx : Q *ᵥ H'.x = 0 := proj_mulVec hσ hW.skew H'.x fun u => by simpa [form] using (hA.orth u).1
  have hQy : Q *ᵥ H'.y = 0 := proj_mulVec hσ hW.skew H'.y fun u => by simpa [form] using (hA.orth u).2
  set ιA := incM F H'.ι
  set QA := incM F Q
  have hQA : QA * ιA = 1 := by rw [← incM_mul, hQι, incM_one]
  have hKK : mat k₁ * mat k₁⁻¹ = 1 := by
    show ((k₁ * k₁⁻¹ : UA σ W₁.J) : GL (Fin d₁) (AE F E)).1 = 1
    simp
  have hKK' : mat k₁⁻¹ * mat k₁ = 1 := by
    show ((k₁⁻¹ * k₁ : UA σ W₁.J) : GL (Fin d₁) (AE F E)).1 = 1
    simp
  set M := 1 + ιA * (mat k₁ - 1) * QA with hM
  set M' := 1 + ιA * (mat k₁⁻¹ - 1) * QA with hM'
  have h1 : M * M' = 1 := blk_mul ιA QA hQA _ _ hKK
  have h2 : M' * M = 1 := blk_mul ιA QA hQA _ _ hKK'
  have hK : (mat k₁)ᵀ * incM F W₁.J * (mat k₁).map (cA σ) = incM F W₁.J := k₁.2
  have hunit : Mᵀ * incM F W.J * M.map (cA σ) = incM F W.J := by
    refine blk_unitary (cA σ).toRingHom ιA QA (incM F W.J) (incM F W₁.J) ?_ ?_ ?_ (mat k₁) hK
    · show incM F W.J * ιA.map (cA σ) = QAᵀ * incM F W₁.J
      rw [incM_map_cA, incM_transpose, ← incM_mul, ← incM_mul]
      exact congrArg (incM F) hQl
    · show ιAᵀ * incM F W.J = incM F W₁.J * QA.map (cA σ)
      rw [incM_map_cA, incM_transpose, ← incM_mul, ← incM_mul]
      exact congrArg (incM F) hQr
    · show ιAᵀ * incM F W.J * ιA.map (cA σ) = incM F W₁.J
      rw [incM_map_cA, incM_transpose, ← incM_mul, ← incM_mul]
      exact congrArg (incM F) hg
  let g : GL (Fin d) (AE F E) := ⟨M, M', h1, h2⟩
  let m : UA σ W.J := ⟨g, hunit⟩
  have hm : mat m = M := rfl
  have hm' : mat m⁻¹ = M' := rfl
  refine ⟨m, ⟨?_, fun z hz => ⟨?_, ?_⟩⟩, ?_, ?_, ?_⟩
  · intro u hu
    show u • (mat m - 1) = 0
    rw [hm, hM, add_sub_cancel_left, ← Matrix.smul_mul, ← Matrix.mul_smul, hk₁.1 u hu, Matrix.mul_zero, Matrix.zero_mul]
  · rw [hm]; exact blk_latHat hA Q hQι hQx hQy _ (fun z hz => (hk₁.2 z hz).1) z hz
  · rw [hm']; exact blk_latHat hA Q hQι hQx hQy _ (fun z hz => by simpa using (hk₁.2 z hz).2) z hz
  · rw [hm, hM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      incM_mulVec_incV, hQx]
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; simp [incV]
    simp [h0]
  · rw [hm, hM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      incM_mulVec_incV, hQy]
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; simp [incV]
    simp [h0]
  · rw [hm, hM, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQA, Matrix.mul_one, Matrix.mul_sub,
      Matrix.mul_one]
    abel

end GlobalTheory.IndLine.LeviK
