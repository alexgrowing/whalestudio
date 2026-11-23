import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section
namespace GlobalTheory.LeviK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_det {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply]
  have hd := congrArg Matrix.det this
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_neg] at hd
  intro h0; rw [h0] at hd; simp at hd; exact absurd hd.symm (pow_ne_zero _ (by norm_num))

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨_, _, _, hc⟩ := h
  let τ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
  apply τ.injective
  rw [hc, hc, star_star]

theorem skew_det {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (h : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  let w := Classical.arbitrary (InfinitePlace F)
  have hd := sig_det (h.sig w)
  rw [Matrix.det_smul] at hd
  intro h0; apply hd
  have hm : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := (RingHom.map_det _ W.J).symm
  rw [hm, h0]; simp

theorem form_skew {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin d → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem map_skew {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) : J.map σ = -Jᵀ := by
  ext i j; simp [hJ j i]

section Mat
variable {σ : E →ₐ[F] E} {d d₁ : ℕ}

def proj (σ : E →ₐ[F] E) (J : Matrix (Fin d) (Fin d) E) (J₁ : Matrix (Fin d₁) (Fin d₁) E) (ι : Matrix (Fin d) (Fin d₁) E) :
    Matrix (Fin d₁) (Fin d) E := J₁ᵀ⁻¹ * (ι.map σ)ᵀ * Jᵀ

variable {J : Matrix (Fin d) (Fin d) E} {J₁ : Matrix (Fin d₁) (Fin d₁) E} {ι : Matrix (Fin d) (Fin d₁) E}

theorem proj_mul (h1 : J₁.det ≠ 0) (hg : ιᵀ * J * ι.map σ = J₁) : proj σ J J₁ ι * ι = 1 := by
  have : (ι.map σ)ᵀ * Jᵀ * ι = J₁ᵀ := by rw [← hg]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [proj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ Jᵀ, this]
  exact Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact h1.isUnit)

theorem proj_mulVec (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = -J i j) {x : Fin d → E}
    (hx : ∀ u, form σ J (ι *ᵥ u) x = 0) : proj σ J J₁ ι *ᵥ x = 0 := by
  have : (ι.map σ)ᵀ *ᵥ (Jᵀ *ᵥ x) = 0 := by
    ext j
    have h := hx (Pi.single j 1)
    rw [form_skew hσ hJ] at h
    have h' : form σ J x (ι *ᵥ Pi.single j 1) = 0 := by
      have := congrArg σ h; rw [map_neg, hσ, map_zero] at this; exact neg_eq_zero.mp this
    rw [Pi.zero_apply, ← h']
    simp only [form, Matrix.mulVec_single_one, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]
    simp [Matrix.vecMul, dotProduct, Matrix.col]
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [proj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero]

theorem proj_transpose_mul (h1 : J₁.det ≠ 0) : (proj σ J J₁ ι)ᵀ * J₁ = J * ι.map σ := by
  rw [proj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.transpose_transpose]
  simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h1.isUnit]

theorem mul_proj_map (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = -J i j) (hJ₁ : ∀ i j, σ (J₁ j i) = -J₁ i j)
    (h1 : J₁.det ≠ 0) : J₁ * (proj σ J J₁ ι).map σ = ιᵀ * J := by
  have mm : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (C : Matrix (Fin b) (Fin c) E), (A * C).map σ = A.map σ * C.map σ :=
    fun A C => Matrix.map_mul (f := (σ : E →+* E))
  have h : ((proj σ J J₁ ι)ᵀ * J₁).map σ = (J * ι.map σ).map σ := by rw [proj_transpose_mul h1]
  rw [mm, mm] at h
  have hιι : (ι.map σ).map σ = ι := by ext i j; simp [hσ]
  rw [hιι, map_skew hJ, map_skew hJ₁, Matrix.transpose_map] at h
  have h2 := congrArg Matrix.transpose h
  simp only [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h2
  exact h2
end Mat

section Gen
variable {R : Type} [CommRing R] (c : R →+* R) {d d₁ : ℕ}

theorem map_mul' {a b e : ℕ} (A : Matrix (Fin a) (Fin b) R) (C : Matrix (Fin b) (Fin e) R) : (A * C).map c = A.map c * C.map c :=
  Matrix.map_mul

def lev (I : Matrix (Fin d) (Fin d₁) R) (Q : Matrix (Fin d₁) (Fin d) R) (D : Matrix (Fin d₁) (Fin d₁) R) : Matrix (Fin d) (Fin d) R :=
  1 + I * (D * Q)

theorem lev_mul (I : Matrix (Fin d) (Fin d₁) R) (Q : Matrix (Fin d₁) (Fin d) R) (hQI : Q * I = 1) (D D' : Matrix (Fin d₁) (Fin d₁) R) :
    lev I Q D * lev I Q D' = lev I Q (D + D' + D * D') := by
  simp only [lev, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q I, hQI, Matrix.one_mul]
  abel

theorem lev_unitary (J : Matrix (Fin d) (Fin d) R) (J₁ : Matrix (Fin d₁) (Fin d₁) R) (I : Matrix (Fin d) (Fin d₁) R)
    (Q : Matrix (Fin d₁) (Fin d) R) (h3 : J * I.map c = Qᵀ * J₁) (h4 : Iᵀ * J = J₁ * Q.map c) (hg : Iᵀ * J * I.map c = J₁)
    (D : Matrix (Fin d₁) (Fin d₁) R) (hD : (1 + D)ᵀ * J₁ * (1 + D).map c = J₁) :
    (lev I Q D)ᵀ * J * (lev I Q D).map c = J := by
  have h3' : ∀ {e : ℕ} (X : Matrix (Fin d₁) (Fin e) R), J * (I.map c * X) = Qᵀ * (J₁ * X) := fun X => by
    rw [← Matrix.mul_assoc, h3, Matrix.mul_assoc]
  have h4' : ∀ {e : ℕ} (X : Matrix (Fin d) (Fin e) R), Iᵀ * (J * X) = J₁ * (Q.map c * X) := fun X => by
    rw [← Matrix.mul_assoc, h4, Matrix.mul_assoc]
  have hg' : ∀ {e : ℕ} (X : Matrix (Fin d₁) (Fin e) R), Iᵀ * (J * (I.map c * X)) = J₁ * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  have hm1 : (1 : Matrix (Fin d) (Fin d) R).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have hm1' : (1 : Matrix (Fin d₁) (Fin d₁) R).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have hD' : J₁ * D.map c + Dᵀ * J₁ + Dᵀ * (J₁ * D.map c) = 0 := by
    rw [Matrix.map_add c (map_add c), hm1', Matrix.transpose_add, Matrix.transpose_one] at hD
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc] at hD
    have := congrArg (· - J₁) hD; simp only [add_sub_cancel_right, sub_self] at this
    rw [← this]; abel
  simp only [lev, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.map_add c (map_add c), hm1, map_mul',
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [hg', h3', h4]
  have : Qᵀ * (J₁ * (D.map c * Q.map c)) + Qᵀ * (Dᵀ * (J₁ * (Q.map c))) + Qᵀ * (Dᵀ * (J₁ * (D.map c * Q.map c))) = 0 := by
    rw [← Matrix.mul_add, ← Matrix.mul_add]
    simp only [← Matrix.mul_assoc]
    rw [← Matrix.add_mul, ← Matrix.add_mul]
    simp only [Matrix.mul_assoc] at hD' ⊢
    rw [hD', Matrix.zero_mul, Matrix.mul_zero]
  rw [← sub_eq_zero, ← this]; abel
end Gen

section Adelic
variable {σ : E →ₐ[F] E}

theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem incM_mul {a b e : ℕ} (A : Matrix (Fin a) (Fin b) E) (C : Matrix (Fin b) (Fin e) E) :
    incM F (A * C) = incM F A * incM F C := Matrix.map_mul

theorem incM_one {a : ℕ} : incM F (1 : Matrix (Fin a) (Fin a) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_transpose {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) : incM F Aᵀ = (incM F A)ᵀ := (Matrix.transpose_map).symm

theorem incM_map {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j; simp [incM, cA_inclR]

theorem incM_mulVec {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) (x : Fin b → E) : incM F A *ᵥ incV F x = incV F (A *ᵥ x) := by
  funext i; exact (RingHom.map_mulVec (inclR (F := F) (AF F)) A x i).symm

theorem incV_zero {a : ℕ} : incV F (0 : Fin a → E) = 0 := by funext i; simp [incV]

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) : mat k * mat k⁻¹ = 1 := by
  simp [mat]

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) : mat k⁻¹ * mat k = 1 := by
  simp [mat]

theorem mat_unitary {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) : (mat k)ᵀ * incM F J * (mat k).map (cA σ) = incM F J :=
  k.2
end Adelic

section Pt
variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {J : Matrix (Fin d) (Fin d) E} {J₁ : Matrix (Fin d₁) (Fin d₁) E}

def leviPt (I : Matrix (Fin d) (Fin d₁) (AE F E)) (Q : Matrix (Fin d₁) (Fin d) (AE F E)) (hQI : Q * I = 1)
    (hu : ∀ D, (1 + D)ᵀ * incM F J₁ * (1 + D).map (cA σ) = incM F J₁ →
      (lev I Q D)ᵀ * incM F J * (lev I Q D).map (cA σ) = incM F J) (k : UA σ J₁) : UA σ J :=
  ⟨⟨lev I Q (mat k - 1), lev I Q (mat k⁻¹ - 1),
    by
      rw [lev_mul I Q hQI, show mat k - 1 + (mat k⁻¹ - 1) + (mat k - 1) * (mat k⁻¹ - 1) = mat k * mat k⁻¹ - 1 by noncomm_ring,
        mat_mul_inv, sub_self]
      simp [lev],
    by
      rw [lev_mul I Q hQI, show mat k⁻¹ - 1 + (mat k - 1) + (mat k⁻¹ - 1) * (mat k - 1) = mat k⁻¹ * mat k - 1 by noncomm_ring,
        mat_inv_mul, sub_self]
      simp [lev]⟩,
    hu _ (by rw [add_sub_cancel]; exact mat_unitary k)⟩

theorem mat_leviPt (I : Matrix (Fin d) (Fin d₁) (AE F E)) (Q : Matrix (Fin d₁) (Fin d) (AE F E)) (hQI : Q * I = 1) hu (k : UA σ J₁) :
    mat (leviPt (J := J) I Q hQI hu k) = lev I Q (mat k - 1) := rfl

theorem mat_leviPt_inv (I : Matrix (Fin d) (Fin d₁) (AE F E)) (Q : Matrix (Fin d₁) (Fin d) (AE F E)) (hQI : Q * I = 1) hu (k : UA σ J₁) :
    mat (leviPt (J := J) I Q hQI hu k)⁻¹ = lev I Q (mat k⁻¹ - 1) := rfl
end Pt

section Lat
variable {a b : ℕ}

theorem latHat_map {X : Spc F E a} {Y : Spc F E b} (A : Matrix (Fin b) (Fin a) E) (hA : ∀ x ∈ X.L, A *ᵥ x ∈ Y.L) :
    ∀ z ∈ latHat X, incM F A *ᵥ z ∈ latHat Y := by
  intro z hz
  have : latHat X ≤ (latHat Y).comap (Matrix.mulVecLin (incM F A)).toAddMonoidHom := by
    refine AddSubgroup.closure_le _ |>.2 ?_
    rintro _ ⟨c, hc1, hc2, x, hx, rfl⟩
    show incM F A *ᵥ (c • incV F x) ∈ latHat Y
    rw [Matrix.mulVec_smul, incM_mulVec]
    exact AddSubgroup.subset_closure ⟨c, hc1, hc2, _, hA x hx, rfl⟩
  exact this hz
end Lat

theorem levi_of_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    ∀ k₁ ∈ KAt σ W₁ v, ∃ m ∈ KAt σ W v, IsLevi H' 1 k₁ m := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hH v k₁ hk₁
  have hσ := sigma_invol hB.cm
  have h1 := skew_det hW₁
  have hQI : incM F (proj σ W.J W₁.J H'.ι) * incM F H'.ι = 1 := by rw [← incM_mul, proj_mul h1 hH.gram, incM_one]
  have hgA : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map (cA σ) = incM F W₁.J := by
    rw [← incM_transpose, incM_map, ← incM_mul, ← incM_mul, hH.gram]
  have h3A : incM F W.J * (incM F H'.ι).map (cA σ) = (incM F (proj σ W.J W₁.J H'.ι))ᵀ * incM F W₁.J := by
    rw [incM_map, ← incM_mul, ← incM_transpose, ← incM_mul, proj_transpose_mul h1]
  have h4A : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F (proj σ W.J W₁.J H'.ι)).map (cA σ) := by
    rw [incM_map, ← incM_transpose, ← incM_mul, ← incM_mul, mul_proj_map hσ hW.skew hW₁.skew h1]
  have hu : ∀ D, (1 + D)ᵀ * incM F W₁.J * (1 + D).map (cA σ) = incM F W₁.J →
      (lev (incM F H'.ι) (incM F (proj σ W.J W₁.J H'.ι)) D)ᵀ * incM F W.J *
        (lev (incM F H'.ι) (incM F (proj σ W.J W₁.J H'.ι)) D).map (cA σ) = incM F W.J :=
    fun D hD => lev_unitary (cA σ).toRingHom _ _ _ _ h3A h4A hgA D hD
  have hx : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 := fun u => (hH.orth u).1
  have hy : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.y = 0 := fun u => (hH.orth u).2
  have hQ0 : ∀ z ∈ W.L, proj σ W.J W₁.J H'.ι *ᵥ z ∈ W₁.L := by
    intro z hz
    obtain ⟨a, b, u, -, -, hu1, rfl⟩ := hH.split z hz
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, proj_mulVec hσ hW.skew hx,
      proj_mulVec hσ hW.skew hy, Matrix.mulVec_mulVec, proj_mul h1 hH.gram, Matrix.one_mulVec]
    simpa using hu1
  have hQl := latHat_map (X := W) (Y := W₁) _ hQ0
  have hIl := latHat_map (X := W₁) (Y := W) H'.ι (fun u hu1 => (hH.low u).1 hu1)
  have hlat : ∀ K : Matrix (Fin d₁) (Fin d₁) (AE F E), (∀ w ∈ latHat W₁, K *ᵥ w ∈ latHat W₁) →
      ∀ z ∈ latHat W, lev (incM F H'.ι) (incM F (proj σ W.J W₁.J H'.ι)) (K - 1) *ᵥ z ∈ latHat W := by
    intro K hK z hz
    simp only [lev, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub]
    have hq := hQl z hz
    exact add_mem hz (sub_mem (hIl _ (hK _ hq)) (hIl _ hq))
  refine ⟨leviPt _ _ hQI hu k₁, ⟨?_, fun z hz => ⟨?_, ?_⟩⟩, ?_, ?_, ?_⟩
  · intro u hu0
    show u • (lev (incM F H'.ι) (incM F (proj σ W.J W₁.J H'.ι)) (mat k₁ - 1) - 1) = 0
    rw [lev, add_sub_cancel_left, ← Matrix.mul_smul, ← Matrix.smul_mul, hk₁.1 u hu0]
    simp
  · rw [mat_leviPt]; exact hlat _ (fun w hw => (hk₁.2 w hw).1) z hz
  · rw [mat_leviPt_inv]; exact hlat _ (fun w hw => (hk₁.2 w hw).2) z hz
  · rw [Units.val_one, one_smul, mat_leviPt]
    simp only [lev, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    rw [incM_mulVec, proj_mulVec hσ hW.skew hx, incV_zero, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  · rw [inv_one, Units.val_one, map_one, one_smul, mat_leviPt]
    simp only [lev, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    rw [incM_mulVec, proj_mulVec hσ hW.skew hy, incV_zero, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  · rw [mat_leviPt]
    simp only [lev, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQI, Matrix.mul_one, Matrix.mul_sub]
    abel

end GlobalTheory.LeviK
