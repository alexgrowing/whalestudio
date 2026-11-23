import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreRest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagKey

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.FrameTorus

open Matrix

section Gen

variable {A : Type} [CommRing A] {n q : ℕ}

theorem mul_core (X Y : Matrix (Fin n) (Fin q) A) (RX RY : Matrix (Fin q) (Fin n) A) (a b a' b' : Fin q → A)
    (h1 : RY * X = 1) (h2 : RY * Y = 0) (h3 : RX * X = 0) (h4 : RX * Y = 1)
    (ha : ∀ i, a i + a' i + a i * a' i = 0) (hb : ∀ i, b i + b' i + b i * b' i = 0) :
    (1 + X * diagonal a * RY + Y * diagonal b * RX) * (1 + X * diagonal a' * RY + Y * diagonal b' * RX) = 1 := by
  first
  | exact @_root_.GlobalTheory.AbelianSumIdentityFourth.main
  | exact _root_.GlobalTheory.AbelianSumIdentityFourth.main
  | (apply _root_.GlobalTheory.AbelianSumIdentityFourth.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbelianSumIdentityFourth.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbelianSumIdentityFourth.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbelianSumIdentityFourth.main ..)

end Gen

section Gen2

variable {A : Type} [CommRing A] {n q : ℕ}

theorem unitary_core (J : Matrix (Fin n) (Fin n) A) (X Xc Y Yc : Matrix (Fin n) (Fin q) A) (a b : Fin q → A)
    (h1 : Xᵀ * J * Xc = 0) (h2 : Xᵀ * J * Yc = 1) (h3 : Yᵀ * J * Xc = 1) (h4 : Yᵀ * J * Yc = 0)
    (hab : ∀ i, a i + b i + a i * b i = 0) :
    (1 + J * Yc * diagonal a * Xᵀ + J * Xc * diagonal b * Yᵀ) * J *
      (1 + Xc * diagonal a * (Yᵀ * J) + Yc * diagonal b * (Xᵀ * J)) = J := by
  first
  | exact @_root_.GlobalTheory.DiagonalKeyIdentity.main
  | exact _root_.GlobalTheory.DiagonalKeyIdentity.main
  | (apply _root_.GlobalTheory.DiagonalKeyIdentity.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DiagonalKeyIdentity.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DiagonalKeyIdentity.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DiagonalKeyIdentity.main ..)

theorem unitary_gen (c : A →+* A) (J : Matrix (Fin n) (Fin n) A) (X Xc Y Yc : Matrix (Fin n) (Fin q) A)
    (RX RY : Matrix (Fin q) (Fin n) A) (a b : Fin q → A)
    (hRYt : RYᵀ = J * Yc) (hRXt : RXᵀ = J * Xc) (hXc : X.map c = Xc) (hYc : Y.map c = Yc)
    (hRYc : RY.map c = Yᵀ * J) (hRXc : RX.map c = Xᵀ * J) (hac : ∀ i, c (a i) = a i) (hbc : ∀ i, c (b i) = b i)
    (h1 : Xᵀ * J * Xc = 0) (h2 : Xᵀ * J * Yc = 1) (h3 : Yᵀ * J * Xc = 1) (h4 : Yᵀ * J * Yc = 0)
    (hab : ∀ i, a i + b i + a i * b i = 0) :
    (1 + X * diagonal a * RY + Y * diagonal b * RX)ᵀ * J * (1 + X * diagonal a * RY + Y * diagonal b * RX).map c = J := by
  have hT : (1 + X * diagonal a * RY + Y * diagonal b * RX)ᵀ = 1 + J * Yc * diagonal a * Xᵀ + J * Xc * diagonal b * Yᵀ := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.diagonal_transpose, hRYt, hRXt,
      Matrix.mul_assoc]
  have hC : (1 + X * diagonal a * RY + Y * diagonal b * RX).map c =
      1 + Xc * diagonal a * (Yᵀ * J) + Yc * diagonal b * (Xᵀ * J) := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c),
      Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero c),
      Matrix.diagonal_map (map_zero c), hXc, hYc, hRYc, hRXc]
    simp only [hac, hbc]
  rw [hT, hC]
  exact unitary_core J X Xc Y Yc a b h1 h2 h3 h4 hab

end Gen2

section Conc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem realAd_mul' (a b : ℝ) : realAd F a * realAd F b = realAd F (a * b) := by
  unfold realAd
  simp only [LinearMap.inl_apply, map_mul]
  refine Prod.ext ?_ ?_
  · show _ * _ = _
    rw [← map_mul]
  · exact mul_zero _

theorem realAd_add' (s t : ℝ) : realAd F (s + t) = realAd F s + realAd F t := by
  simp only [realAd, map_add]
  rfl

theorem realAd_zero' : realAd F 0 = 0 := by
  simp only [realAd, map_zero]
  rfl

theorem realAd_key {t : ℝ} (ht : t ≠ 0) :
    realAd F (t - 1) + realAd F (t⁻¹ - 1) + realAd F (t - 1) * realAd F (t⁻¹ - 1) = 0 := by
  rw [realAd_mul', ← realAd_add', ← realAd_add']
  have : t - 1 + (t⁻¹ - 1) + (t - 1) * (t⁻¹ - 1) = 0 := by field_simp; ring
  rw [this, realAd_zero']

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

def colMat {n p : ℕ} (u : Fin p → Fin n → E) : Matrix (Fin n) (Fin p) E := Matrix.of fun k i => u i k

theorem colMat_form (σ : E →ₐ[F] E) {n p p' : ℕ} (J : Matrix (Fin n) (Fin n) E) (u : Fin p → Fin n → E)
    (v : Fin p' → Fin n → E) (i : Fin p) (j : Fin p') :
    ((colMat u)ᵀ * J * (colMat v).map (σ : E →+* E)) i j = form σ J (u i) (v j) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, form, dotProduct, Matrix.mulVec, colMat]

theorem tr_eq {n p p' : ℕ} (s : E →+* E) (J : Matrix (Fin n) (Fin n) E) (U : Matrix (Fin n) (Fin p) E)
    (V : Matrix (Fin n) (Fin p') E) : (V.map s)ᵀ * Jᵀ * U = (Uᵀ * J * V.map s)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end Conc

theorem exists_isTorusU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s → ∀ (q : ℕ) (x y : Fin q → Fin n → E),
    IsFrameU σ X.J x y → ∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a := by
  intro F E _ _ _ _ _ σ B n X r s hB hX q x y hF t ht
  have hσσ := sigma_sigma hB.cm
  set J := X.J with hJdef
  set sg : E →+* E := (σ : E →+* E) with hsg
  set ι : E →+* AE F E := inclR (F := F) (AF F) with hι
  set c : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hc
  have hcι : ∀ e, c (ι e) = ι (sg e) := fun e => cA_inclR σ e
  have hconj : ∀ {p p' : ℕ} (M : Matrix (Fin p) (Fin p') E), (M.map ι).map c = (M.map sg).map ι := by
    intro p p' M; ext i j; simp only [Matrix.map_apply]; exact hcι _
  set Xe := colMat x with hXe
  set Ye := colMat y with hYe
  have hXX : Xeᵀ * J * Xe.map sg = 0 := by ext i j; rw [colMat_form]; exact hF.1 i j
  have hYY : Yeᵀ * J * Ye.map sg = 0 := by ext i j; rw [colMat_form]; exact hF.2.1 i j
  have hXY : Xeᵀ * J * Ye.map sg = 1 := by ext i j; rw [colMat_form, hF.2.2 i j, Matrix.one_apply]
  have hJt : Jᵀ.map sg = J := by ext i j; exact hX.herm i j
  have hss : ∀ {p p' : ℕ} (M : Matrix (Fin p) (Fin p') E), (M.map sg).map sg = M := by
    intro p p' M; ext i j; simp [hsg, hσσ]
  have hYX : Yeᵀ * J * Xe.map sg = 1 := by
    have e : Yeᵀ * J * Xe.map sg = ((Xeᵀ * J * Ye.map sg)ᵀ).map sg := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul, hJt,
        Matrix.transpose_map, hss, Matrix.mul_assoc]
    rw [e, hXY, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]

  set RYe : Matrix (Fin q) (Fin n) E := (Ye.map sg)ᵀ * Jᵀ with hRYe
  set RXe : Matrix (Fin q) (Fin n) E := (Xe.map sg)ᵀ * Jᵀ with hRXe
  have mapι : ∀ {p p' : ℕ} (M : Matrix (Fin p) (Fin n) E) (N : Matrix (Fin n) (Fin p') E), M.map ι * N.map ι = (M * N).map ι :=
    fun M N => (Matrix.map_mul).symm
  have z0 : ∀ {p p' : ℕ}, (0 : Matrix (Fin p) (Fin p') E).map ι = 0 := by intros; exact Matrix.map_zero _ (map_zero _)
  have o1 : ∀ {p : ℕ}, (1 : Matrix (Fin p) (Fin p) E).map ι = 1 := by intros; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : RYe.map ι * Xe.map ι = 1 := by rw [mapι, hRYe, tr_eq, hXY, Matrix.transpose_one, o1]
  have h2 : RYe.map ι * Ye.map ι = 0 := by rw [mapι, hRYe, tr_eq, hYY, Matrix.transpose_zero, z0]
  have h3 : RXe.map ι * Xe.map ι = 0 := by rw [mapι, hRXe, tr_eq, hXX, Matrix.transpose_zero, z0]
  have h4 : RXe.map ι * Ye.map ι = 1 := by rw [mapι, hRXe, tr_eq, hYX, Matrix.transpose_one, o1]
  set al : (Fin q → ℝ) → Fin q → AE F E := fun t i => algebraMap (AF F) (AE F E) (realAd F (t i - 1)) with hal
  have key : ∀ u : Fin q → ℝ, (∀ i, u i ≠ 0) → ∀ i, al u i + al (fun i => (u i)⁻¹) i + al u i * al (fun i => (u i)⁻¹) i = 0 := by
    intro u hu i
    simp only [hal, ← map_add, ← map_mul, realAd_key (hu i), map_zero]
  set M : (Fin q → ℝ) → Matrix (Fin n) (Fin n) (AE F E) := fun u =>
    1 + Xe.map ι * diagonal (al u) * RYe.map ι + Ye.map ι * diagonal (al (fun i => (u i)⁻¹)) * RXe.map ι with hM
  have ht0 : ∀ i, t i ≠ 0 := fun i => (ht i).ne'
  have ht0' : ∀ i, (fun i => (t i)⁻¹) i ≠ 0 := fun i => inv_ne_zero (ht0 i)
  have hinv : M t * M (fun i => (t i)⁻¹) = 1 :=
    mul_core _ _ _ _ _ _ _ _ h1 h2 h3 h4 (key t ht0) (key _ ht0')

  have hmem : (⟨M t, M (fun i => (t i)⁻¹), hinv, (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) (AE F E) rfl).mp hinv⟩ : GL (Fin n) (AE F E)) ∈
      UG (cA σ) (incM F X.J) := by
    show (M t)ᵀ * J.map ι * (M t).map c = J.map ι
    refine unitary_gen c (J.map ι) (Xe.map ι) ((Xe.map sg).map ι) (Ye.map ι) ((Ye.map sg).map ι) (RXe.map ι) (RYe.map ι)
      (al t) (al (fun i => (t i)⁻¹)) ?_ ?_ (hconj Xe) (hconj Ye) ?_ ?_ (fun i => (cA σ).commutes _) (fun i => (cA σ).commutes _)
      ?_ ?_ ?_ ?_ (key t ht0)
    · rw [← Matrix.transpose_map, hRYe, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
        Matrix.map_mul]
    · rw [← Matrix.transpose_map, hRXe, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
        Matrix.map_mul]
    · rw [hconj, hRYe, Matrix.map_mul, hJt, Matrix.transpose_map, hss, Matrix.map_mul, Matrix.transpose_map]
    · rw [hconj, hRXe, Matrix.map_mul, hJt, Matrix.transpose_map, hss, Matrix.map_mul, Matrix.transpose_map]
    · rw [← Matrix.transpose_map, mapι, mapι, hXX, z0]
    · rw [← Matrix.transpose_map, mapι, mapι, hXY, o1]
    · rw [← Matrix.transpose_map, mapι, mapι, hYX, o1]
    · rw [← Matrix.transpose_map, mapι, mapι, hYY, z0]

  have hM1 : M t - 1 = Xe.map ι * diagonal (al t) * RYe.map ι + Ye.map ι * diagonal (al (fun i => (t i)⁻¹)) * RXe.map ι := by
    simp only [hM]; abel
  have col : ∀ (N : Matrix (Fin n) (Fin n) (AE F E)) {p : ℕ} (Z : Matrix (Fin n) (Fin p) (AE F E)) (i : Fin p),
      N *ᵥ (fun k => Z k i) = fun k => (N * Z) k i := by
    intro N p Z i; funext k; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine ⟨⟨_, hmem⟩, fun i => ?_, fun i => ?_, fun z hzx hzy => ?_⟩
  · have hx : incV F (x i) = fun k => (Xe.map ι) k i := rfl
    have e : (M t - 1) * Xe.map ι = Xe.map ι * diagonal (al t) := by
      rw [hM1]; simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3, Matrix.mul_one, Matrix.mul_zero, add_zero]
    show (M t - 1) *ᵥ incV F (x i) = _
    rw [hx, col, e]
    funext k
    simp [Matrix.mul_diagonal, Algebra.smul_def, hal, mul_comm]
  · have hy : incV F (y i) = fun k => (Ye.map ι) k i := rfl
    have e : (M t - 1) * Ye.map ι = Ye.map ι * diagonal (al (fun i => (t i)⁻¹)) := by
      rw [hM1]; simp only [Matrix.add_mul, Matrix.mul_assoc, h2, h4, Matrix.mul_one, Matrix.mul_zero, zero_add]
    show (M t - 1) *ᵥ incV F (y i) = _
    rw [hy, col, e]
    funext k
    simp [Matrix.mul_diagonal, Algebra.smul_def, hal, mul_comm]
  · set Ze := colMat (fun _ : Fin 1 => z) with hZe
    have hz : incV F z = fun k => (Ze.map ι) k 0 := rfl
    have hYZ : RYe.map ι * Ze.map ι = 0 := by
      have e0 : Zeᵀ * J * Ye.map sg = 0 := by ext i j; rw [colMat_form]; exact hzy j
      rw [mapι, hRYe, tr_eq, e0, Matrix.transpose_zero, z0]
    have hXZ : RXe.map ι * Ze.map ι = 0 := by
      have e0 : Zeᵀ * J * Xe.map sg = 0 := by ext i j; rw [colMat_form]; exact hzx j
      rw [mapι, hRXe, tr_eq, e0, Matrix.transpose_zero, z0]
    have e : (M t - 1) * Ze.map ι = 0 := by
      rw [hM1]; simp only [Matrix.add_mul, Matrix.mul_assoc, hYZ, hXZ, Matrix.mul_zero, add_zero]
    show (M t - 1) *ᵥ incV F z = 0
    rw [hz, col, e]
    rfl

end GlobalTheory.FrameTorus
