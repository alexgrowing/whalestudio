import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviCont

def cols {n₁ : ℕ} {A : Type} (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) A) (x y : Fin (n₁ + 2) → A) :
    Fin (n₁ + 2) → Fin (n₁ + 2) → A :=
  Fin.snoc (α := fun _ => Fin (n₁ + 2) → A) (Fin.snoc (α := fun _ => Fin (n₁ + 2) → A) (fun j i => ι i j) x) y

def colMat {n₁ : ℕ} {A : Type} (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) A) (x y : Fin (n₁ + 2) → A) :
    Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) A :=
  (Matrix.of (cols ι x y))ᵀ

theorem colMat_mulVec {n₁ : ℕ} {A : Type} [CommRing A] (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) A) (x y : Fin (n₁ + 2) → A)
    (c : Fin (n₁ + 2) → A) :
    colMat ι x y *ᵥ c = ι *ᵥ (fun j => c (Fin.castSucc (Fin.castSucc j))) + c (Fin.castSucc (Fin.last n₁)) • x +
      c (Fin.last (n₁ + 1)) • y := by
  ext i
  simp [colMat, cols, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]

theorem mul_colMat {n₁ : ℕ} {A : Type} [CommRing A] (T : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) A)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) A) (x y : Fin (n₁ + 2) → A) :
    T * colMat ι x y = colMat (T * ι) (T *ᵥ x) (T *ᵥ y) := by
  ext i k
  refine Fin.lastCases ?_ (fun k => Fin.lastCases ?_ (fun j => ?_) k) k <;>
    simp [colMat, cols, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem colMat_map {n₁ : ℕ} {A A' : Type} (f : A → A') (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) A) (x y : Fin (n₁ + 2) → A) :
    (colMat ι x y).map f = colMat (ι.map f) (fun i => f (x i)) (fun i => f (y i)) := by
  ext i k
  refine Fin.lastCases ?_ (fun k => Fin.lastCases ?_ (fun j => ?_) k) k <;> simp [colMat, cols]

theorem continuous_colMat {n₁ : ℕ} {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (C : Matrix (Fin (n₁ + 2)) (Fin n₁) A) (x y : Fin (n₁ + 2) → A) :
    Continuous fun M : Matrix (Fin n₁) (Fin n₁) A => colMat (C * M) x y := by
  have hC : Continuous fun M : Matrix (Fin n₁) (Fin n₁) A => C * M := continuous_const.matrix_mul continuous_id
  refine continuous_pi fun i => continuous_pi fun k => ?_
  refine Fin.lastCases ?_ (fun k => Fin.lastCases ?_ (fun j => ?_) k) k
  · simp only [colMat, cols, Matrix.transpose_apply, Matrix.of_apply, Fin.snoc_last]; exact continuous_const
  · simp only [colMat, cols, Matrix.transpose_apply, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last]; exact continuous_const
  · simp only [colMat, cols, Matrix.transpose_apply, Matrix.of_apply, Fin.snoc_castSucc]; exact hC.matrix_elem i j

section Indep

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → E) :
    form σ J (v + v') w = form σ J v w + form σ J v' w := by
  simp [form, add_dotProduct]

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (v w : Fin n → E) :
    form σ J (s • v) w = s * form σ J v w := by
  simp [form, smul_dotProduct]

theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → E) :
    form σ J v (w + w') = form σ J v w + form σ J v w' := by
  unfold form
  rw [show (fun i => σ ((w + w') i)) = (fun i => σ (w i)) + (fun i => σ (w' i)) from funext fun i => by simp,
    Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (v w : Fin n → E) :
    form σ J v (s • w) = σ s * form σ J v w := by
  unfold form
  rw [show (fun i => σ ((s • w) i)) = σ s • (fun i => σ (w i)) from funext fun i => by simp,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_mulVec (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (u' u : Fin n₁ → E) :
    form σ J (ι *ᵥ u') (ι *ᵥ u) = u' ⬝ᵥ (ιᵀ * J * ι.map σ) *ᵥ (fun j => σ (u j)) := by
  unfold form
  have h1 : (fun i => σ ((ι *ᵥ u) i)) = ι.map σ *ᵥ (fun j => σ (u j)) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum]
  rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec u' ιᵀ, Matrix.vecMul_transpose]

theorem det_colMat_ne_zero (σ : E →ₐ[F] E) {n₁ : ℕ} (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E)
    (J₁ : Matrix (Fin n₁) (Fin n₁) E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E) (x y : Fin (n₁ + 2) → E)
    (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hgram : ιᵀ * J * ι.map σ = J₁) (hJ₁ : J₁.det ≠ 0) : (colMat ι x y).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [colMat_mulVec] at hc
  set u : Fin n₁ → E := fun j => c (Fin.castSucc (Fin.castSucc j)) with hu_def
  set a := c (Fin.castSucc (Fin.last n₁)) with ha_def
  set b := c (Fin.last (n₁ + 1)) with hb_def
  have hzero : ∀ w, form σ J 0 w = 0 := fun w => by simp [form]
  have hzero' : ∀ v, form σ J v 0 = 0 := fun v => by
    unfold form; simp only [Pi.zero_apply, map_zero]
    rw [show (fun _ : Fin (n₁ + 2) => (0 : E)) = 0 from rfl, Matrix.mulVec_zero, dotProduct_zero]
  have ha : a = 0 := by
    have h := congrArg (fun v => form σ J v y) hc
    simp only [form_add_left, form_smul_left, (horth u).2, hxy, hyy, hzero] at h
    simpa using h
  have hu : u = 0 := by
    have h : ∀ u', u' ⬝ᵥ J₁ *ᵥ (fun j => σ (u j)) = 0 := by
      intro u'
      have h := congrArg (fun v => form σ J (ι *ᵥ u') v) hc
      simp only [form_add_right, form_smul_right, (horth u').1, (horth u').2, hzero', mul_zero, add_zero,
        form_mulVec, hgram] at h
      exact h
    have hz : J₁ *ᵥ (fun j => σ (u j)) = 0 := by
      funext j
      have := h (Pi.single j 1)
      simpa using this
    have hσu := Matrix.eq_zero_of_mulVec_eq_zero hJ₁ hz
    funext j
    have := congrFun hσu j
    simpa using this
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [hzero'] at hxy
    exact zero_ne_one hxy
  have hb : b = 0 := by
    rw [hu, ha] at hc
    simp only [Matrix.mulVec_zero, zero_smul, zero_add] at hc
    exact (smul_eq_zero.mp hc).resolve_right hy0
  apply hc0
  funext k
  refine Fin.lastCases ?_ (fun k => Fin.lastCases ?_ (fun j => ?_) k) k
  · exact hb
  · exact ha
  · exact congrFun hu j

end Indep

theorem eq_colMat_mul {A : Type} [CommRing A] {n₁ : ℕ} (Q R : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) A) (hQR : Q * R = 1)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) A) (x y : Fin (n₁ + 2) → A) (hQ : Q = colMat ι x y)
    (T : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) A) (Mh : Matrix (Fin n₁) (Fin n₁) A)
    (hx : T *ᵥ x = x) (hy : T *ᵥ y = y) (hι : T * ι = ι * Mh) : T = colMat (ι * Mh) x y * R := by
  calc T = T * (Q * R) := by rw [hQR, Matrix.mul_one]
    _ = (T * Q) * R := by rw [Matrix.mul_assoc]
    _ = _ := by rw [hQ, mul_colMat, hx, hy, hι]

theorem mulVec_inv {A : Type} [CommRing A] {m : ℕ} (T T' : Matrix (Fin m) (Fin m) A) (hTT : T' * T = 1)
    (v : Fin m → A) (hv : T *ᵥ v = v) : T' *ᵥ v = v := by
  calc T' *ᵥ v = T' *ᵥ (T *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, hTT, Matrix.one_mulVec]

theorem mul_inv_intertwine {A : Type} [CommRing A] {m n₁ : ℕ} (T T' : Matrix (Fin m) (Fin m) A)
    (Mh Mh' : Matrix (Fin n₁) (Fin n₁) A) (ι : Matrix (Fin m) (Fin n₁) A) (hTT : T' * T = 1) (hMM : Mh * Mh' = 1)
    (hι : T * ι = ι * Mh) : T' * ι = ι * Mh' := by
  calc T' * ι = T' * ι * (Mh * Mh') := by rw [hMM, Matrix.mul_one]
    _ = T' * (ι * Mh) * Mh' := by simp only [Matrix.mul_assoc]
    _ = T' * T * ι * Mh' := by rw [← hι]; simp only [Matrix.mul_assoc]
    _ = ι * Mh' := by rw [hTT, Matrix.one_mul]

theorem continuous_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' r₁ s₁ : ℕ),
    W.IsSkew σ B r' s' → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ f : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi H' 1 h₁ (f h₁)) → Continuous f := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hW hW₁ hH f hf
  have hrank := hH.rank
  subst hrank
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hJ₁ : W₁.J.det ≠ 0 := GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B d₁ r₁ s₁ W₁ hW₁
  set P := colMat H'.ι H'.x H'.y with hP
  have hdet : P.det ≠ 0 :=
    det_colMat_ne_zero σ W.J W₁.J H'.ι H'.x H'.y hH.yy hH.xy hH.orth hH.gram hJ₁
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hdet)
  have hQR : incM F P * incM F P⁻¹ = 1 := by
    unfold incM
    rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ : incM F P = colMat (incM F H'.ι) (incV F H'.x) (incV F H'.y) := by
    unfold incM incV
    rw [hP, colMat_map]
  have hlevi : ∀ (T : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) (AE F E)) (Mh : Matrix (Fin d₁) (Fin d₁) (AE F E)),
      T *ᵥ incV F H'.x = incV F H'.x → T *ᵥ incV F H'.y = incV F H'.y → T * incM F H'.ι = incM F H'.ι * Mh →
      T = colMat (incM F H'.ι * Mh) (incV F H'.x) (incV F H'.y) * incM F P⁻¹ :=
    fun T Mh hx hy hι => eq_colMat_mul _ _ hQR _ _ _ hQ T Mh hx hy hι
  have hcont := continuous_colMat (incM F H'.ι) (incV F H'.x) (incV F H'.y)
  have hval : Continuous fun h₁ : UA σ W₁.J => mat h₁ := Units.continuous_val.comp continuous_subtype_val
  have hinv : Continuous fun h₁ : UA σ W₁.J => (((h₁ : GL (Fin d₁) (AE F E))⁻¹ : GL (Fin d₁) (AE F E)) :
      Matrix (Fin d₁) (Fin d₁) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hx1 : ∀ h₁, mat (f h₁) *ᵥ incV F H'.x = incV F H'.x := fun h₁ => by simpa using (hf h₁).1
  have hy1 : ∀ h₁, mat (f h₁) *ᵥ incV F H'.y = incV F H'.y := fun h₁ => by simpa using (hf h₁).2.1
  have hι1 : ∀ h₁, mat (f h₁) * incM F H'.ι = incM F H'.ι * mat h₁ := fun h₁ => (hf h₁).2.2
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · have heq : (Units.val ∘ Subtype.val ∘ f) =
        fun h₁ => colMat (incM F H'.ι * mat h₁) (incV F H'.x) (incV F H'.y) * incM F P⁻¹ :=
      funext fun h₁ => hlevi _ _ (hx1 h₁) (hy1 h₁) (hι1 h₁)
    rw [heq]
    exact (hcont.comp hval).matrix_mul continuous_const
  · have heq : (fun h₁ => (((Subtype.val ∘ f) h₁)⁻¹ : GL (Fin (d₁ + 2)) (AE F E)).val) =
        fun h₁ : UA σ W₁.J => colMat (incM F H'.ι * (((h₁ : GL (Fin d₁) (AE F E))⁻¹ : GL (Fin d₁) (AE F E)) :
          Matrix (Fin d₁) (Fin d₁) (AE F E))) (incV F H'.x) (incV F H'.y) * incM F P⁻¹ := by
      funext h₁
      have hTT : ((((f h₁ : GL (Fin (d₁ + 2)) (AE F E)))⁻¹ : GL (Fin (d₁ + 2)) (AE F E)) :
          Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) (AE F E)) * mat (f h₁) = 1 :=
        Units.inv_mul _
      have hMM : mat h₁ * (((h₁ : GL (Fin d₁) (AE F E))⁻¹ : GL (Fin d₁) (AE F E)) :
          Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1 := Units.mul_inv _
      exact hlevi _ _ (mulVec_inv _ _ hTT _ (hx1 h₁)) (mulVec_inv _ _ hTT _ (hy1 h₁))
        (mul_inv_intertwine _ _ _ _ _ hTT hMM (hι1 h₁))
    rw [heq]
    exact (hcont.comp hinv).matrix_mul continuous_const

end GlobalTheory.LeviCont
