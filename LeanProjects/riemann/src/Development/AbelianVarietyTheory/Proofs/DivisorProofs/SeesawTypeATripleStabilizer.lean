import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviQuot

open Matrix

section Lin

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n b : ℕ}

def cvec (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : Fin n → E := J *ᵥ fun i => σ (x i)

def coef (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin b) E) (J₁ : Matrix (Fin b) (Fin b) E) :
    Matrix (Fin b) (Fin n) E :=
  (J₁ᵀ)⁻¹ * ((ι.map σ)ᵀ * Jᵀ)

theorem form_eq_dot (J : Matrix (Fin n) (Fin n) E) (u x : Fin n → E) : form σ J u x = cvec σ J x ⬝ᵥ u := by
  rw [form, dotProduct_comm]; rfl

theorem eq_zero_of_dot (invol : ∀ e, σ (σ e) = e) {v : Fin b → E}
    (h : ∀ z : Fin b → E, v ⬝ᵥ (fun i => σ (z i)) = 0) : v = 0 := by
  funext j
  have := h (fun i => σ ((Pi.single j (1 : E) : Fin b → E) i))
  simp only [invol] at this
  simpa using this

theorem form_symm (invol : ∀ e, σ (σ e) = e) {J : Matrix (Fin n) (Fin n) E} (herm : ∀ i j, σ (J j i) = J i j)
    (u w : Fin n → E) : form σ J u w = σ (form σ J w u) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, invol, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [herm]; ring

theorem form_mulVec (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin b) E) (u : Fin n → E) (z : Fin b → E) :
    form σ J u (ι *ᵥ z) = (u ᵥ* (J * ι.map σ)) ⬝ᵥ (fun i => σ (z i)) := by
  have : (fun i => σ ((ι *ᵥ z) i)) = ι.map σ *ᵥ (fun i => σ (z i)) :=
    funext fun i => RingHom.map_mulVec (σ : E →+* E) ι z i
  rw [form, this, mulVec_mulVec, dotProduct_mulVec]

theorem cvec_vecMul {J : Matrix (Fin n) (Fin n) E} {ι : Matrix (Fin n) (Fin b) E} {x : Fin n → E}
    (h : ∀ u, form σ J (ι *ᵥ u) x = 0) : cvec σ J x ᵥ* ι = 0 := by
  funext j
  have := h (Pi.single j 1)
  rw [form_eq_dot, dotProduct_mulVec, dotProduct_single, mul_one] at this
  exact this

theorem vecMul_J_map (invol : ∀ e, σ (σ e) = e) {J : Matrix (Fin n) (Fin n) E} (herm : ∀ i j, σ (J j i) = J i j)
    {ι : Matrix (Fin n) (Fin b) E} {x : Fin n → E} (h : ∀ u, form σ J (ι *ᵥ u) x = 0) :
    x ᵥ* (J * ι.map σ) = 0 := by
  apply eq_zero_of_dot σ invol
  intro z
  rw [← form_mulVec, form_symm σ invol herm, h z, map_zero]

theorem coef_mul {J : Matrix (Fin n) (Fin n) E} {ι : Matrix (Fin n) (Fin b) E} {J₁ : Matrix (Fin b) (Fin b) E}
    (gram : ιᵀ * J * ι.map σ = J₁) (hJ₁ : IsUnit J₁.det) : coef σ J ι J₁ * ι = 1 := by
  have e : (ι.map σ)ᵀ * Jᵀ * ι = J₁ᵀ := by
    rw [← gram, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [coef, Matrix.mul_assoc, e]
  exact Matrix.nonsing_inv_mul _ (by rwa [det_transpose])

theorem coef_mulVec {J : Matrix (Fin n) (Fin n) E} {ι : Matrix (Fin n) (Fin b) E} {J₁ : Matrix (Fin b) (Fin b) E}
    {x : Fin n → E} (h : x ᵥ* (J * ι.map σ) = 0) : coef σ J ι J₁ *ᵥ x = 0 := by
  rw [coef, ← mulVec_mulVec, ← transpose_mul, mulVec_transpose, h, mulVec_zero]

theorem proj (invol : ∀ e, σ (σ e) = e) {J : Matrix (Fin n) (Fin n) E} (herm : ∀ i j, σ (J j i) = J i j)
    {ι : Matrix (Fin n) (Fin b) E} {J₁ : Matrix (Fin b) (Fin b) E} {x y : Fin n → E} (hn : n = b + 2)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (gram : ιᵀ * J * ι.map σ = J₁) (hJ₁ : IsUnit J₁.det) :
    ι * coef σ J ι J₁ + vecMulVec x (cvec σ J y) + vecMulVec y (cvec σ J x) = 1 := by
  have hyx : form σ J y x = 1 := by rw [form_symm σ invol herm, hxy, map_one]
  have hSx := coef_mulVec σ (J₁ := J₁) (vecMul_J_map σ invol herm fun u => (horth u).1)
  have hSy := coef_mulVec σ (J₁ := J₁) (vecMul_J_map σ invol herm fun u => (horth u).2)
  have hcx := cvec_vecMul σ fun u => (horth u).1
  have hcy := cvec_vecMul σ fun u => (horth u).2
  have hd : ∀ u w : Fin n → E, (∑ k, cvec σ J w k * u k) = form σ J u w := fun u w => by
    rw [form_eq_dot]; rfl
  let A₂ : Matrix (Fin n) (Fin 2) E := Matrix.of fun i c => ![x i, y i] c
  let B₂ : Matrix (Fin 2) (Fin n) E := Matrix.of ![cvec σ J y, cvec σ J x]
  have h1 : fromRows (coef σ J ι J₁) B₂ * fromCols ι A₂ = 1 := by
    rw [fromRows_mul_fromCols, ← fromBlocks_one]
    refine fromBlocks_inj.2 ⟨coef_mul σ gram hJ₁, ?_, ?_, ?_⟩
    · ext i c
      fin_cases c
      · simpa [A₂, Matrix.mul_apply, mulVec, dotProduct] using congrFun hSx i
      · simpa [A₂, Matrix.mul_apply, mulVec, dotProduct] using congrFun hSy i
    · ext c j
      fin_cases c
      · simpa [B₂, Matrix.mul_apply, vecMul, dotProduct] using congrFun hcy j
      · simpa [B₂, Matrix.mul_apply, vecMul, dotProduct] using congrFun hcx j
    · ext c d
      fin_cases c <;> fin_cases d <;> simp [A₂, B₂, Matrix.mul_apply, hd, hxx, hyy, hxy, hyx]
  have e : Fin b ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr hn.symm)
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  rw [fromCols_mul_fromRows] at h2
  have h3 : A₂ * B₂ = vecMulVec x (cvec σ J y) + vecMulVec y (cvec σ J x) := by
    ext i j; simp [A₂, B₂, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec]
  rw [h3, ← add_assoc] at h2
  exact h2

end Lin

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem cA_inclR (e : E) : cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

variable {n b : ℕ}

theorem incM_mul {m p q : Type} [Fintype p] (A : Matrix m p E) (B : Matrix p q E) :
    incM F (A * B) = incM F A * incM F B := by
  simp only [incM]; exact Matrix.map_mul

theorem incM_add {m p : Type} (A B : Matrix m p E) : incM F (A + B) = incM F A + incM F B := by
  simp only [incM]; exact Matrix.map_add _ (map_add _) A B

theorem incM_one : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp only [incM]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_vecMulVec {p : ℕ} (u : Fin n → E) (w : Fin p → E) :
    incM F (vecMulVec u w) = vecMulVec (incV F u) (incV F w) := by
  ext i j; simp [incM, incV, vecMulVec]

theorem incM_mulVec {p : ℕ} (A : Matrix (Fin n) (Fin p) E) (x : Fin p → E) :
    incM F A *ᵥ incV F x = incV F (A *ᵥ x) :=
  funext fun i => (RingHom.map_mulVec (inclR (AF F)) A x i).symm

theorem incV_vecMul {p : ℕ} (x : Fin n → E) (A : Matrix (Fin n) (Fin p) E) :
    incV F x ᵥ* incM F A = incV F (x ᵥ* A) :=
  funext fun i => (RingHom.map_vecMul (inclR (AF F)) A x i).symm

theorem incV_dot (x y : Fin n → E) : incV F x ⬝ᵥ incV F y = inclR (AF F) (x ⬝ᵥ y) :=
  (RingHom.map_dotProduct (inclR (AF F)) x y).symm

theorem incV_zero : incV F (0 : Fin n → E) = 0 := funext fun _ => by simp [incV]

theorem incM_map {m p : Type} (A : Matrix m p E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j; simp [incM, cA_inclR]

theorem incV_map (x : Fin n → E) : (fun i => cA σ (incV F x i)) = incV F (fun i => σ (x i)) :=
  funext fun i => cA_inclR σ (x i)

theorem vecMulVec_zero' {R : Type} [MulZeroClass R] {m p : Type} (w : m → R) : vecMulVec w (0 : p → R) = 0 := by
  ext i j; simp [vecMulVec]

variable {J : Matrix (Fin n) (Fin n) E} {ι : Matrix (Fin n) (Fin b) E} {J₁ : Matrix (Fin b) (Fin b) E}
  {x y : Fin n → E} {K : Matrix (Fin n) (Fin n) (AE F E)} {l : (AE F E)ˣ}

theorem transpose_cvec (hU : Kᵀ * incM F J * K.map (cA σ) = incM F J) (hK : K *ᵥ incV F x = (l : AE F E) • incV F x) :
    cA σ (l : AE F E) • (Kᵀ *ᵥ incV F (cvec σ J x)) = incV F (cvec σ J x) := by
  have h1 : K.map (cA σ) *ᵥ incV F (fun i => σ (x i)) = cA σ (l : AE F E) • incV F (fun i => σ (x i)) := by
    rw [← incV_map]
    funext i
    have h := RingHom.map_mulVec (cA σ : AE F E →+* AE F E) K (incV F x) i
    rw [hK] at h
    simp only [Pi.smul_apply, smul_eq_mul, map_mul] at h ⊢
    exact h.symm
  rw [cvec, ← incM_mulVec, ← mulVec_smul, ← mulVec_smul, ← h1, mulVec_mulVec, mulVec_mulVec, hU]

theorem cvec_K (hcx : cvec σ J x ᵥ* ι = 0) (hU : Kᵀ * incM F J * K.map (cA σ) = incM F J)
    (hK : K *ᵥ incV F x = (l : AE F E) • incV F x) : incV F (cvec σ J x) ᵥ* (K * incM F ι) = 0 := by
  have hu : IsUnit (cA σ (l : AE F E)) := l.isUnit.map (cA σ)
  have h2 : Kᵀ *ᵥ incV F (cvec σ J x) = (↑hu.unit⁻¹ : AE F E) • incV F (cvec σ J x) := by
    have h := transpose_cvec σ hU hK
    calc Kᵀ *ᵥ incV F (cvec σ J x) = ((↑hu.unit⁻¹ : AE F E) * cA σ (l : AE F E)) • (Kᵀ *ᵥ incV F (cvec σ J x)) := by
          rw [IsUnit.val_inv_mul, one_smul]
      _ = (↑hu.unit⁻¹ : AE F E) • incV F (cvec σ J x) := by rw [← smul_smul, h]
  rw [← vecMul_vecMul, ← Matrix.mulVec_transpose K, h2, smul_vecMul, incV_vecMul, hcx, incV_zero, smul_zero]

theorem projA (S : Matrix (Fin b) (Fin n) E)
    (hP : ι * S + vecMulVec x (cvec σ J y) + vecMulVec y (cvec σ J x) = 1) :
    incM F ι * incM F S + vecMulVec (incV F x) (incV F (cvec σ J y)) +
      vecMulVec (incV F y) (incV F (cvec σ J x)) = 1 := by
  rw [← incM_mul, ← incM_vecMulVec, ← incM_vecMulVec, ← incM_add, ← incM_add, hP, incM_one]

theorem decomp (S : Matrix (Fin b) (Fin n) E)
    (hP : ι * S + vecMulVec x (cvec σ J y) + vecMulVec y (cvec σ J x) = 1)
    (hcx : cvec σ J x ᵥ* ι = 0) (hU : Kᵀ * incM F J * K.map (cA σ) = incM F J)
    (hK : K *ᵥ incV F x = (l : AE F E) • incV F x) (z : Fin b → AE F E) :
    K *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ ((incM F S * K * incM F ι) *ᵥ z) +
      (incV F (cvec σ J y) ⬝ᵥ (K *ᵥ (incM F ι *ᵥ z))) • incV F x := by
  have hPA := projA σ S hP
  have h0 : incV F (cvec σ J x) ⬝ᵥ (K *ᵥ (incM F ι *ᵥ z)) = 0 := by
    rw [mulVec_mulVec, dotProduct_mulVec, cvec_K σ hcx hU hK, zero_dotProduct]
  conv_lhs => rw [← one_mulVec (K *ᵥ (incM F ι *ᵥ z)), ← hPA]
  rw [add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, h0, op_smul_eq_smul, op_smul_eq_smul, zero_smul,
    add_zero]
  simp only [← mulVec_mulVec]

theorem unitary (S : Matrix (Fin b) (Fin n) E)
    (hP : ι * S + vecMulVec x (cvec σ J y) + vecMulVec y (cvec σ J x) = 1)
    (hcx : cvec σ J x ᵥ* ι = 0) (hxJ : x ᵥ* (J * ι.map σ) = 0) (hxcx : x ⬝ᵥ cvec σ J x = 0)
    (gram : ιᵀ * J * ι.map σ = J₁) (hU : Kᵀ * incM F J * K.map (cA σ) = incM F J)
    (hK : K *ᵥ incV F x = (l : AE F E) • incV F x) :
    (incM F S * K * incM F ι)ᵀ * incM F J₁ * (incM F S * K * incM F ι).map (cA σ) = incM F J₁ := by
  have hPA := projA σ S hP
  have hK0 := cvec_K σ hcx hU hK
  have hT : incM F ι * (incM F S * K * incM F ι) =
      K * incM F ι - vecMulVec (incV F x) (incV F (cvec σ J y) ᵥ* (K * incM F ι)) := by
    have h : incM F ι * incM F S * (K * incM F ι) +
        vecMulVec (incV F x) (incV F (cvec σ J y) ᵥ* (K * incM F ι)) = K * incM F ι := by
      calc _ = (incM F ι * incM F S + vecMulVec (incV F x) (incV F (cvec σ J y)) +
            vecMulVec (incV F y) (incV F (cvec σ J x))) * (K * incM F ι) := by
            rw [Matrix.add_mul, Matrix.add_mul, vecMulVec_mul, vecMulVec_mul, hK0, vecMulVec_zero', add_zero]
        _ = K * incM F ι := by rw [hPA, Matrix.one_mul]
    rw [eq_sub_iff_add_eq]
    refine Eq.trans ?_ h
    simp only [Matrix.mul_assoc]
  have hJ₁A : incM F J₁ = (incM F ι)ᵀ * incM F J * (incM F ι).map (cA σ) := by
    rw [incM_map, ← gram, incM_mul, incM_mul]; rfl
  have hx2 : incV F x ᵥ* (incM F J * (K.map (cA σ) * (incM F ι).map (cA σ))) = 0 := by
    have h3 : (l : AE F E) • (incV F x ᵥ* (incM F J * K.map (cA σ))) = incV F x ᵥ* incM F J := by
      have := congrArg (incV F x ᵥ* ·) hU
      rw [Matrix.mul_assoc, ← vecMul_vecMul, vecMul_transpose, hK, smul_vecMul] at this
      exact this
    have h4 : incV F x ᵥ* (incM F J * K.map (cA σ)) = (↑l⁻¹ : AE F E) • (incV F x ᵥ* incM F J) := by
      rw [← h3, smul_smul, Units.inv_mul, one_smul]
    rw [← Matrix.mul_assoc, ← vecMul_vecMul, h4, smul_vecMul, incM_map, incV_vecMul, incV_vecMul, vecMul_vecMul, hxJ,
      incV_zero, smul_zero]
  have hmapT : (K * incM F ι - vecMulVec (incV F x) (incV F (cvec σ J y) ᵥ* (K * incM F ι))).map (cA σ) =
      K.map (cA σ) * (incM F ι).map (cA σ) - vecMulVec (fun i => cA σ (incV F x i))
        (fun j => cA σ ((incV F (cvec σ J y) ᵥ* (K * incM F ι)) j)) := by
    ext i j; simp [Matrix.mul_apply, vecMulVec, map_sum, map_mul]
  have hcX : incM F J *ᵥ (fun i => cA σ (incV F x i)) = incV F (cvec σ J x) := by
    rw [incV_map, incM_mulVec]; rfl
  have e2 : (K * incM F ι - vecMulVec (incV F x) (incV F (cvec σ J y) ᵥ* (K * incM F ι)))ᵀ *ᵥ
      incV F (cvec σ J x) = 0 := by
    rw [mulVec_transpose, vecMul_sub, hK0, vecMul_vecMulVec, dotProduct_comm, incV_dot, hxcx, map_zero, zero_smul,
      sub_zero]
  have e3 : (K * incM F ι - vecMulVec (incV F x) (incV F (cvec σ J y) ᵥ* (K * incM F ι)))ᵀ *
      (incM F J * (K.map (cA σ) * (incM F ι).map (cA σ))) = incM F J₁ := by
    have e4 : (incM F ι)ᵀ * Kᵀ * (incM F J * (K.map (cA σ) * (incM F ι).map (cA σ))) =
        (incM F ι)ᵀ * (Kᵀ * incM F J * K.map (cA σ)) * (incM F ι).map (cA σ) := by
      simp only [Matrix.mul_assoc]
    rw [transpose_sub, transpose_vecMulVec, Matrix.sub_mul, vecMulVec_mul, hx2, vecMulVec_zero', sub_zero,
      transpose_mul, e4, hU, ← hJ₁A]
  calc (incM F S * K * incM F ι)ᵀ * incM F J₁ * (incM F S * K * incM F ι).map (cA σ)
      = (incM F ι * (incM F S * K * incM F ι))ᵀ * (incM F J * (incM F ι * (incM F S * K * incM F ι)).map (cA σ)) := by
        rw [hJ₁A]
        simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    _ = incM F J₁ := by
        rw [hT, hmapT, Matrix.mul_sub, Matrix.mul_vecMulVec, hcX, Matrix.mul_sub, Matrix.mul_vecMulVec, e2,
          zero_vecMulVec, sub_zero, e3]

theorem isUnit_det_of_hasSig {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} {r s : ℕ} (h : HasSig M r s) : IsUnit M.det := by
  obtain ⟨hrs, A, hA⟩ := h
  have hD : (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * fromBlocks 1 0 0 (-1) = 1 := by
    rw [fromBlocks_multiply]; simp
  have h1 : ((fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * Aᵀ * M) * A.map star = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, hD]
  have e : Fin r ⊕ Fin s ≃ Fin m := finSumFinEquiv.trans (finCongr hrs)
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  exact Matrix.isUnit_det_of_left_inverse
    (B := A.map star * ((fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * Aᵀ))
    (by rw [← h2]; simp only [Matrix.mul_assoc])

end Adelic

theorem levi_quot : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (k : UA σ G.V.J), k ∈ UAt σ G.V (evFin F v) → ∀ l : (AE F E)ˣ,
      mat k *ᵥ incV F H.x = (l : AE F E) • incV F H.x → ∃ g₁ ∈ UAt σ G₁.V (evFin F v), (∀ z : Fin b → AE F E, ∃ a : AE F E, mat k *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g₁ *ᵥ z) + a • incV F H.x) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hA hT hT₁ v k hk l hl
  have hH := hA.hH
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have invol : ∀ e, σ (σ e) = e := by
    intro e
    apply (B.emb w).1.injective
    rw [hT.base.cm.2.2.2, hT.base.cm.2.2.2, star_star]
  have herm := hT.geo.hV.herm
  have hJ₁ : IsUnit G₁.V.J.det := by
    have h := isUnit_det_of_hasSig (hT₁.geo.hV.sig w)
    have h' : (B.emb w).1 G₁.V.J.det ≠ 0 := by
      rw [RingHom.map_det]; exact h.ne_zero
    exact Ne.isUnit (fun h0 => h' (by rw [h0, map_zero]))
  have hcx := cvec_vecMul σ (fun u => (hH.orth u).1)
  have hxJ := vecMul_J_map σ invol herm (fun u => (hH.orth u).1)
  have hP := proj σ invol herm hH.rank hH.xx hH.yy hH.xy hH.orth hH.gram hJ₁
  have hU : (mat k)ᵀ * incM F G.V.J * (mat k).map (cA σ) = incM F G.V.J := k.2
  have hSι := coef_mul σ hH.gram hJ₁
  have hun := unitary σ _ hP hcx hxJ hH.xx hH.gram hU hl
  have hdet : IsUnit (incM F (coef σ G.V.J H.ι G₁.V.J) * mat k * incM F H.ι).det := by
    have h := congrArg Matrix.det hun
    rw [det_mul, det_mul, det_transpose] at h
    have hJA : IsUnit (incM F G₁.V.J).det := by
      have := hJ₁.map (inclR (AF F) : E →+* AE F E)
      rwa [RingHom.map_det] at this
    refine isUnit_iff_exists_inv.2 ⟨((incM F (coef σ G.V.J H.ι G₁.V.J) * mat k * incM F H.ι).map (cA σ)).det,
      hJA.mul_left_cancel ?_⟩
    linear_combination h
  refine ⟨⟨⟨incM F (coef σ G.V.J H.ι G₁.V.J) * mat k * incM F H.ι,
    (incM F (coef σ G.V.J H.ι G₁.V.J) * mat k * incM F H.ι)⁻¹, Matrix.mul_nonsing_inv _ hdet,
    Matrix.nonsing_inv_mul _ hdet⟩, hun⟩, ?_, fun z => ⟨_, decomp σ _ hP hcx hU hl z⟩⟩
  show At (evFin F v) (incM F (coef σ G.V.J H.ι G₁.V.J) * mat k * incM F H.ι - 1)
  intro u hu
  have hk' : u • (mat k - 1) = 0 := hk u hu
  have e : incM F (coef σ G.V.J H.ι G₁.V.J) * mat k * incM F H.ι - 1 =
      incM F (coef σ G.V.J H.ι G₁.V.J) * (mat k - 1) * incM F H.ι := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← incM_mul, hSι, incM_one]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hk', Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.LeviQuot
