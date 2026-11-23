import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDeterminantNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorDecompositionAlongAdaptedPlaneStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipCompact

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mul {m n p : Type} [Fintype n] (A : Matrix m n E) (B : Matrix n p E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

theorem incM_one {n : Type} [DecidableEq n] : incM F (1 : Matrix n n E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_add {m n : Type} (A B : Matrix m n E) : incM F (A + B) = incM F A + incM F B := by
  ext i j; simp [incM]

theorem incM_neg {m n : Type} (A : Matrix m n E) : incM F (-A) = -incM F A := by
  ext i j; simp [incM]

theorem incM_transpose {m n : Type} (A : Matrix m n E) : incM F Aᵀ = (incM F A)ᵀ := rfl

theorem incM_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i; simp [incM, incV, Matrix.mulVec, dotProduct, map_sum]

theorem incV_dot {n : ℕ} (a b : Fin n → E) : incV F a ⬝ᵥ incV F b = inclR (F := F) (AF F) (a ⬝ᵥ b) := by
  simp [incV, dotProduct, map_sum]

theorem incM_vecMulVec {m n : ℕ} (a : Fin m → E) (b : Fin n → E) :
    incM F (vecMulVec a b) = vecMulVec (incV F a) (incV F b) := by
  ext i j; simp [incM, incV, vecMulVec_apply]

theorem incV_smul {n : ℕ} (c : E) (a : Fin n → E) : incV F (c • a) = inclR (F := F) (AF F) c • incV F a := by
  ext i; simp [incV]

theorem incV_neg_eq {n : ℕ} (a : Fin n → E) : incV F (-a) = -incV F a := by
  ext i; simp [incV]

theorem incV_add {n : ℕ} (a b : Fin n → E) : incV F (a + b) = incV F a + incV F b := by
  ext i; simp [incV]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  have : (cA σ).comp (cA σ) = AlgHom.id (AF F) (AE F E) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [cA, hσ]
  exact AlgHom.congr_fun this z

end GlobalTheory.UnipCompact

namespace GlobalTheory.UnipCompact

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Rat

variable (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E)

def sv (v : Fin d → E) : Fin d → E := fun i => σ (v i)

def phi (v : Fin d → E) : Fin d → E := J *ᵥ sv σ v

theorem form_eq (u v : Fin d → E) : form σ J u v = u ⬝ᵥ phi σ J v := rfl

variable {σ J}

theorem sv_mulVec (M : Matrix (Fin d) (Fin d) E) (v : Fin d → E) : sv σ (M *ᵥ v) = M.map σ *ᵥ sv σ v := by
  ext i; simp [sv, mulVec, dotProduct, map_sum, map_mul]

theorem form_swap (hσ : ∀ a, σ (σ a) = a) (hskew : ∀ i j, σ (J j i) = -J i j) (a b : Fin d → E) :
    form σ J b a = -σ (form σ J a b) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hskew, Finset.mul_sum, Finset.sum_neg_distrib,
    neg_mul, mul_neg]
  rw [neg_neg, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem map_sigma_J (hskew : ∀ i j, σ (J j i) = -J i j) : J.map σ = -Jᵀ := by
  ext i j; simp [hskew]

end Rat

end GlobalTheory.UnipCompact

namespace GlobalTheory.UnipCompact

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Adj

variable (σ : E →ₐ[F] E) {d : ℕ}

def cT (X : Matrix (Fin d) (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E) :=
  ((cA σ : AE F E →+* AE F E).mapMatrix X)ᵀ

def adj (Li L : Matrix (Fin d) (Fin d) E) : Matrix (Fin d) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin d) (AE F E) where
  toFun X := incM F Li * cT σ X * incM F L
  map_zero' := by simp [cT]
  map_add' X Y := by simp only [cT, map_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

variable {σ}

theorem adj_apply (Li L : Matrix (Fin d) (Fin d) E) (X : Matrix (Fin d) (Fin d) (AE F E)) :
    adj σ Li L X = incM F Li * cT σ X * incM F L := rfl

theorem cT_mul (X Y : Matrix (Fin d) (Fin d) (AE F E)) : cT σ (X * Y) = cT σ Y * cT σ X := by
  simp [cT, Matrix.transpose_mul]

theorem cT_incM (A : Matrix (Fin d) (Fin d) E) : cT σ (incM F A) = incM F (A.map σ)ᵀ := by
  rw [cT, RingHom.mapMatrix_apply, incM_transpose]
  congr 1

theorem cT_cT (hσ : ∀ a, σ (σ a) = a) (X : Matrix (Fin d) (Fin d) (AE F E)) : cT σ (cT σ X) = X := by
  ext i j; simp [cT, cA_cA σ hσ]

theorem adj_mul {Li L : Matrix (Fin d) (Fin d) E} (hLL : L * Li = 1) (X Y : Matrix (Fin d) (Fin d) (AE F E)) :
    adj σ Li L (X * Y) = adj σ Li L Y * adj σ Li L X := by
  have h : incM F L * incM F Li = 1 := by rw [← incM_mul, hLL, incM_one]
  simp only [adj_apply, cT_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F L) (incM F Li), h, Matrix.one_mul]

theorem adj_adj (hσ : ∀ a, σ (σ a) = a) {Li L : Matrix (Fin d) (Fin d) E} (hLi : Li * L = 1)
    (hL1 : (L.map σ)ᵀ = -L) (hL2 : (Li.map σ)ᵀ = -Li) (X : Matrix (Fin d) (Fin d) (AE F E)) :
    adj σ Li L (adj σ Li L X) = X := by
  have h : incM F Li * incM F L = 1 := by rw [← incM_mul, hLi, incM_one]
  simp only [adj_apply, cT_mul, cT_incM, cT_cT hσ, hL1, hL2, incM_neg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F Li) (-incM F L), Matrix.mul_neg, h]
  simp [Matrix.neg_mul, h]

theorem adj_incM {Li L : Matrix (Fin d) (Fin d) E} (A : Matrix (Fin d) (Fin d) E) :
    adj σ Li L (incM F A) = incM F (Li * (A.map σ)ᵀ * L) := by
  rw [adj_apply, cT_incM, incM_mul, incM_mul]

theorem unitary_iff {J Li : Matrix (Fin d) (Fin d) E} (hLi : Li * Jᵀ = 1) (hLL : Jᵀ * Li = 1)
    (G : Matrix (Fin d) (Fin d) (AE F E)) :
    Gᵀ * incM F J * G.map (cA σ) = incM F J ↔ adj σ Li Jᵀ G * G = 1 := by
  have h1 : incM F Li * incM F Jᵀ = 1 := by rw [← incM_mul, hLi, incM_one]
  have h2 : incM F Jᵀ * incM F Li = 1 := by rw [← incM_mul, hLL, incM_one]
  have key : Gᵀ * incM F J * G.map (cA σ) = incM F J ↔ cT σ G * incM F Jᵀ * G = incM F Jᵀ := by
    constructor
    · intro h
      have := congrArg Matrix.transpose h
      simpa [cT, Matrix.transpose_mul, incM_transpose, Matrix.mul_assoc] using this
    · intro h
      have := congrArg Matrix.transpose h
      simpa [cT, Matrix.transpose_mul, incM_transpose, Matrix.mul_assoc] using this
  rw [key, adj_apply]
  constructor
  · intro h
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ G), h, h1]
  · intro h
    have := congrArg (incM F Jᵀ * ·) h
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_one] at this
    exact this

end Adj

end GlobalTheory.UnipCompact

namespace GlobalTheory.UnipCompact

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Proj

variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {J : Matrix (Fin d) (Fin d) E} {x y : Fin d → E} {ι : Matrix (Fin d) (Fin d₁) E}

variable (σ J x y) in

def E1 : Matrix (Fin d) (Fin d) E := vecMulVec x (phi σ J y)

variable (σ J x y) in

def E3 : Matrix (Fin d) (Fin d) E := vecMulVec (-y) (phi σ J x)

theorem E1_mul_E1 (hxy : form σ J x y = 1) : E1 σ J x y * E1 σ J x y = E1 σ J x y := by
  rw [E1, vecMulVec_mul_vecMulVec, dotProduct_comm, ← form_eq, hxy, one_smul]

theorem E1_mul_E3 (hyy : form σ J y y = 0) : E1 σ J x y * E3 σ J x y = 0 := by
  rw [E1, E3, vecMulVec_mul_vecMulVec, dotProduct_neg, dotProduct_comm, ← form_eq, hyy, neg_zero, zero_smul]
  ext i j; simp [vecMulVec_apply]

theorem E3_mul_E1 (hxx : form σ J x x = 0) : E3 σ J x y * E1 σ J x y = 0 := by
  rw [E1, E3, vecMulVec_mul_vecMulVec, dotProduct_comm, ← form_eq, hxx, zero_smul]
  ext i j; simp [vecMulVec_apply]

theorem map_vecMulVec (a b : Fin d → E) : (vecMulVec a b).map σ = vecMulVec (sv σ a) (sv σ b) := by
  ext i j; simp [vecMulVec_apply, sv]

theorem adj_E1 (hσ : ∀ a, σ (σ a) = a) (hskew : ∀ i j, σ (J j i) = -J i j) {Li : Matrix (Fin d) (Fin d) E}
    (hLi : Li * Jᵀ = 1) : Li * ((E1 σ J x y).map σ)ᵀ * Jᵀ = E3 σ J x y := by
  have h1 : sv σ (phi σ J y) = -(Jᵀ *ᵥ y) := by
    rw [phi, sv_mulVec, map_sigma_J hskew]
    have : sv σ (sv σ y) = y := by ext i; simp [sv, hσ]
    rw [this, Matrix.neg_mulVec]
  rw [E1, map_vecMulVec, transpose_vecMulVec, mul_vecMulVec, vecMulVec_mul, h1, Matrix.mulVec_neg,
    Matrix.mulVec_mulVec, hLi, Matrix.one_mulVec, vecMul_transpose, E3]
  rfl

end Proj

end GlobalTheory.UnipCompact

namespace GlobalTheory.UnipCompact

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Char

variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {J : Matrix (Fin d) (Fin d) E} {x y : Fin d → E} {ι : Matrix (Fin d) (Fin d₁) E}

theorem E1_mulVec (v : Fin d → AE F E) :
    incM F (E1 σ J x y) *ᵥ v = (incV F (phi σ J y) ⬝ᵥ v) • incV F x := by
  rw [E1, incM_vecMulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem E3_mulVec (v : Fin d → AE F E) :
    incM F (E3 σ J x y) *ᵥ v = (incV F (phi σ J x) ⬝ᵥ v) • incV F (-y) := by
  rw [E3, incM_vecMulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem phi_dot (a b : Fin d → E) : incV F (phi σ J b) ⬝ᵥ incV F a = inclR (F := F) (AF F) (form σ J a b) := by
  rw [dotProduct_comm, incV_dot, form_eq]

theorem phi_dot_iota (horth : ∀ u, form σ J (ι *ᵥ u) x = 0) (z : Fin d₁ → AE F E) :
    incV F (phi σ J x) ⬝ᵥ (incM F ι *ᵥ z) = 0 := by
  have h0 : ιᵀ *ᵥ phi σ J x = 0 := by
    ext k
    have := horth (Pi.single k 1)
    rw [form_eq, dotProduct_comm, dotProduct_mulVec, dotProduct_single, mul_one] at this
    rw [mulVec_transpose]
    simpa using this
  rw [dotProduct_mulVec, ← mulVec_transpose, ← incM_transpose, incM_mulVec, h0]
  simp [incV, dotProduct]

theorem fix_iff (hxy : form σ J x y = 1) (M : Matrix (Fin d) (Fin d) (AE F E)) :
    (M - 1) * incM F (E1 σ J x y) = 0 ↔ M *ᵥ incV F x = incV F x := by
  have hx : incM F (E1 σ J x y) *ᵥ incV F x = incV F x := by
    rw [E1_mulVec, phi_dot, hxy, map_one, one_smul]
  constructor
  · intro h
    have := congrArg (· *ᵥ incV F x) h
    simp only [← Matrix.mulVec_mulVec, hx, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec] at this
    exact sub_eq_zero.1 this
  · intro h
    rw [E1, incM_vecMulVec, mul_vecMulVec, Matrix.sub_mulVec, Matrix.one_mulVec, h, sub_self]
    ext i j; simp [vecMulVec_apply]

theorem mat_eq_zero_of_mulVec {A : Matrix (Fin d) (Fin d) (AE F E)} (h : ∀ v, A *ᵥ v = 0) : A = 0 := by
  ext i j
  have := congr_fun (h (Pi.single j 1)) i
  simpa [mulVec_single] using this

theorem shear_of (hxy : form σ J x y = 1) (horth : ∀ u, form σ J (ι *ᵥ u) x = 0)
    (M : Matrix (Fin d) (Fin d) (AE F E)) (h : (1 - incM F (E1 σ J x y)) * (M - 1) * (1 - incM F (E3 σ J x y)) = 0)
    (z : Fin d₁ → AE F E) : ∃ a : AE F E, M *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + a • incV F x := by
  set w := incM F ι *ᵥ z
  have h3 : (1 - incM F (E3 σ J x y)) *ᵥ w = w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, E3_mulVec, phi_dot_iota horth, zero_smul, sub_zero]
  have := congrArg (· *ᵥ w) h
  simp only [← Matrix.mulVec_mulVec, h3, Matrix.zero_mulVec] at this
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, E1_mulVec, sub_eq_zero, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_iff_eq_add'] at this
  exact ⟨_, this⟩

theorem shear_to (hxy : form σ J x y = 1) (hxx : form σ J x x = 0)
    (hyx : form σ J y x = -1) (horth : ∀ u, form σ J (ι *ᵥ u) x = 0)
    (hdec : ∀ v : Fin d → AE F E, ∃ (a b : AE F E) (z : Fin d₁ → AE F E), v = a • incV F x + incM F ι *ᵥ z + b • incV F y)
    (M : Matrix (Fin d) (Fin d) (AE F E)) (hM : M *ᵥ incV F x = incV F x)
    (hz : ∀ z : Fin d₁ → AE F E, ∃ a : AE F E, M *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + a • incV F x) :
    (1 - incM F (E1 σ J x y)) * (M - 1) * (1 - incM F (E3 σ J x y)) = 0 := by
  refine mat_eq_zero_of_mulVec fun v => ?_
  obtain ⟨a, b, z, rfl⟩ := hdec v
  obtain ⟨c, hc⟩ := hz z
  have h3 : (1 - incM F (E3 σ J x y)) *ᵥ (a • incV F x + incM F ι *ᵥ z + b • incV F y) =
      a • incV F x + incM F ι *ᵥ z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, E3_mulVec]
    simp only [dotProduct_add, dotProduct_smul, phi_dot, hxx, hyx, phi_dot_iota horth, map_zero, map_neg, map_one,
      smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one]
    rw [incV_neg_eq, neg_smul, smul_neg, neg_neg, add_sub_cancel_right]
  have h2 : (M - 1) *ᵥ (a • incV F x + incM F ι *ᵥ z) = c • incV F x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hM, hc]
    abel
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3, h2, Matrix.sub_mulVec, Matrix.one_mulVec, E1_mulVec,
    dotProduct_smul, phi_dot, hxy, map_one, smul_eq_mul, mul_one, sub_self]

end Char

end GlobalTheory.UnipCompact

namespace GlobalTheory.UnipCompact

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Grp

variable (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (x : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E)

def shearGrp : Subgroup (UA σ J) where
  carrier := {u | mat u *ᵥ incV F x = incV F x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + a • incV F x}
  one_mem' := by
    refine ⟨?_, fun z => ⟨0, ?_⟩⟩
    · show (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _
      rw [Matrix.one_mulVec]
    · show (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _
      rw [Matrix.one_mulVec, zero_smul, add_zero]
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨?_, fun z => ?_⟩
    · show (mat u * mat v) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, hv1, hu1]
    · obtain ⟨b, hb⟩ := hv2 z
      obtain ⟨a, ha⟩ := hu2 z
      refine ⟨a + b, ?_⟩
      show (mat u * mat v) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, ha, hu1, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have hinv : mat u⁻¹ * mat u = 1 := Units.inv_mul u.1
    have hx : mat u⁻¹ *ᵥ incV F x = incV F x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    set w := incM F ι *ᵥ z
    have := congrArg (mat u⁻¹ *ᵥ ·) ha
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hx] at this
    rw [eq_sub_of_add_eq this.symm, neg_smul, sub_eq_add_neg]

end Grp

end GlobalTheory.UnipCompact

namespace GlobalTheory.UnipCompact

open Matrix

theorem dec_adelic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d d₁ : ℕ}
    {x y : Fin d → E} {ι : Matrix (Fin d) (Fin d₁) E}
    (h : ∀ v : Fin d → E, ∃ (a b : E) (u : Fin d₁ → E), v = a • x + ι *ᵥ u + b • y) (v : Fin d → AE F E) :
    ∃ (a b : AE F E) (z : Fin d₁ → AE F E), v = a • incV F x + incM F ι *ᵥ z + b • incV F y := by
  choose a b u hu using fun i : Fin d => h (Pi.single i 1)
  refine ⟨∑ i, v i * inclR (F := F) (AF F) (a i), ∑ i, v i * inclR (F := F) (AF F) (b i), ∑ i, v i • incV F (u i), ?_⟩
  have hv : v = ∑ i, v i • incV F (Pi.single i 1) := by
    ext k; simp [incV, Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv]
  have e : ∀ i, incV F (Pi.single i (1 : E)) =
      inclR (F := F) (AF F) (a i) • incV F x + incM F ι *ᵥ incV F (u i) + inclR (F := F) (AF F) (b i) • incV F y := by
    intro i; rw [incM_mulVec, ← incV_smul, ← incV_smul, ← incV_add, ← incV_add, ← hu i]
  simp only [e, smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul, Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

end GlobalTheory.UnipCompact

namespace GlobalTheory.UnipCompact

open Matrix

set_option maxHeartbeats 1000000 in

theorem exists_bounded_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∃ R : ℝ≥0, ∀ u ∈ unip σ W H', ∃ γ ∈ ratU σ W.J ⊓ unip σ W H', ht (γ * u) ≤ R := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s hB hW hH
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hσ : ∀ a, σ (σ a) = a := sigma_invol hB.cm
  have hskew := hW.skew
  have hJ : W.J.det ≠ 0 := GlobalTheory.T.skew_hermitian_determinant_ne_zero F E σ B d W r s hW
  have hdetL : IsUnit (W.Jᵀ).det := by rw [det_transpose]; exact isUnit_iff_ne_zero.2 hJ
  set L : Matrix (Fin d) (Fin d) E := W.Jᵀ with hLdef
  set Li : Matrix (Fin d) (Fin d) E := L⁻¹ with hLidef
  have hLi : Li * L = 1 := Matrix.nonsing_inv_mul _ hdetL
  have hLL : L * Li = 1 := Matrix.mul_nonsing_inv _ hdetL
  have hL1 : (L.map σ)ᵀ = -L := by
    rw [hLdef, Matrix.transpose_map, transpose_transpose, map_sigma_J hskew]
  have hL2 : (Li.map σ)ᵀ = -Li := by
    have h0 : Li.map σ * L.map σ = 1 := by
      have e : Li.map σ * L.map σ = (Li * L).map σ := by ext i j; simp [Matrix.mul_apply, map_sum, map_mul]
      rw [e, hLi]; ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have hT : -L * (Li.map σ)ᵀ = 1 := by
      rw [← hL1, ← Matrix.transpose_mul, h0, transpose_one]
    calc (Li.map σ)ᵀ = (Li * L) * (Li.map σ)ᵀ := by rw [hLi, Matrix.one_mul]
      _ = -(Li * (-L * (Li.map σ)ᵀ)) := by simp [Matrix.mul_assoc]
      _ = -Li := by rw [hT, Matrix.mul_one]
  have hxx := hH.xx
  have hyy := hH.yy
  have hxy := hH.xy
  have hyx : form σ W.J H'.y H'.x = -1 := by rw [form_swap hσ hskew, hxy, map_one]
  have horth : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 := fun u => (hH.orth u).1
  have hdec := dec_adelic (F := F) (GlobalTheory.T.vector_decomposition_along_adapted_plane F E σ B d d₁ W W₁ H' i₀ i₁ r s hW hH)

  set e₁ := incM F (E1 σ W.J H'.x H'.y) with he₁
  set e₃ := incM F (E3 σ W.J H'.x H'.y) with he₃
  set st := adj (F := F) σ Li L with hst
  set S₀ : Subring (Matrix (Fin d) (Fin d) (AE F E)) :=
    (RingHom.mapMatrix (inclR (F := F) (E := E) (AF F)) : Matrix (Fin d) (Fin d) E →+* _).range with hS₀
  have memS₀ : ∀ A : Matrix (Fin d) (Fin d) E, incM F A ∈ S₀ := fun A => ⟨A, rfl⟩
  set hh : Matrix (Fin d) (Fin d) (AE F E) := incM F (Matrix.scalar (Fin d) (2⁻¹ : E)) with hhdef
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hcont : Continuous st := by
    show Continuous fun X => incM F Li * cT σ X * incM F L
    exact (continuous_const.matrix_mul (continuous_id.matrix_map hcA).matrix_transpose).matrix_mul continuous_const
  have hst_mul : ∀ X Y, st (X * Y) = st Y * st X := adj_mul hLL
  have hst_inv : ∀ X, st (st X) = X := adj_adj hσ hLi hL1 hL2
  have hst_S₀ : ∀ X ∈ S₀, st X ∈ S₀ := by
    rintro _ ⟨A, rfl⟩
    exact ⟨_, (adj_incM A).symm⟩
  have hst_e₁ : st e₁ = e₃ := by rw [he₁, hst, adj_incM, adj_E1 hσ hskew hLi]
  have h11 : e₁ * e₁ = e₁ := by rw [he₁, ← incM_mul, E1_mul_E1 hxy]
  have h13 : e₁ * e₃ = 0 := by rw [he₁, he₃, ← incM_mul, E1_mul_E3 hyy]; ext; simp [incM]
  have h31 : e₃ * e₁ = 0 := by rw [he₁, he₃, ← incM_mul, E3_mul_E1 hxx]; ext; simp [incM]
  have hhalf : hh + hh = 1 := by
    have h2 : (2⁻¹ : E) + 2⁻¹ = 1 := by norm_num
    rw [hhdef, ← incM_add, ← map_add, h2, map_one, incM_one]
  have hcomm : ∀ X, hh * X = X * hh := by
    intro X
    have : hh = Matrix.scalar (Fin d) (inclR (F := F) (AF F) 2⁻¹) := by
      ext i j; by_cases hij : i = j <;> simp [hhdef, incM, hij, Matrix.scalar_apply, Matrix.diagonal_apply]
    rw [this]; exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) X)
  obtain ⟨K₀, hK₀, hK₀s⟩ := GlobalTheory.AutFunCompare.tens_cocompact (F := F) (E := E)
  set K : Set (Matrix (Fin d) (Fin d) (AE F E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K₀ with hKdef
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK₀
  have hKs : ∀ X, ∃ Y ∈ S₀, X - Y ∈ K := by
    intro X
    choose y hy using fun i j => hK₀s (X i j)
    exact ⟨incM F (Matrix.of y), memS₀ _, fun i _ j _ => hy i j⟩
  obtain ⟨K', hK', -, h2⟩ := GlobalTheory.TwoStepUnipotent.compact_mod_subring (Matrix (Fin d) (Fin d) (AE F E)) st S₀
    e₁ e₃ hh K hcont hst_mul hst_inv hst_S₀ (memS₀ _) (memS₀ _) h11 hst_e₁ h13 h31 hhalf hcomm hK hKs
  obtain ⟨R, hR⟩ := hK'.bddAbove_image (GlobalTheory.Grow.continuous_heightGL (E := E) F).continuousOn
  refine ⟨R, fun u hu => ?_⟩
  have hu' : u ∈ shearGrp σ W.J H'.x H'.ι := (Subgroup.closure_le _).2 (fun v hv => hv) hu
  obtain ⟨hu1, hu2⟩ := hu'
  have hunit : ∀ g : GL (Fin d) (AE F E), g ∈ UG (cA σ) (incM F W.J) ↔ st g * g = 1 := fun g =>
    unitary_iff (F := F) (E := E) (σ := σ) (J := W.J) (Li := Li) hLi hLL (g : Matrix (Fin d) (Fin d) (AE F E))
  obtain ⟨γ, hγ, ⟨A, hA⟩, ⟨A', hA'⟩, hγK⟩ := h2 u.1
    ⟨(hunit u.1).1 u.2, (fix_iff (F := F) hxy _).2 hu1, shear_to (F := F) hxy hxx hyx horth hdec _ hu1 hu2⟩
  have hγU : γ ∈ UG (cA σ) (incM F W.J) := (hunit γ).2 hγ.1
  let γ' : UA σ W.J := ⟨γ, hγU⟩
  have hAA : A * A' = 1 := by
    apply Matrix.map_injective (GlobalTheory.AutFunCompare.inclA_injective (F := F) (E := E))
    change incM F (A * A') = incM F 1
    rw [incM_mul, incM_one]
    change RingHom.mapMatrix _ A * RingHom.mapMatrix _ A' = 1
    rw [hA, hA']; exact Units.mul_inv γ
  have hA'A : A' * A = 1 := by
    apply Matrix.map_injective (GlobalTheory.AutFunCompare.inclA_injective (F := F) (E := E))
    change incM F (A' * A) = incM F 1
    rw [incM_mul, incM_one]
    change RingHom.mapMatrix _ A' * RingHom.mapMatrix _ A = 1
    rw [hA, hA']; exact Units.inv_mul γ
  have hrat : γ' ∈ ratU σ W.J := by
    rw [ratU, Subgroup.mem_subgroupOf]
    refine ⟨⟨A, A', hAA, hA'A⟩, Units.ext ?_⟩
    exact hA
  have hx' : mat γ' *ᵥ incV F H'.x = incV F H'.x := (fix_iff (F := F) hxy _).1 hγ.2.1
  have hun : γ' ∈ unip σ W H' :=
    Subgroup.subset_closure ⟨hx', fun z => shear_of (F := F) hxy horth _ hγ.2.2 z⟩
  refine ⟨γ', ⟨hrat, hun⟩, ?_⟩
  exact hR ⟨γ * u.1, hγK, rfl⟩

end GlobalTheory.UnipCompact
