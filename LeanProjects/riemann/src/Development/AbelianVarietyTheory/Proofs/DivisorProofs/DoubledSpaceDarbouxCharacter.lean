import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DiagLagrMove

open Matrix

section Witt

variable {K : Type} [Field K] {σ : K →+* K} {β : Type} [Fintype β] [DecidableEq β]

theorem swap_form (hσ : ∀ x, σ (σ x) = x) {J : Matrix β β K} (hJ : (J.map σ)ᵀ = -J) {μ ν : Type} [Fintype μ] [Fintype ν]
    (P : Matrix β μ K) (Q : Matrix β ν K) : Qᵀ * J * P.map σ = -((Pᵀ * J * Q.map σ).map σ)ᵀ := by
  have hQ : (Q.map σ).map σ = Q := by ext; simp [hσ]
  rw [Matrix.map_mul, Matrix.map_mul, hQ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_map,
    Matrix.transpose_transpose, hJ]
  simp [Matrix.mul_assoc]

theorem exists_compl (hσ : ∀ x, σ (σ x) = x) (h2 : (2 : K) ≠ 0) {J : Matrix β β K} (hJ : (J.map σ)ᵀ = -J) {ν : Type}
    [Fintype ν] [DecidableEq ν] (Z X : Matrix β ν K) (h : Zᵀ * J * Z.map σ = 0) (k : Zᵀ * J * X.map σ = 1) :
    ∃ Z' : Matrix β ν K, Zᵀ * J * Z'.map σ = 1 ∧ Z'ᵀ * J * Z'.map σ = 0 := by
  set A := Xᵀ * J * X.map σ with hA
  have hA' : (A.map σ)ᵀ = -A := by
    have := swap_form hσ hJ X X
    rw [← hA] at this
    exact neg_eq_iff_eq_neg.mp this.symm
  have h1 : (1 : Matrix ν ν K).map σ = 1 := Matrix.map_one _ (map_zero σ) (map_one σ)
  have hXZ : Xᵀ * J * Z.map σ = -1 := by rw [swap_form hσ hJ Z X, k, h1, Matrix.transpose_one]
  have hc : σ (2⁻¹ : K) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set T : Matrix ν ν K := -((2⁻¹ : K) • Aᵀ) with hT
  have hTs : T.map σ = (2⁻¹ : K) • A := by
    ext i j
    have := congrFun (congrFun hA' i) j
    simp only [transpose_apply, map_apply, Matrix.neg_apply] at this
    simp [hT, hc, this]
  have hTt : Tᵀ = -((2⁻¹ : K) • A) := by rw [hT]; simp
  have hm : (X + Z * T).map σ = X.map σ + Z.map σ * T.map σ := by rw [Matrix.map_add _ (map_add σ), Matrix.map_mul]
  refine ⟨X + Z * T, ?_, ?_⟩
  · rw [hm, Matrix.mul_add, ← Matrix.mul_assoc (Zᵀ * J), h, Matrix.zero_mul, add_zero, k]
  · have e : (X + Z * T)ᵀ * J * (X + Z * T).map σ = A + (Xᵀ * J * Z.map σ) * T.map σ + Tᵀ * (Zᵀ * J * X.map σ) +
        Tᵀ * (Zᵀ * J * Z.map σ) * T.map σ := by
      simp only [hm, hA, Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul,
        Matrix.mul_add, Matrix.mul_assoc]
      abel
    rw [e, hXZ, k, h, hTs, hTt]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
    rw [add_assoc, ← neg_add, ← two_smul K ((2⁻¹ : K) • A), smul_smul, mul_inv_cancel₀ h2, one_smul,
      add_neg_cancel]

theorem gram_frame (hσ : ∀ x, σ (σ x) = x) {J : Matrix β β K} (hJ : (J.map σ)ᵀ = -J) {ν : Type} [Fintype ν]
    [DecidableEq ν] (Z Z' : Matrix β ν K) (h : Zᵀ * J * Z.map σ = 0) (a : Zᵀ * J * Z'.map σ = 1)
    (b : Z'ᵀ * J * Z'.map σ = 0) :
    (fromCols Z Z')ᵀ * J * (fromCols Z Z').map σ = fromBlocks 0 1 (-1) 0 := by
  have h1 : (1 : Matrix ν ν K).map σ = 1 := Matrix.map_one _ (map_zero σ) (map_one σ)
  have c : Z'ᵀ * J * Z.map σ = -1 := by rw [swap_form hσ hJ Z Z', a, h1, Matrix.transpose_one]
  rw [transpose_fromCols, fromRows_mul, fromCols_map, fromRows_mul_fromCols, h, a, b, c]

end Witt

end GlobalTheory.DiagLagrMove

namespace GlobalTheory.DiagLagrMove

open Matrix

section Witt2

variable {K : Type} [Field K] {σ : K →+* K}

theorem exists_unitary (hσ : ∀ x, σ (σ x) = x) (h2 : (2 : K) ≠ 0) {ν : Type} [Fintype ν] [DecidableEq ν]
    {J : Matrix (ν ⊕ ν) (ν ⊕ ν) K} (hJ : (J.map σ)ᵀ = -J) (Z₁ Z₂ X₁ X₂ : Matrix (ν ⊕ ν) ν K)
    (h₁ : Z₁ᵀ * J * Z₁.map σ = 0) (h₂ : Z₂ᵀ * J * Z₂.map σ = 0)
    (k₁ : Z₁ᵀ * J * X₁.map σ = 1) (k₂ : Z₂ᵀ * J * X₂.map σ = 1) :
    ∃ g g' : Matrix (ν ⊕ ν) (ν ⊕ ν) K, gᵀ * J * g.map σ = J ∧ g * Z₁ = Z₂ ∧ g * g' = 1 := by
  obtain ⟨Z₁', a₁, b₁⟩ := exists_compl hσ h2 hJ Z₁ X₁ h₁ k₁
  obtain ⟨Z₂', a₂, b₂⟩ := exists_compl hσ h2 hJ Z₂ X₂ h₂ k₂
  have H₁ := gram_frame hσ hJ Z₁ Z₁' h₁ a₁ b₁
  have H₂ := gram_frame hσ hJ Z₂ Z₂' h₂ a₂ b₂
  set Hi : Matrix (ν ⊕ ν) (ν ⊕ ν) K := fromBlocks 0 (-1) 1 0
  have hH : (fromBlocks 0 1 (-1) 0 : Matrix (ν ⊕ ν) (ν ⊕ ν) K).map σ = fromBlocks 0 1 (-1) 0 := by
    rw [fromBlocks_map, Matrix.map_zero _ (map_zero σ), Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.map_neg _ (map_neg σ), Matrix.map_one _ (map_zero σ) (map_one σ)]
  have HiH : Hi * fromBlocks 0 1 (-1) 0 = 1 := by
    rw [fromBlocks_multiply]; simp [fromBlocks_one]
  have linv : ∀ P : Matrix (ν ⊕ ν) (ν ⊕ ν) K, Pᵀ * J * P.map σ = fromBlocks 0 1 (-1) 0 →
      ∃ Q : Matrix (ν ⊕ ν) (ν ⊕ ν) K, Q * P = 1 := by
    intro P hP
    refine ⟨Hi * (P.map σ)ᵀ * J.map σ, ?_⟩
    have hPP : (P.map σ).map σ = P := by ext; simp [hσ]
    have e := congrArg (fun M => M.map σ) hP
    simp only [Matrix.map_mul, hPP, hH] at e
    rw [Matrix.transpose_map] at e
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (P.map σ)ᵀ, e, HiH]
  obtain ⟨Q₁, QP₁⟩ := linv _ H₁
  obtain ⟨Q₂, QP₂⟩ := linv _ H₂
  have PQ₁ : fromCols Z₁ Z₁' * Q₁ = 1 := mul_eq_one_comm.1 QP₁
  have PQ₂ : fromCols Z₂ Z₂' * Q₂ = 1 := mul_eq_one_comm.1 QP₂
  refine ⟨fromCols Z₂ Z₂' * Q₁, fromCols Z₁ Z₁' * Q₂, ?_, ?_, ?_⟩
  · calc (fromCols Z₂ Z₂' * Q₁)ᵀ * J * (fromCols Z₂ Z₂' * Q₁).map σ
          = Q₁ᵀ * ((fromCols Z₂ Z₂')ᵀ * J * (fromCols Z₂ Z₂').map σ) * Q₁.map σ := by
            rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = Q₁ᵀ * ((fromCols Z₁ Z₁')ᵀ * J * (fromCols Z₁ Z₁').map σ) * Q₁.map σ := by rw [H₁, H₂]
      _ = (fromCols Z₁ Z₁' * Q₁)ᵀ * J * (fromCols Z₁ Z₁' * Q₁).map σ := by
            rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [PQ₁, Matrix.transpose_one, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.one_mul, Matrix.mul_one]
  · have e₁ : Z₁ = fromCols Z₁ Z₁' * fromRows (1 : Matrix ν ν K) (0 : Matrix ν ν K) := by
      rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
    have e₂ : Z₂ = fromCols Z₂ Z₂' * fromRows (1 : Matrix ν ν K) (0 : Matrix ν ν K) := by
      rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
    conv_lhs => rw [e₁]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q₁, QP₁, Matrix.one_mul, ← e₂]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q₁, QP₁, Matrix.one_mul, PQ₂]

end Witt2

end GlobalTheory.DiagLagrMove

namespace GlobalTheory.DiagLagrMove

open Matrix

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def lagCol {d d₁ : ℕ} (x : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E) : (Unit ⊕ Unit) ⊕ Fin d₁ → Fin d ⊕ Fin d → E
  | Sum.inl (Sum.inl _) => Sum.elim x 0
  | Sum.inl (Sum.inr _) => Sum.elim 0 x
  | Sum.inr k => Sum.elim (ι *ᵥ Pi.single k 1) (ι *ᵥ Pi.single k 1)

def lagDual {d d₁ : ℕ} (y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E) (V : Matrix (Fin d₁) (Fin d₁) E) :
    (Unit ⊕ Unit) ⊕ Fin d₁ → Fin d ⊕ Fin d → E
  | Sum.inl (Sum.inl _) => Sum.elim y 0
  | Sum.inl (Sum.inr _) => Sum.elim 0 (-y)
  | Sum.inr k => Sum.elim (ι *ᵥ fun r => V r k) 0

theorem entry_eq (σ : E →ₐ[F] E) {β μ ν : Type} [Fintype β] (M : Matrix β β E) (P : Matrix β μ E) (Q : Matrix β ν E)
    (j : μ) (j' : ν) : (Pᵀ * M * Q.map σ) j j' = (fun s => P s j) ⬝ᵥ M *ᵥ (fun s => σ (Q s j')) := by
  simp only [Matrix.mul_apply, transpose_apply, map_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem dbl_form (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (p q p' q' : Fin d → E) :
    Sum.elim p q ⬝ᵥ dbl J *ᵥ (fun s => σ (Sum.elim p' q' s)) = form σ J p p' - form σ J q q' := by
  have : (fun s => σ (Sum.elim p' q' s)) = Sum.elim (fun i => σ (p' i)) (fun i => σ (q' i)) := by
    funext s; cases s <;> rfl
  rw [this, dbl, fromBlocks_mulVec]
  simp only [form, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add, neg_mulVec,
    sumElim_dotProduct_sumElim, dotProduct_neg, sub_eq_add_neg]

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (p q : Fin d → E) : form σ J p q = -σ (form σ J q p) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show σ (J i j) = -J j i from hJ j i]
  ring

end Rat

end GlobalTheory.DiagLagrMove

namespace GlobalTheory.DiagLagrMove

open Matrix

section Rat2

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem form_mulVec (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (u v : Fin d₁ → E) : form σ J (ι *ᵥ u) (ι *ᵥ v) = u ⬝ᵥ (ιᵀ * J * ι.map σ) *ᵥ fun i => σ (v i) := by
  have hv : (fun i => σ ((ι *ᵥ v) i)) = ι.map σ *ᵥ fun i => σ (v i) := by
    ext i; simp [mulVec, dotProduct, map_sum, map_mul]
  rw [form, hv, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u ιᵀ, vecMul_transpose]

theorem exists_rat_unitary [CharZero F] [CharZero E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d d₁ : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (J₁ : Matrix (Fin d₁) (Fin d₁) E) (hJ : ∀ i j, σ (J j i) = -J i j)
    (hJu : J.det ≠ 0) (hJ₁u : J₁.det ≠ 0) (x y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E)
    (xx : form σ J x x = 0) (xy : form σ J x y = 1)
    (orth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (gram : ιᵀ * J * ι.map σ = J₁)
    (e : Fin d ≃ (Unit ⊕ Unit) ⊕ Fin d₁) :
    ∃ g g' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) E, gᵀ * dbl J * g.map σ = dbl J ∧
      g * Matrix.of (fun s j => lagCol x ι (e j) s) = diagCols (Fin d) ∧ g * g' = 1 := by
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have hσ' : ∀ x : E, (σ : E →+* E) ((σ : E →+* E) x) = x := hσ
  have hJd : ((dbl J).map (σ : E →+* E))ᵀ = -dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, hJ]
  have f0 : ∀ v, form σ J 0 v = 0 := fun v => by simp [form]
  have f1 : ∀ p, form σ J p 0 = 0 := fun p => by
    simp only [form, Pi.zero_apply, map_zero]
    rw [show (fun _ : Fin d => (0 : E)) = 0 from rfl, mulVec_zero, dotProduct_zero]
  have fn : ∀ p q, form σ J p (-q) = -form σ J p q := fun p q => by
    simp only [form, Pi.neg_apply, map_neg]
    rw [show (fun i => -σ (q i)) = -(fun i => σ (q i)) from rfl, mulVec_neg, dotProduct_neg]
  have fxι : ∀ u, form σ J x (ι *ᵥ u) = 0 := fun u => by
    rw [form_swap σ hσ hJ, (orth u).1, map_zero, neg_zero]
  have fyι : ∀ u, form σ J (ι *ᵥ u) y = 0 := fun u => (orth u).2
  have fxι' : ∀ u, form σ J (ι *ᵥ u) x = 0 := fun u => (orth u).1
  set V : Matrix (Fin d₁) (Fin d₁) E := J₁⁻¹.map σ with hV
  have hVV : J₁ * V.map σ = 1 := by
    have : V.map σ = J₁⁻¹ := by ext; simp [hV, hσ]
    rw [this, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ₁u)]
  have iso : ∀ m m', lagCol x ι m ⬝ᵥ dbl J *ᵥ (fun s => σ (lagCol x ι m' s)) = 0 := by
    intro m m'
    rcases m with (_ | _) | k <;> rcases m' with (_ | _) | k' <;>
      simp only [lagCol, dbl_form, f0, f1, xx, fxι, fxι', sub_zero, zero_sub, neg_zero, sub_self]
  have dual : ∀ m m', lagCol x ι m ⬝ᵥ dbl J *ᵥ (fun s => σ (lagDual y ι V m' s)) = if m = m' then 1 else 0 := by
    intro m m'
    rcases m with (_ | _) | k <;> rcases m' with (_ | _) | k' <;>
      simp only [lagCol, lagDual, dbl_form, f0, f1, fn, xy, fxι, fyι, sub_zero, zero_sub, neg_zero, sub_self, neg_neg]
    all_goals try (simp; done)
    rw [form_mulVec, gram, single_dotProduct, one_mul]
    have := congrFun (congrFun hVV k) k'
    simp only [Matrix.mul_apply, map_apply, one_apply] at this
    simp only [mulVec, dotProduct]
    rw [this]
    simp [eq_comm]
  have h₁ : (Matrix.of fun s j => lagCol x ι (e j) s)ᵀ * dbl J * (Matrix.of fun s j => lagCol x ι (e j) s).map σ = 0 := by
    ext j j'; rw [entry_eq]; exact iso _ _
  have k₁ : (Matrix.of fun s j => lagCol x ι (e j) s)ᵀ * dbl J *
      (Matrix.of fun s j => lagDual y ι V (e j) s).map σ = 1 := by
    ext j j'; rw [entry_eq]; exact (dual _ _).trans (by simp [one_apply, e.injective.eq_iff])
  have h₂ : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E)ᵀ * dbl J *
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E).map σ = 0 := (isLagr_diagCols σ J).1
  have hm : (fromRows (J⁻¹.map σ) (0 : Matrix (Fin d) (Fin d) E)).map σ = fromRows J⁻¹ (0 : Matrix (Fin d) (Fin d) E) := by
    ext (i | i) j <;> simp [hσ]
  have k₂ : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E)ᵀ * dbl J *
      (fromRows (J⁻¹.map σ) (0 : Matrix (Fin d) (Fin d) E)).map σ = 1 := by
    rw [hm, diagCols, transpose_fromRows, dbl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp [mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJu)]
  obtain ⟨g, g', hg, hgZ, hgg⟩ := exists_unitary hσ' h2 hJd _ _ _ _ h₁ h₂ k₁ k₂
  exact ⟨g, g', hg, hgZ, hgg⟩

end Rat2

end GlobalTheory.DiagLagrMove

namespace GlobalTheory.DiagLagrMove

open Matrix

theorem siegelRule_transport {R E : Type} [CommRing R] [Invertible (2 : R)] [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ}
    {χ : Eˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy Cy' : Matrix β ν E}
    {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)} (hs : IsSplitting C ψ d (actB c) om)
    (hS : SiegelRule c C ψ ξ JA JB d χ Cy om) (g : UG c JB) (S : GL ν E)
    (hg : ((g : GL β E) : Matrix β β E) * Cy' = Cy * (S : Matrix ν ν E)) :
    SiegelRule c C ψ ξ JA JB d χ Cy' om := by
  intro l hl hinv p t hp φ hφ
  have hl' : l ∘ₗ om g⁻¹ ∈ C.adm κ := hs.adm g⁻¹ l hl
  have hgg : ((g⁻¹ : UG c JB) : GL β E).1 * (g : GL β E).1 = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hSS : (S : Matrix ν ν E) * ((S⁻¹ : GL ν E) : Matrix ν ν E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]; rfl
  have hgi : ((g⁻¹ : UG c JB) : GL β E).1 * Cy = Cy' * ((S⁻¹ : GL ν E) : Matrix ν ν E) := by
    calc ((g⁻¹ : UG c JB) : GL β E).1 * Cy = ((g⁻¹ : UG c JB) : GL β E).1 * (Cy * ((S : Matrix ν ν E) *
          ((S⁻¹ : GL ν E) : Matrix ν ν E))) := by rw [hSS, Matrix.mul_one]
      _ = ((g⁻¹ : UG c JB) : GL β E).1 * ((g : GL β E).1 * Cy') * ((S⁻¹ : GL ν E) : Matrix ν ν E) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = Cy' * ((S⁻¹ : GL ν E) : Matrix ν ν E) := by rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]
  have hinv' : ∀ z : Matrix α ν E, ∀ φ ∈ C.sp κ, (l ∘ₗ om g⁻¹) (d.rho ψ (z * Cyᵀ) φ) = (l ∘ₗ om g⁻¹) φ := by
    intro z φ hφ
    simp only [LinearMap.comp_apply]
    rw [hs.impl g⁻¹ _ φ hφ]
    have e1 : actB c g⁻¹ (z * Cyᵀ) = (z * ((S⁻¹ : GL ν E) : Matrix ν ν E)ᵀ) * Cy'ᵀ := by
      unfold actB
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hgi, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e1]
    exact hinv _ _ (hs.pres _ φ hφ)
  have hp' : (((g * p * g⁻¹ : UG c JB) : GL β E) : Matrix β β E) * Cy =
      Cy * ((S * t * S⁻¹ : GL ν E) : Matrix ν ν E) := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [Matrix.mul_assoc, hgi, ← Matrix.mul_assoc, Matrix.mul_assoc (g : GL β E).1, hp,
      ← Matrix.mul_assoc, hg]
    simp only [Matrix.mul_assoc]
  have key := hS (l ∘ₗ om g⁻¹) hl' hinv' (g * p * g⁻¹) (S * t * S⁻¹) hp' (om g φ) (hs.pres g φ hφ)
  simp only [LinearMap.comp_apply] at key
  have e2 : om g⁻¹ (om (g * p * g⁻¹) (om g φ)) = om p φ := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2; group
  have e3 : om g⁻¹ (om g φ) = φ := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e4 : Matrix.GeneralLinearGroup.det (S * t * S⁻¹) = Matrix.GeneralLinearGroup.det t := by
    rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det S), mul_assoc, mul_inv_cancel, mul_one]
  rw [e2, e3, e4] at key
  exact key

theorem det_ne_zero_of_hasSig {m r s : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin m ≃ Fin r ⊕ Fin s := (finCongr hrs.symm).trans finSumFinEquiv.symm
  have h1 : (A.submatrix id e)ᵀ * M * (A.submatrix id e).map star =
      (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e e := by
    rw [← hA]; ext i j; simp [Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [det_submatrix_equiv_self, det_mul, det_mul, det_fromBlocks_zero₂₁, det_one, det_neg, det_one] at h2
  intro h0
  rw [h0, mul_zero, zero_mul] at h2
  simp at h2
  exact pow_ne_zero s (by norm_num) h2.symm

end GlobalTheory.DiagLagrMove

namespace GlobalTheory.DiagLagrMove

open Matrix

theorem siegelRule_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' r₁ s₁ : ℕ),
    W.IsSkew σ B r' s' → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (χ : Chr F E) (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
      (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)),
      IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      SiegelRule (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χ (diagCols (Fin d)) omd →
      ∀ l ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d),
        (∀ (y₁ y₂ : Fin n → AE F E) (Z : Matrix (Fin n) (Fin d₁) (AE F E)), ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          l (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H'.x) + Z * (incM F H'.ι)ᵀ)
            (Matrix.vecMulVec y₂ (incV F H'.x) + Z * (incM F H'.ι)ᵀ)) Ψ) = l Ψ) →
        ∀ (t : (AE F E)ˣ) (p : UG (cA σ) (dbl (incM F W.J))),
          (p.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = t.1 • Sum.elim (incV F H'.x) (0 : Fin d → AE F E) →
          (p.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) →
          (p.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromRows (incM F H'.ι) (incM F H'.ι) =
            Matrix.fromRows (incM F H'.ι) (incM F H'.ι) →
          ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), l (omd p Ψ) = (χ t : ℂ) *
            ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * l Ψ := by
  intro F E _ _ _ _ _ σ B hB n d d₁ X W W₁ H' i₀ i₁ r' s' r₁ s₁ hW hW₁ hH χ dd omd hsp hsieg l hl hinv t p hpa hpb hpc Ψ hΨ

  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have hσ : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star])

  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hdet : ∀ {m r s : ℕ} (J : Matrix (Fin m) (Fin m) E), HasSig (Complex.I • J.map (B.emb w).1) r s → J.det ≠ 0 := by
    intro m r s J h hJ
    apply det_ne_zero_of_hasSig h
    rw [det_smul, show (J.map (B.emb w).1).det = (B.emb w).1 J.det from ((B.emb w).1.map_det J).symm, hJ, map_zero,
      mul_zero]
  have hWd := hdet W.J (hW.sig w)
  have hW₁d := hdet W₁.J (hW₁.sig w)

  have hcard : Fintype.card (Fin d) = Fintype.card ((Unit ⊕ Unit) ⊕ Fin d₁) := by
    have := hH.rank
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_unit]
    omega
  let e : Fin d ≃ (Unit ⊕ Unit) ⊕ Fin d₁ := Fintype.equivOfCardEq hcard
  obtain ⟨g, g', hg, hgZ, hgg⟩ :=
    exists_rat_unitary σ hσ W.J W₁.J hW.skew hWd hW₁d H'.x H'.y H'.ι hH.xx hH.xy hH.orth hH.gram e
  set ιA : E →+* AE F E := inclR (F := F) (AF F) with hιA
  have hc : ∀ {a b : Type} (M : Matrix a b E), (M.map ιA).map (cA σ) = (M.map σ).map ιA := by
    intro a b M; ext i j; simp [hιA, cA, inclR]
  have hd : dbl (incM F W.J) = (dbl W.J).map ιA := by
    ext (i | i) (j | j) <;> simp [dbl, incM, hιA]
  have hgg' : g' * g = 1 := mul_eq_one_comm.1 hgg
  let gGL : GL (Fin d ⊕ Fin d) (AE F E) := ⟨g.map ιA, g'.map ιA,
    by rw [← Matrix.map_mul, hgg, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, hgg', Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hgU : gGL ∈ UG (cA σ) (dbl (incM F W.J)) := by
    show (g.map ιA)ᵀ * dbl (incM F W.J) * (g.map ιA).map (cA σ) = dbl (incM F W.J)
    rw [hc, hd, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  set Cy' : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := incM F (Matrix.of fun s j => lagCol H'.x H'.ι (e j) s) with hCy'
  have hgS : ((⟨gGL, hgU⟩ : UG (cA σ) (dbl (incM F W.J))) : GL (Fin d ⊕ Fin d) (AE F E)).1 * Cy' =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
        ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) := by
    show g.map ιA * (Matrix.of fun s j => lagCol H'.x H'.ι (e j) s).map ιA = _
    rw [← Matrix.map_mul, hgZ, Units.val_one, Matrix.mul_one, diagCols, diagCols, fromRows_map,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hS' := siegelRule_transport hsp hsieg ⟨gGL, hgU⟩ 1 hgS

  have hinv' : ∀ z : Matrix (Fin n) (Fin d) (AE F E), ∀ φ ∈ (adeleClass F).sp (Fin n × Fin d ⊕ Fin n × Fin d),
      l (dd.rho B.ψ (z * Cy'ᵀ) φ) = l φ := by
    intro z φ hφ
    have hz : z * Cy'ᵀ = Matrix.fromCols
        (Matrix.vecMulVec (fun i => z i (e.symm (Sum.inl (Sum.inl ())))) (incV F H'.x) +
          (Matrix.of fun i k => z i (e.symm (Sum.inr k))) * (incM F H'.ι)ᵀ)
        (Matrix.vecMulVec (fun i => z i (e.symm (Sum.inl (Sum.inr ())))) (incV F H'.x) +
          (Matrix.of fun i k => z i (e.symm (Sum.inr k))) * (incM F H'.ι)ᵀ) := by
      ext i (r | r) <;>
      · simp only [Matrix.mul_apply, transpose_apply, hCy', incM, map_apply, of_apply, fromCols_apply_inl,
          fromCols_apply_inr, Matrix.add_apply, vecMulVec_apply, incV]
        rw [← e.symm.sum_comp]
        simp [Fintype.sum_sum_type, lagCol, mulVec, dotProduct, Pi.single_apply, hιA]
    rw [hz]; exact hinv _ _ _ φ hφ

  let dv : (Unit ⊕ Unit) ⊕ Fin d₁ → AE F E :=
    Sum.elim (Sum.elim (fun _ => t.1) (fun _ => (1 : AE F E))) (fun _ => (1 : AE F E))
  let dvi : (Unit ⊕ Unit) ⊕ Fin d₁ → AE F E :=
    Sum.elim (Sum.elim (fun _ => (t⁻¹ : (AE F E)ˣ).1) (fun _ => (1 : AE F E))) (fun _ => (1 : AE F E))
  have hdd : ∀ m, dv m * dvi m = 1 := by rintro ((_ | _) | k) <;> simp [dv, dvi]
  let t₀ : GL (Fin d) (AE F E) := ⟨diagonal (dv ∘ e), diagonal (dvi ∘ e),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext j; exact hdd (e j),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext j; rw [mul_comm]; exact hdd (e j)⟩
  have hdet0 : Matrix.GeneralLinearGroup.det t₀ = t := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show (diagonal (dv ∘ e)).det = t.1
    rw [det_diagonal, show ∏ j, (dv ∘ e) j = ∏ m, dv m from e.prod_comp dv]
    simp [dv, Fintype.prod_sum_type]
  have hcol : ∀ m, ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ
      (fun r => ιA (lagCol H'.x H'.ι m r)) = dv m • (fun r => ιA (lagCol H'.x H'.ι m r)) := by
    rintro ((⟨⟩ | ⟨⟩) | k)
    · have : (fun r => ιA (lagCol H'.x H'.ι (Sum.inl (Sum.inl ())) r)) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) := by
        funext r; cases r <;> simp [lagCol, incV, hιA]
      rw [this, hpa]
      rfl
    · have : (fun r => ιA (lagCol H'.x H'.ι (Sum.inl (Sum.inr ())) r)) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) := by
        funext r; cases r <;> simp [lagCol, incV, hιA]
      rw [this, hpb]; simp [dv]
    · have : (fun r => ιA (lagCol H'.x H'.ι (Sum.inr k) r)) =
          fun r => Matrix.fromRows (incM F H'.ι) (incM F H'.ι) r k := by
        funext r; cases r <;> simp [lagCol, incM, hιA, mulVec, dotProduct, Pi.single_apply]
      rw [this]
      ext r
      have := congrFun (congrFun hpc r) k
      simp only [Matrix.mul_apply] at this
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [this]
      simp [dv]
  have hp : ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Cy' =
      Cy' * (t₀ : Matrix (Fin d) (Fin d) (AE F E)) := by
    show _ = Cy' * diagonal (dv ∘ e)
    ext s j
    rw [mul_diagonal]
    have := congrFun (hcol (e j)) s
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, hCy', incM, map_apply, of_apply, Function.comp_apply]
    rw [this, mul_comm]
  have key := hS' l hl hinv' p t₀ hp Ψ hΨ
  rw [hdet0, Fintype.card_fin] at key
  exact key

end GlobalTheory.DiagLagrMove
