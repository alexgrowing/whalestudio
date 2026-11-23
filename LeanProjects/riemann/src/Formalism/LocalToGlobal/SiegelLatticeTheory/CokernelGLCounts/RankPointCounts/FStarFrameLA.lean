import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarSteps

noncomputable section

open scoped Classical
open Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)

def gram {m n : Type*} (u : n → S.V) (v : m → S.V) : Matrix m n E := fun i j => S.hT (v i) (u j)

def comb {m n : Type*} [Fintype m] (u : m → S.V) (A : Matrix m n E) : n → S.V := fun j => ∑ i, A i j • u i

def om {r : ℕ} (f f' : Fin (r + 1) → S.V) : S.V := ∑ b, (gram S f' f).adjugate b (Fin.last r) • f' b

variable {S}

theorem gram_comb_left {l m n : Type*} [Fintype m] (u : m → S.V) (A : Matrix m n E) (v : l → S.V) :
    gram S (comb S u A) v = gram S u v * A := by
  ext i j
  simp only [gram, comb, Matrix.mul_apply, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem gram_comb_right {l m n : Type*} [Fintype m] (u : l → S.V) (v : m → S.V) (B : Matrix m n E) :
    gram S u (comb S v B) = Bᴴ * gram S u v := by
  ext i j
  simp only [gram, comb, Matrix.mul_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Matrix.conjTranspose_apply, starRingEnd_apply]

theorem gram_add_left {m n : Type*} (u₁ u₂ : n → S.V) (v : m → S.V) :
    gram S (u₁ + u₂) v = gram S u₁ v + gram S u₂ v := by
  ext i j
  simp [gram, map_add]

theorem gram_add_right {m n : Type*} (u : n → S.V) (v₁ v₂ : m → S.V) :
    gram S u (v₁ + v₂) = gram S u v₁ + gram S u v₂ := by
  ext i j
  simp [gram, map_add, LinearMap.add_apply]

theorem gram_swap {m n : Type*} (u : n → S.V) (v : m → S.V) : gram S v u = (gram S u v)ᴴ := by
  ext i j
  simp only [gram, Matrix.conjTranspose_apply]
  have := (LinearMap.isSymm_def.1 S.herm) (u i) (v j)
  rw [← this, starRingEnd_apply, star_star]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem adj_last {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    A.adjugate (Fin.last r) (Fin.last r) = leadMinorE A r := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ r)]
  have hc : (Fin.castLE (Nat.le_succ r) : Fin r → Fin (r + 1)) = Fin.castSucc := funext fun i => Fin.ext rfl
  rw [hc, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem leadMinorE_full {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : leadMinorE A (r + 1) = A.det := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  have hc : (Fin.castLE (le_refl (r + 1)) : Fin (r + 1) → Fin (r + 1)) = id := funext fun i => Fin.ext rfl
  rw [hc, Matrix.submatrix_id_id]

theorem mulVec_adjCol {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    A *ᵥ (fun b => A.adjugate b (Fin.last r)) = A.det • Pi.single (Fin.last r) 1 := by
  ext i
  have h := congrFun (congrFun (Matrix.mul_adjugate A) i) (Fin.last r)
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul, h]

theorem mul_eq_zero_of_last {r : ℕ} (A Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hA : ∀ i j, (i ≠ Fin.last r ∨ j ≠ Fin.last r) → A i j = 0) (hQ : ∀ b, Q (Fin.last r) b = 0) : A * Q = 0 := by
  ext i b
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j = Fin.last r
  · subst hj; rw [hQ, mul_zero]
  · rw [hA i j (Or.inr hj), zero_mul]

theorem quad_last {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hA : ∀ i j, (i ≠ Fin.last r ∨ j ≠ Fin.last r) → A i j = 0) (v : Fin (r + 1) → E) :
    star v ⬝ᵥ (A *ᵥ v) = star (v (Fin.last r)) * A (Fin.last r) (Fin.last r) * v (Fin.last r) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · ring
    · intro j _ hj; rw [hA _ _ (Or.inr hj), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    rw [Finset.sum_eq_zero fun j _ => by rw [hA _ _ (Or.inl hi), zero_mul], mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

def solM {n : Type*} [Fintype n] (H : Matrix n n E) (k ℓ : n → E) : Matrix n n E :=
  (2 : E)⁻¹ • (H - vecMulVec (H *ᵥ k) (star ℓ) + vecMulVec ℓ (star k ᵥ* H))

theorem solM_add {n : Type*} [Fintype n] (H : Matrix n n E) (hH : Hᴴ = H) (k ℓ : n → E) :
    solM H k ℓ + (solM H k ℓ)ᴴ = H := by
  have h1 : ∀ i j, star (H j i) = H i j := fun i j => by
    have := congrFun (congrFun hH i) j; rwa [Matrix.conjTranspose_apply] at this
  have h2 : star (H *ᵥ k) = star k ᵥ* H := by rw [Matrix.star_mulVec, hH]
  have h3 : star (star k ᵥ* H) = H *ᵥ k := by rw [Matrix.star_vecMul, hH, star_star]
  have h2' : ∀ j, star ((H *ᵥ k) j) = (star k ᵥ* H) j := fun j => congrFun h2 j
  have h3' : ∀ j, star ((star k ᵥ* H) j) = (H *ᵥ k) j := fun j => congrFun h3 j
  have h22 : star (2 : E)⁻¹ = (2 : E)⁻¹ := by rw [star_inv₀, star_ofNat]
  ext i j
  simp only [solM, Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply,
    vecMulVec_apply, smul_eq_mul, Pi.star_apply, star_mul', star_add, star_sub, star_star, h22, h1, h2', h3']
  have h2ne : (2 : E) ≠ 0 := two_ne_zero
  field_simp
  ring

theorem solM_mulVec {n : Type*} [Fintype n] (H : Matrix n n E) (k ℓ : n → E) (hk : star k ⬝ᵥ (H *ᵥ k) = 0)
    (hℓ : star ℓ ⬝ᵥ k = 1) : solM H k ℓ *ᵥ k = 0 := by
  have hv : ∀ a b : n → E, vecMulVec a b *ᵥ k = fun i => a i * (b ⬝ᵥ k) := by
    intro a b; ext i; simp [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have hk' : star k ᵥ* H ⬝ᵥ k = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hk
  rw [solM, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, hv, hv, hℓ, hk']
  ext i
  simp

theorem sum_comb {m n : Type*} [Fintype m] [Fintype n] (u : m → S.V) (A : Matrix m n E) (v : n → E) :
    ∑ b, v b • comb S u A b = ∑ i, (A *ᵥ v) i • u i := by
  simp only [comb, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]

theorem sum_mem_X {r : ℕ} {T : E} (F : FlagG S r T) (v : Fin (r + 1) → E) (hv : v (Fin.last r) = 0) :
    ∑ a, v a • F.fvec a ∈ F.X := by
  rw [Fin.sum_univ_castSucc, hv, zero_smul, add_zero]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  simp only [FlagG.fvec, Fin.snoc_castSucc]
  exact Submodule.subset_span ⟨a, rfl⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem frame_la {r : ℕ} {T T' : E} (F : FlagG S r T) (f₁ : Fin (r + 1) → S.V)
    (h1 : ∀ a b, (a ≠ Fin.last r ∨ b ≠ Fin.last r) → S.hT (f₁ a) (f₁ b) = 0)
    (h2 : S.hT (f₁ (Fin.last r)) (f₁ (Fin.last r)) = -T')
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hZ : Z.det ≠ 0) (hZ₁ : (gram S f₁ F.fvec).det ≠ 0)
    (hx : leadMinorE (gram S f₁ F.fvec) r * Z.det = leadMinorE Z r * (gram S f₁ F.fvec).det) :
    ∃ F₂ : FlagG S r T', Zhat F F₂ = Z ∧
      Z.det • om S F.fvec f₁ - (gram S f₁ F.fvec).det • om S F.fvec F₂.fvec ∈ F.X ∧
      ∀ b, F₂.fvec b ∈ Submodule.span E (Set.range (Sum.elim F.fvec f₁)) := by
  set f := F.fvec with hf
  set Z₁ := gram S f₁ f with hZ₁def
  set l := Fin.last r with hl
  set Γ' := gram S f₁ f₁ with hΓ'

  have hfe : ∀ a : Fin r, f (Fin.castSucc a) = F.e a := fun a => by simp [hf, FlagG.fvec]
  have hfz : f l = F.z := by simp [hf, hl, FlagG.fvec]
  have hΓ : ∀ i j, (i ≠ l ∨ j ≠ l) → gram S f f i j = 0 := by
    intro i j hij
    simp only [gram]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hl.symm (by simpa using hij)
      | cast b =>
        rw [hfz, hfe, ← LinearMap.IsSymm.eq_iff S.herm]
        exact F.z_orth b
    | cast a =>
      induction j using Fin.lastCases with
      | last => rw [hfz, hfe]; exact F.z_orth a
      | cast b => rw [hfe, hfe]; exact F.e_iso a b
  have hΓ'0 : ∀ i j, (i ≠ l ∨ j ≠ l) → Γ' i j = 0 := fun i j h => h1 i j h
  have hΓ'h : Γ'ᴴ = Γ' := (gram_swap f₁ f₁).symm

  set k : Fin (r + 1) → E := fun b => Z.adjugate b l with hk
  set k₁ : Fin (r + 1) → E := fun b => Z₁.adjugate b l with hk₁
  have hZk : Z *ᵥ k = Z.det • Pi.single l 1 := mulVec_adjCol Z
  have hZk₁ : Z₁ *ᵥ k₁ = Z₁.det • Pi.single l 1 := mulVec_adjCol Z₁
  have hu₁ : IsUnit Z₁.det := isUnit_iff_ne_zero.2 hZ₁
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.2 hZ
  set P := Z₁⁻¹ * Z with hP
  have hZ₁P : Z₁ * P = Z := Matrix.mul_nonsing_inv_cancel_left Z₁ Z hu₁
  clear_value P
  have hPk : P *ᵥ k = (Z.det / Z₁.det) • k₁ := by
    have h0 : Z₁ *ᵥ (P *ᵥ k - (Z.det / Z₁.det) • k₁) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hZ₁P, hZk, Matrix.mulVec_smul, hZk₁, smul_smul,
        div_mul_cancel₀ _ hZ₁, sub_self]
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hZ₁ h0)
  have hkl : k l = leadMinorE Z r := adj_last Z
  have hPkl : (P *ᵥ k) l = k l := by
    rw [hPk, Pi.smul_apply, smul_eq_mul, hkl]
    show Z.det / Z₁.det * Z₁.adjugate l l = _
    rw [adj_last Z₁]
    field_simp
    rw [mul_comm, hx]
    ring

  set H := Γ' - Pᴴ * Γ' * P with hH
  have hHh : Hᴴ = H := by
    simp only [hH, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hΓ'h,
      Matrix.mul_assoc]
  have hkHk : star k ⬝ᵥ (H *ᵥ k) = 0 := by
    have e1 : star k ⬝ᵥ ((Pᴴ * Γ' * P) *ᵥ k) = star (P *ᵥ k) ⬝ᵥ (Γ' *ᵥ (P *ᵥ k)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    rw [hH, Matrix.sub_mulVec, dotProduct_sub, e1, quad_last Γ' hΓ'0, quad_last Γ' hΓ'0, hPkl, sub_self]
  have hk0 : k ≠ 0 := by
    intro h
    have := hZk
    rw [h, Matrix.mulVec_zero] at this
    have h' := congrFun this l
    simp only [Pi.zero_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h'
    exact hZ h'.symm
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hk0
  set ℓ : Fin (r + 1) → E := fun i => if i = j then star (k j)⁻¹ else 0 with hℓ
  have hℓk : star ℓ ⬝ᵥ k = 1 := by
    simp only [dotProduct, Pi.star_apply, hℓ]
    rw [Finset.sum_eq_single j]
    · simp only [ite_true, star_star]
      exact inv_mul_cancel₀ hj
    · intro i _ hi; simp [if_neg hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  set M := solM H k ℓ with hM
  have hMH : M + Mᴴ = H := solM_add H hHh k ℓ
  have hMk : M *ᵥ k = 0 := solM_mulVec H k ℓ hkHk hℓk

  set Q := (M * Z⁻¹)ᴴ with hQ
  have hQZ : Qᴴ * Z = M := by
    rw [hQ, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul_cancel_right Z M hu]
  have hZinv : Z⁻¹ *ᵥ Pi.single l 1 = (Z.det)⁻¹ • k := by
    have h0 : Z *ᵥ (Z⁻¹ *ᵥ Pi.single l 1 - (Z.det)⁻¹ • k) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Z hu, Matrix.one_mulVec,
        Matrix.mulVec_smul, hZk, smul_smul, inv_mul_cancel₀ hZ, one_smul, sub_self]
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hZ h0)
  have hQl : ∀ b, Q l b = 0 := by
    intro b
    have e : (M * Z⁻¹) *ᵥ Pi.single l 1 = 0 := by
      rw [← Matrix.mulVec_mulVec, hZinv, Matrix.mulVec_smul, hMk, smul_zero]
    have e' := congrFun e b
    rw [Matrix.mulVec_single_one] at e'
    simp only [hQ, Matrix.conjTranspose_apply]
    rw [show (M * Z⁻¹) b l = 0 from e', star_zero]
  have hΓQ : gram S f f * Q = 0 := mul_eq_zero_of_last _ Q hΓ hQl

  set f₂ : Fin (r + 1) → S.V := comb S f₁ P + comb S f Q with hf₂
  have hZ2 : gram S f₂ f = Z := by
    rw [hf₂, gram_add_left, gram_comb_left, gram_comb_left, ← hZ₁def, hZ₁P, hΓQ, add_zero]
  have hG2 : gram S f₂ f₂ = Γ' := by
    have e1 : gram S f₂ f₁ = Γ' * P + Z₁ᴴ * Q := by
      rw [hf₂, gram_add_left, gram_comb_left, gram_comb_left, gram_swap f₁ f]
    have e2 : Pᴴ * (Z₁ᴴ * Q) = Mᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hZ₁P, ← hQZ, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    calc gram S f₂ f₂ = gram S f₂ (comb S f₁ P) + gram S f₂ (comb S f Q) := by rw [hf₂, gram_add_right]
      _ = Pᴴ * (Γ' * P + Z₁ᴴ * Q) + Qᴴ * Z := by rw [gram_comb_right, gram_comb_right, e1, hZ2]
      _ = Pᴴ * Γ' * P + (M + Mᴴ) := by rw [Matrix.mul_add, e2, hQZ, Matrix.mul_assoc]; abel
      _ = Γ' := by rw [hMH, hH]; abel
  have hG2e : ∀ a b, S.hT (f₂ a) (f₂ b) = S.hT (f₁ a) (f₁ b) := fun a b => congrFun (congrFun hG2 a) b
  have hind : LinearIndependent E (fun a : Fin r => f₂ (Fin.castSucc a)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    set c : Fin (r + 1) → E := Fin.snoc g 0 with hc
    have hsum : ∑ b, c b • f₂ b = 0 := by
      rw [Fin.sum_univ_castSucc]
      simp only [hc, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
      exact hg
    have hZc : Z *ᵥ c = 0 := by
      ext i
      have := congrArg (S.hT (f i)) hsum
      rw [map_sum, map_zero] at this
      simp only [map_smul, smul_eq_mul] at this
      rw [← hZ2]
      simpa [Matrix.mulVec, dotProduct, gram, mul_comm] using this
    have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hZ hZc) (Fin.castSucc a)
    simpa [hc] using this
  have hiso : ∀ a b : Fin r, S.hT (f₂ (Fin.castSucc a)) (f₂ (Fin.castSucc b)) = 0 := fun a b => by
    rw [hG2e]; exact h1 _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
  have horth : ∀ a : Fin r, S.hT (f₂ (Fin.castSucc a)) (f₂ l) = 0 := fun a => by
    rw [hG2e]; exact h1 _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
  have hnorm : S.hT (f₂ l) (f₂ l) = -T' := by rw [hG2e]; exact h2
  let F₂ : FlagG S r T' := ⟨fun a => f₂ (Fin.castSucc a), f₂ l, hind, hiso, horth, hnorm⟩
  have hfv : F₂.fvec = f₂ := Fin.snoc_init_self f₂
  refine ⟨F₂, ?_, ?_, ?_⟩
  · ext a b
    simp only [Zhat, brS, hfv]
    exact congrFun (congrFun hZ2 a) b
  · rw [hfv]
    have hom2 : om S f f₂ = (Z.det / Z₁.det) • om S f f₁ + ∑ a, (Q *ᵥ k) a • f a := by
      simp only [om, hZ2]
      rw [show (∑ b, Z.adjugate b (Fin.last r) • f₂ b) = ∑ b, k b • f₂ b from rfl, hf₂]
      simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
      rw [sum_comb, sum_comb, hPk]
      simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum]
      rfl
    have hx0 : (Q *ᵥ k) l = 0 := by
      simp only [Matrix.mulVec, dotProduct, hQl, zero_mul, Finset.sum_const_zero]
    rw [hom2, smul_add, smul_smul, mul_div_cancel₀ _ hZ₁, sub_add_eq_sub_sub, sub_self, zero_sub]
    exact F.X.neg_mem (F.X.smul_mem _ (sum_mem_X F _ hx0))
  · intro b
    rw [hfv, hf₂]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨Sum.inr c, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA
