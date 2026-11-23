import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct

namespace GroundTheory.GroupCoh

variable {k G : Type u} [CommRing k] [Group G]

section Indices

variable {M : Type*} [Monoid M]

theorem partialProd_add {m r p q : ℕ} (x : Fin m → M) (y : Fin r → M) (hpr : p + r ≤ m)
    (hy : ∀ j : Fin r, y j = x ⟨p + j, by omega⟩) (hq : q ≤ r) :
    Fin.partialProd x ⟨p + q, by omega⟩ =
      Fin.partialProd x ⟨p, by omega⟩ * Fin.partialProd y ⟨q, by omega⟩ := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 := Fin.partialProd_succ x ⟨p + q, by omega⟩
    have h2 := Fin.partialProd_succ y ⟨q, by omega⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h1 h2
    rw [show (⟨p + (q + 1), by omega⟩ : Fin (m + 1)) = ⟨p + q + 1, by omega⟩ from
      Fin.ext (by simp only; omega), h1, h2, ih (by omega), hy, mul_assoc]

theorem partialProd_contractNth_of_lt {m p : ℕ} (x : Fin (m + 1) → M) (j : Fin (m + 1))
    (hp : p ≤ m) (hj : (j : ℕ) < p) :
    Fin.partialProd (Fin.contractNth j (· * ·) x) ⟨p, by omega⟩ =
      Fin.partialProd x ⟨p + 1, by omega⟩ := by
  rw [Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  congr 1
  rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · simp [Fin.le_def]; omega

theorem partialProd_contractNth_of_le {m p : ℕ} (x : Fin (m + 1) → M) (j : Fin (m + 1))
    (hp : p ≤ m) (hj : p ≤ (j : ℕ)) :
    Fin.partialProd (Fin.contractNth j (· * ·) x) ⟨p, by omega⟩ =
      Fin.partialProd x ⟨p, by omega⟩ := by
  rw [Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  congr 1
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · simp [Fin.lt_def]; omega

variable {α : Type*}

theorem contractNth_prefix {m p : ℕ} (op : α → α → α) (x : Fin (m + 1) → α) (j : Fin (m + 1))
    (j' : Fin (p + 1)) (hp : p ≤ m) (hj : (j : ℕ) = j') :
    (fun l : Fin p => Fin.contractNth j op x ⟨l, by omega⟩) =
      Fin.contractNth j' op (fun l : Fin (p + 1) => x ⟨l, by omega⟩) := by
  funext l
  simp only [Fin.contractNth, Fin.castSucc_mk, Fin.succ_mk, hj]
  rfl

theorem contractNth_prefix_of_le {m p : ℕ} (op : α → α → α) (x : Fin (m + 1) → α)
    (j : Fin (m + 1)) (hj : p ≤ (j : ℕ)) :
    (fun l : Fin p => Fin.contractNth j op x ⟨l, by omega⟩) = fun l : Fin p => x ⟨l, by omega⟩ := by
  funext l
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
  rfl

theorem contractNth_suffix_of_lt {m p q : ℕ} (op : α → α → α) (x : Fin (m + 1) → α)
    (j : Fin (m + 1)) (hpq : p + q ≤ m) (hj : (j : ℕ) < p) :
    (fun l : Fin q => Fin.contractNth j op x ⟨p + l, by omega⟩) =
      fun l : Fin q => x ⟨p + 1 + l, by omega⟩ := by
  funext l
  rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
  simp only [Fin.succ_mk]
  congr 2
  omega

theorem contractNth_suffix {m p q : ℕ} (op : α → α → α) (x : Fin (m + 1) → α) (j : Fin (m + 1))
    (j' : Fin (q + 1)) (hpq : p + q = m) (hj : (j : ℕ) = p + j') :
    (fun l : Fin q => Fin.contractNth j op x ⟨p + l, by omega⟩) =
      Fin.contractNth j' op (fun l : Fin (q + 1) => x ⟨p + l, by omega⟩) := by
  funext l
  simp only [Fin.contractNth, Fin.castSucc_mk, Fin.succ_mk, hj]
  by_cases h1 : (l : ℕ) < j'
  · rw [if_pos (by omega), if_pos h1]
    rfl
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : (l : ℕ) = j'
    · rw [if_pos (by omega), if_pos h2]
      rfl
    · rw [if_neg (by omega), if_neg h2]
      rfl

end Indices

section Cochains

variable {A B : Rep k G} {p q n : ℕ}

def cupCochain (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    (Fin n → G) → (A ⊗ B : Rep k G) := fun x =>
  f (fun i : Fin p => x ⟨i, by omega⟩) ⊗ₜ[k]
    B.ρ (Fin.partialProd x ⟨p, by omega⟩) (g fun j : Fin q => x ⟨p + j, by omega⟩)

theorem cupCochain_apply (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B)
    (x : Fin n → G) :
    cupCochain h f g x = f (fun i : Fin p => x ⟨i, by omega⟩) ⊗ₜ[k]
      B.ρ (Fin.partialProd x ⟨p, by omega⟩) (g fun j : Fin q => x ⟨p + j, by omega⟩) :=
  rfl

theorem d_cupCochain (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    (inhomogeneousCochains.d (A ⊗ B) n).hom (cupCochain h f g) =
      cupCochain (by omega) ((inhomogeneousCochains.d A p).hom f) g +
        (-1 : k) ^ p • cupCochain (by omega) f ((inhomogeneousCochains.d B q).hom g) := by
  subst h
  funext x
  simp only [inhomogeneousCochains.d_hom_apply, cupCochain_apply, Pi.add_apply, Pi.smul_apply]
  have hs : ∀ {M : Type u} [AddCommMonoid M] (F : Fin (p + q + 1) → M),
      ∑ j, F j = ∑ i : Fin p, F (Fin.castAdd (q + 1) i) + ∑ m : Fin (q + 1), F (Fin.natAdd p m) :=
    fun F => Fin.sum_univ_add (a := p) (b := q + 1) F
  rw [hs, Fin.sum_univ_castSucc (n := p)]
  have e0 : ((A ⊗ B).ρ (x 0))
      ((f fun i : Fin p => x (⟨i, by omega⟩ : Fin (p + q)).succ) ⊗ₜ[k]
        B.ρ (Fin.partialProd (fun i : Fin (p + q) => x i.succ) ⟨p, by omega⟩)
          (g fun j : Fin q => x (⟨p + j, by omega⟩ : Fin (p + q)).succ)) =
      A.ρ (x 0) (f fun i : Fin p => x (⟨i, by omega⟩ : Fin (p + q)).succ) ⊗ₜ[k]
        B.ρ (Fin.partialProd x ⟨p + 1, by omega⟩) (g fun j : Fin q => x ⟨p + 1 + j, by omega⟩) := by
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul, ← Module.End.mul_apply,
      ← map_mul]
    have hP : x 0 * Fin.partialProd (fun i : Fin (p + q) => x i.succ) ⟨p, by omega⟩ =
        Fin.partialProd x ⟨p + 1, by omega⟩ := by
      have := Fin.partialProd_succ' x ⟨p, by omega⟩
      simp only [Fin.succ_mk] at this
      rw [this]
      rfl
    have hg : (fun j : Fin q => x (⟨p + j, by omega⟩ : Fin (p + q)).succ) =
        fun j : Fin q => x ⟨p + 1 + j, by omega⟩ := by
      funext j
      congr 1
      ext
      simp only [Fin.val_succ]
      omega
    rw [hP, hg]
  have e1 : ∀ i : Fin p, (-1 : k) ^ ((Fin.castAdd (q + 1) i : Fin (p + q + 1)) + 1 : ℕ) •
      ((f fun l : Fin p =>
          Fin.contractNth (n := p + q) (Fin.castAdd (q + 1) i) (· * ·) x ⟨l, by omega⟩) ⊗ₜ[k]
        B.ρ (Fin.partialProd
            (Fin.contractNth (n := p + q) (Fin.castAdd (q + 1) i) (· * ·) x) ⟨p, by omega⟩)
          (g fun j : Fin q =>
            Fin.contractNth (n := p + q) (Fin.castAdd (q + 1) i) (· * ·) x ⟨p + j, by omega⟩)) =
      ((-1 : k) ^ ((Fin.castSucc i : ℕ) + 1) •
          f (Fin.contractNth (Fin.castSucc i) (· * ·) fun l : Fin (p + 1) => x ⟨l, by omega⟩)) ⊗ₜ[k]
        B.ρ (Fin.partialProd x ⟨p + 1, by omega⟩) (g fun j : Fin q => x ⟨p + 1 + j, by omega⟩) := by
    intro i
    rw [contractNth_prefix _ x _ (Fin.castSucc i) (by omega) (by simp),
      partialProd_contractNth_of_lt _ _ (by omega) (by simp),
      contractNth_suffix_of_lt _ x _ (by omega) (by simp), TensorProduct.smul_tmul']
    simp
  have e2 : ∀ m : Fin (q + 1), (-1 : k) ^ ((Fin.natAdd p m : Fin (p + q + 1)) + 1 : ℕ) •
      ((f fun l : Fin p =>
          Fin.contractNth (n := p + q) (Fin.natAdd p m) (· * ·) x ⟨l, by omega⟩) ⊗ₜ[k]
        B.ρ (Fin.partialProd
            (Fin.contractNth (n := p + q) (Fin.natAdd p m) (· * ·) x) ⟨p, by omega⟩)
          (g fun j : Fin q =>
            Fin.contractNth (n := p + q) (Fin.natAdd p m) (· * ·) x ⟨p + j, by omega⟩)) =
      (-1 : k) ^ p • ((f fun l : Fin p => x ⟨l, by omega⟩) ⊗ₜ[k]
        B.ρ (Fin.partialProd x ⟨p, by omega⟩) ((-1 : k) ^ ((m : ℕ) + 1) •
          g (Fin.contractNth m (· * ·) fun j : Fin (q + 1) => x ⟨p + j, by omega⟩))) := by
    intro m
    rw [contractNth_prefix_of_le _ x _ (by simp), partialProd_contractNth_of_le _ _ (by omega) (by simp),
      contractNth_suffix _ x _ m rfl (by simp), map_smul, TensorProduct.tmul_smul, smul_smul,
      ← pow_add]
    congr 2
  rw [e0, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_congr rfl fun m _ => e2 m]
  have hlast : (Fin.contractNth (Fin.last p) (· * ·) fun l : Fin (p + 1) => x ⟨l, by omega⟩) =
      fun l : Fin p => x ⟨l, by omega⟩ := by
    funext l
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
    rfl
  have hT : A.ρ (x ⟨((0 : Fin (p + 1)) : ℕ), by omega⟩)
      (f fun i : Fin p => x ⟨(i.succ : ℕ), by omega⟩) =
      A.ρ (x 0) (f fun i : Fin p => x (⟨i, by omega⟩ : Fin (p + q)).succ) := rfl
  have hG : (fun i : Fin q => x ⟨p + (i.succ : ℕ), by omega⟩) =
      fun j : Fin q => x ⟨p + 1 + j, by omega⟩ := by
    funext j
    congr 1
    ext
    simp only [Fin.val_succ]
    omega
  have hP : B.ρ (Fin.partialProd x ⟨p, by omega⟩) (B.ρ (x ⟨p + ((0 : Fin (q + 1)) : ℕ), by omega⟩)
      (g fun j : Fin q => x ⟨p + 1 + j, by omega⟩)) =
      B.ρ (Fin.partialProd x ⟨p + 1, by omega⟩) (g fun j : Fin q => x ⟨p + 1 + j, by omega⟩) := by
    rw [← Module.End.mul_apply, ← map_mul]
    congr 2
    have := Fin.partialProd_succ x ⟨p, by omega⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at this
    rw [this]
    rfl
  rw [hlast, hT, hG, map_add, TensorProduct.tmul_add, smul_add, hP, TensorProduct.add_tmul,
    TensorProduct.add_tmul, ← TensorProduct.smul_tmul', TensorProduct.sum_tmul, map_sum,
    TensorProduct.tmul_sum, Finset.smul_sum, Fin.val_last, pow_succ, mul_neg_one, neg_smul]
  abel

theorem partialProd_prefix {M : Type*} [Monoid M] {m m' j : ℕ} (x : Fin m' → M) (hm : m ≤ m')
    (hj : j ≤ m) :
    Fin.partialProd (fun i : Fin m => x ⟨i, by omega⟩) ⟨j, by omega⟩ =
      Fin.partialProd x ⟨j, by omega⟩ := by
  induction j with
  | zero => simp [Fin.partialProd]
  | succ j ih =>
    have h1 := Fin.partialProd_succ x ⟨j, by omega⟩
    have h2 := Fin.partialProd_succ (fun i : Fin m => x ⟨i, by omega⟩) ⟨j, by omega⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h1 h2
    rw [h1, h2, ih (by omega)]

theorem partialProd_mk_zero {M : Type*} [Monoid M] {m : ℕ} (x : Fin m → M) (h : 0 < m + 1) :
    Fin.partialProd x ⟨0, h⟩ = 1 := by
  simp [Fin.partialProd]

theorem tensor_ρ_tmul (X Y : Rep k G) (s : G) (a : X) (b : Y) :
    (X ⊗ Y).ρ s (a ⊗ₜ[k] b) = X.ρ s a ⊗ₜ[k] Y.ρ s b :=
  rfl

theorem associator_hom_tmul (X Y Z : Rep k G) (a : X) (b : Y) (c : Z) :
    (α_ X Y Z).hom.hom (((a ⊗ₜ[k] b : (X ⊗ Y : Rep k G)) ⊗ₜ[k] c : ((X ⊗ Y) ⊗ Z : Rep k G))) =
      a ⊗ₜ[k] (b ⊗ₜ[k] c) :=
  rfl

theorem leftUnitor_hom_tmul (X : Rep k G) (c : k) (a : X) :
    (λ_ X).hom.hom ((c ⊗ₜ[k] a : (𝟙_ (Rep k G) ⊗ X : Rep k G))) = c • a :=
  rfl

theorem rightUnitor_hom_tmul (X : Rep k G) (a : X) (c : k) :
    (ρ_ X).hom.hom ((a ⊗ₜ[k] c : (X ⊗ 𝟙_ (Rep k G) : Rep k G))) = c • a :=
  rfl

def cupₗ (h : p + q = n) :
    ((Fin p → G) → A) →ₗ[k] ((Fin q → G) → B) →ₗ[k] ((Fin n → G) → (A ⊗ B : Rep k G)) :=
  LinearMap.mk₂ k (cupCochain h)
    (fun f f' g => by funext x; simp [cupCochain_apply, TensorProduct.add_tmul])
    (fun c f g => by funext x; simp [cupCochain_apply, TensorProduct.smul_tmul'])
    (fun f g g' => by funext x; simp [cupCochain_apply, TensorProduct.tmul_add])
    (fun c f g => by funext x; simp [cupCochain_apply, TensorProduct.tmul_smul])

@[simp]
theorem cupₗ_apply (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    cupₗ h f g = cupCochain h f g :=
  rfl

variable (A B p q) in

def cupCochainsTensor :
    ((Fin p → G) → A) ⊗[k] ((Fin q → G) → B) →ₗ[k] ((Fin (p + q) → G) → (A ⊗ B : Rep k G)) :=
  TensorProduct.lift (cupₗ rfl)

@[simp]
theorem cupCochainsTensor_tmul (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    cupCochainsTensor A B p q (f ⊗ₜ g) = cupCochain rfl f g :=
  rfl

theorem tensorHom_cupCochain {A' B' : Rep k G} (φ : A ⟶ A') (ψ : B ⟶ B') (h : p + q = n)
    (f : (Fin p → G) → A) (g : (Fin q → G) → B) (x : Fin n → G) :
    (φ ⊗ₘ ψ).hom (cupCochain h f g x) =
      cupCochain h (fun y => φ.hom (f y)) (fun y => ψ.hom (g y)) x := by
  change φ.hom _ ⊗ₜ[k] ψ.hom _ = _
  rw [Rep.hom_comm_apply]
  rfl

theorem associator_cupCochain {C : Rep k G} {r m l : ℕ} (h₁ : p + q = m) (h₂ : m + r = n)
    (h₃ : q + r = l) (h₄ : p + l = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B)
    (e : (Fin r → G) → C) (x : Fin n → G) :
    (α_ A B C).hom.hom (cupCochain h₂ (cupCochain h₁ f g) e x) =
      cupCochain h₄ f (cupCochain h₃ g e) x := by
  subst h₁ h₂ h₃
  simp only [cupCochain_apply]
  rw [associator_hom_tmul, tensor_ρ_tmul, ← Module.End.mul_apply,
    ← map_mul, ← partialProd_add x (fun j : Fin (q + r) => x ⟨p + j, by omega⟩) (by omega)
      (fun j => rfl) (by omega), partialProd_prefix x (by omega) (by omega)]
  have hE : (fun j : Fin r => x ⟨p + (q + j), by omega⟩) = fun j : Fin r => x ⟨p + q + j, by omega⟩ :=
    funext fun j => congrArg x (Fin.ext (by simp only; omega))
  rw [hE]

def oneCochain : (Fin 0 → G) → (𝟙_ (Rep k G) : Rep k G) := fun _ => (1 : k)

theorem leftUnitor_oneCochain_cupCochain (f : (Fin q → G) → A) (x : Fin q → G) :
    (λ_ A).hom.hom (cupCochain (zero_add q) oneCochain f x) = f x := by
  simp only [cupCochain_apply, oneCochain, partialProd_mk_zero, map_one, Module.End.one_apply]
  rw [leftUnitor_hom_tmul, one_smul]
  exact congrArg f (funext fun j => congrArg x (Fin.ext (zero_add _)))

theorem rightUnitor_cupCochain_oneCochain (f : (Fin p → G) → A) (x : Fin p → G) :
    (ρ_ A).hom.hom (cupCochain (add_zero p) f oneCochain x) = f x := by
  simp only [cupCochain_apply, oneCochain]
  rw [rightUnitor_hom_tmul]
  exact one_smul k _

end Cochains

end GroundTheory.GroupCoh
