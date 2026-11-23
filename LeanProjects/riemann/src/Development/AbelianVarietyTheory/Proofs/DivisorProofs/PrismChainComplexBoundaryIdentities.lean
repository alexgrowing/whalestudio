import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlternatingSumZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PrCx

open SimplexCategory

theorem alt_sum_zero {A : Type*} [AddCommGroup A] {n : ℕ} (G : (SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 2)) → A) :
    ∑ i : Fin (n + 3), ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • G (δ j ≫ δ i) = 0 :=
  _root_.UpperTheory.Reformulated.B.AlternatingSumZero.alt_sum_zero G

end GlobalTheory.EtC.PrCx

namespace GlobalTheory.EtC.PrCx

open SimplexCategory Finsupp

variable {N : ℕ}

theorem d₁_zero {r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) : Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

theorem d₁_succ {p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) = ∑ i : Fin (p + 2), single ⟨p, r, δ i ≫ a, b⟩ ((-1) ^ (i : ℕ)) := rfl

theorem d₂_zero {p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) : Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

theorem d₂_succ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) = ∑ j : Fin (r + 2), single ⟨p, r, a, δ j ≫ b⟩ ((-1) ^ (j : ℕ)) := rfl

variable (N) in

def D₁ : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := linearCombination ℤ fun z => z.d₁

variable (N) in

def D₂ : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := linearCombination ℤ fun z => z.d₂

variable (N) in

def E : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := linearCombination ℤ fun z : Pr N => (-1 : ℤ) ^ z.1 • single z (1 : ℤ)

theorem D₁_single (z : Pr N) (c : ℤ) : D₁ N (single z c) = c • z.d₁ := by simp [D₁]

theorem D₂_single (z : Pr N) (c : ℤ) : D₂ N (single z c) = c • z.d₂ := by simp [D₂]

theorem E_single (z : Pr N) (c : ℤ) : E N (single z c) = (-1 : ℤ) ^ z.1 • single z c := by
  rw [E, linearCombination_single, smul_comm, smul_single_one]

theorem d_single (z : Pr N) (c : ℤ) : Pr.d N (single z c) = c • (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  simp [Pr.d]

theorem E_d₂ (z : Pr N) : E N z.d₂ = (-1 : ℤ) ^ z.1 • z.d₂ := by
  obtain ⟨p, r, a, b⟩ := z
  rcases r with _ | r
  · simp [d₂_zero]
  · simp [d₂_succ, map_sum, E_single, Finset.smul_sum]

theorem E_d₁ (z : Pr N) : E N z.d₁ = -((-1 : ℤ) ^ z.1 • z.d₁) := by
  obtain ⟨p, r, a, b⟩ := z
  rcases p with _ | p
  · simp [d₁_zero]
  · simp [d₁_succ, map_sum, E_single, Finset.smul_sum, pow_succ]

theorem d_eq (c : Pr N →₀ ℤ) : Pr.d N c = D₁ N c + E N (D₂ N c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; abel
  | single z c => simp [d_single, D₁_single, D₂_single, E_d₂]

theorem E_E (c : Pr N →₀ ℤ) : E N (E N c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single z c => rw [E_single, map_zsmul, E_single, smul_smul, ← mul_pow]; simp

theorem D₂_E (c : Pr N →₀ ℤ) : D₂ N (E N c) = E N (D₂ N c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single z c => rw [E_single, map_zsmul, D₂_single, map_zsmul, E_d₂, smul_comm]

theorem D₁_E (c : Pr N →₀ ℤ) : D₁ N (E N c) = -E N (D₁ N c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; abel
  | single z c => rw [E_single, map_zsmul, D₁_single, map_zsmul, E_d₁, smul_neg, smul_comm, neg_neg]

theorem D₁_D₁ (c : Pr N →₀ ℤ) : D₁ N (D₁ N c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single z c =>
    rw [D₁_single, map_zsmul]
    suffices D₁ N (Pr.d₁ z) = 0 by rw [this, smul_zero]
    obtain ⟨p, r, a, b⟩ := z
    rcases p with _ | p
    · simp [d₁_zero]
    rcases p with _ | p
    · simp [d₁_succ, map_sum, D₁_single, d₁_zero]
    have h := alt_sum_zero (n := p) (fun θ => single (⟨p, r, θ ≫ a, b⟩ : Pr N) (1 : ℤ))
    rw [d₁_succ, map_sum]
    simp only [D₁_single, d₁_succ, Finset.smul_sum]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [smul_single, Category.assoc]

theorem D₂_D₂ (c : Pr N →₀ ℤ) : D₂ N (D₂ N c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single z c =>
    rw [D₂_single, map_zsmul]
    suffices D₂ N (Pr.d₂ z) = 0 by rw [this, smul_zero]
    obtain ⟨p, r, a, b⟩ := z
    rcases r with _ | r
    · simp [d₂_zero]
    rcases r with _ | r
    · simp [d₂_succ, map_sum, D₂_single, d₂_zero]
    have h := alt_sum_zero (n := r) (fun θ => single (⟨p, r, a, θ ≫ b⟩ : Pr N) (1 : ℤ))
    rw [d₂_succ, map_sum]
    simp only [D₂_single, d₂_succ, Finset.smul_sum]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [smul_single, Category.assoc]

theorem D₁_D₂ (c : Pr N →₀ ℤ) : D₁ N (D₂ N c) = D₂ N (D₁ N c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single z c =>
    rw [D₁_single, D₂_single, map_zsmul, map_zsmul]
    congr 1
    obtain ⟨p, r, a, b⟩ := z
    rcases p with _ | p <;> rcases r with _ | r
    · simp [d₁_zero, d₂_zero]
    · simp [d₁_zero, d₂_succ, map_sum, D₁_single]
    · simp [d₂_zero, d₁_succ, map_sum, D₂_single]
    · simp only [d₁_succ, d₂_succ, map_sum, D₁_single, D₂_single, Finset.smul_sum, smul_single, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]

theorem d_d (c : Pr N →₀ ℤ) : Pr.d N (Pr.d N c) = 0 := by
  rw [d_eq (Pr.d N c), d_eq c]
  simp only [map_add, D₁_E, D₂_E, D₁_D₁, D₂_D₂, D₁_D₂, E_E, map_zero, map_neg]
  abel

end GlobalTheory.EtC.PrCx

namespace GlobalTheory.EtC.PrCx

open SimplexCategory Finsupp

theorem push_single {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) (c : ℤ) :
    Pr.push θ (single z c) = single (⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ : Pr M) c := by
  simp [Pr.push]

theorem push_d₁ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₁ = Pr.d₁ (⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ : Pr M) := by
  obtain ⟨p, r, a, b⟩ := z
  rcases p with _ | p
  · simp [d₁_zero]
  · simp [d₁_succ, map_sum, push_single, Category.assoc]

theorem push_d₂ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₂ = Pr.d₂ (⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ : Pr M) := by
  obtain ⟨p, r, a, b⟩ := z
  rcases r with _ | r
  · simp [d₂_zero]
  · simp [d₂_succ, map_sum, push_single, Category.assoc]

theorem d_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single z c =>
    rw [push_single, d_single, d_single, map_zsmul, map_add, map_zsmul, push_d₁, push_d₂]

theorem push_push {N M K : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M)
    (θ' : SimplexCategory.mk M ⟶ SimplexCategory.mk K) (c : Pr N →₀ ℤ) :
    Pr.push θ' (Pr.push θ c) = Pr.push (θ ≫ θ') c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single z c => simp [push_single, Category.assoc]

theorem bd_bd {N : ℕ} (c : Pr N →₀ ℤ) : Pr.bd (Pr.bd c) = 0 := by
  have h := alt_sum_zero (n := N) (fun θ => Pr.push θ c)
  simp only [Pr.bd, map_sum, map_zsmul, push_push, Finset.smul_sum, smul_smul]
  exact h

theorem d_bd {N : ℕ} (c : Pr N →₀ ℤ) : Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c) := by
  simp only [Pr.bd, map_sum, map_zsmul, d_push]

theorem deg_iff {N : ℕ} (k : ℕ) (c : Pr N →₀ ℤ) :
    Pr.Deg k c ↔ c ∈ supported ℤ ℤ {z : Pr N | z.1 + z.2.1 = k} := by
  simp [Pr.Deg, mem_supported, Set.subset_def]

theorem deg_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (k : ℕ) (c : Pr N →₀ ℤ)
    (hc : Pr.Deg k c) : Pr.Deg k (Pr.push θ c) := by
  classical
  intro z hz
  have hz' := Finsupp.mapDomain_support (f := fun z : Pr N => (⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ : Pr M))
    (s := c) hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz'
  exact hc w hw

theorem deg_d {N : ℕ} (k : ℕ) (c : Pr N →₀ ℤ) (hc : Pr.Deg (k + 1) c) : Pr.Deg k (Pr.d N c) := by
  rw [deg_iff] at hc ⊢
  have key : ∀ z : Pr N, z.1 + z.2.1 = k + 1 →
      z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂ ∈ supported ℤ ℤ {z : Pr N | z.1 + z.2.1 = k} := by
    rintro ⟨p, r, a, b⟩ hz
    simp only at hz
    refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
    · rcases p with _ | p
      · simp [d₁_zero]
      · rw [d₁_succ]
        exact Submodule.sum_mem _ fun i _ => single_mem_supported ℤ _ (by simp; omega)
    · rcases r with _ | r
      · simp [d₂_zero]
      · rw [d₂_succ]
        exact Submodule.sum_mem _ fun j _ => single_mem_supported ℤ _ (by simp; omega)
  rw [Pr.d, linearCombination_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (key z ((mem_supported _ _).1 hc hz))

theorem deg_bd {N : ℕ} (k : ℕ) (c : Pr N →₀ ℤ) (hc : Pr.Deg k c) : Pr.Deg k (Pr.bd c) := by
  have h : ∀ θ : SimplexCategory.mk N ⟶ SimplexCategory.mk (N + 1),
      Pr.push θ c ∈ supported ℤ ℤ {z : Pr (N + 1) | z.1 + z.2.1 = k} :=
    fun θ => (deg_iff k _).1 (deg_push θ k c hc)
  rw [deg_iff, Pr.bd]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h _)

theorem deg_aw (N : ℕ) : Pr.Deg N (Pr.aw N) := by
  rw [deg_iff, Pr.aw]
  exact Submodule.sum_mem _ fun p _ => single_mem_supported ℤ _ (by simp; omega)

theorem deg_wa (N : ℕ) : Pr.Deg N (Pr.wa N) := by
  rw [deg_iff, Pr.wa]
  exact Submodule.sum_mem _ fun p _ => single_mem_supported ℤ _ (by simp; omega)

theorem pr_complex :
    (∀ N (c : Pr N →₀ ℤ), Pr.d N (Pr.d N c) = 0) ∧
    (∀ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) c, Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c)) ∧
    (∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.Deg k (Pr.d N c)) ∧
    (∀ N k (c : Pr N →₀ ℤ), Pr.Deg k c → Pr.Deg k (Pr.bd c)) ∧
    (∀ N (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0) ∧
    (∀ N (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)) ∧
    ∀ N, Pr.Deg N (Pr.aw N) ∧ Pr.Deg N (Pr.wa N) :=
  ⟨fun _ c => d_d c, fun θ c => d_push θ c, fun _ k c h => deg_d k c h, fun _ k c h => deg_bd k c h,
    fun _ c => bd_bd c, fun _ c => d_bd c, fun N => ⟨deg_aw N, deg_wa N⟩⟩

end GlobalTheory.EtC.PrCx
