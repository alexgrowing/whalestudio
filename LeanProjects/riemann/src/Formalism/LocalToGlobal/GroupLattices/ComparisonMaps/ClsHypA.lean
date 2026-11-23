import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

noncomputable section

open Matrix Formalism.UG

namespace Formalism.L2.G.Cmp

variable {T K : Type} [CommRing T] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
  (φ : T ≃+* K × K) (σ : T →+* T) (hσ : ∀ t, φ (σ t) = swapR K (φ t)) (Ov : Subring K) (S : Subring T)
  (hS : ∀ t, t ∈ S ↔ (φ t).1 ∈ Ov ∧ (φ t).2 ∈ Ov) (J : Matrix n n T) (Λ : Submodule S (n → T))
  (hΛ : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, hform σ J z y ∈ S)

include hσ in
theorem hform_fst (z y : n → T) :
    (φ (hform σ J z y)).1 = ∑ i, ∑ j, (φ (z i)).2 * (φ (J i j)).1 * (φ (y j)).1 := by
  simp [hform, map_sum, map_mul, Prod.fst_sum, hσ, swapR]

include hσ in
theorem hform_snd (z y : n → T) :
    (φ (hform σ J z y)).2 = ∑ i, ∑ j, (φ (z i)).1 * (φ (J i j)).2 * (φ (y j)).2 := by
  simp [hform, map_sum, map_mul, Prod.snd_sum, hσ, swapR]

include hσ hS hΛ in

theorem map_of_first (x : GL n T) (hx : x ∈ UJ σ J)
    (h1 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ (((x : Matrix n n T) *ᵥ y) a)).1)
    (h2 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ ((((x⁻¹ : GL n T) : Matrix n n T) *ᵥ y) a)).1)
    (y : n → T) (hy : y ∈ Λ) : (x : Matrix n n T) *ᵥ y ∈ Λ := by
  have key : ∀ (K' : Matrix n n T) (a b : n → T), hform σ K' a b = (fun i => σ (a i)) ᵥ* K' ⬝ᵥ b := by
    intro K' a b
    simp only [hform, Matrix.vecMul, dotProduct, Finset.sum_mul]
    exact Finset.sum_comm
  have hgen : ∀ (M : Matrix n n T) (a b : n → T),
      hform σ J (M *ᵥ a) (M *ᵥ b) = hform σ (cT σ M * J * M) a b := by
    intro M a b
    have hmap : (fun i => σ ((M *ᵥ a) i)) = (M.map σ) *ᵥ (fun i => σ (a i)) := by
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [key, key, hmap, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      Matrix.vecMul_vecMul]
    simp only [Matrix.mul_assoc]
    rfl
  have hU : cT σ (x : Matrix n n T) * J * (x : Matrix n n T) = J := hx
  have hz' : ∀ z : n → T, z = (x : Matrix n n T) *ᵥ (((x⁻¹ : GL n T) : Matrix n n T) *ᵥ z) := by
    intro z
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hΛ]
  intro z hz
  rw [hS]
  have hinv : hform σ J z ((x : Matrix n n T) *ᵥ y) =
      hform σ J (((x⁻¹ : GL n T) : Matrix n n T) *ᵥ z) y := by
    nth_rewrite 1 [hz' z]
    rw [hgen, hU]
  refine ⟨?_, ?_⟩
  · obtain ⟨y', hy'Λ, hy'⟩ := h1 y hy
    have e : (φ (hform σ J z ((x : Matrix n n T) *ᵥ y))).1 = (φ (hform σ J z y')).1 := by
      rw [hform_fst φ σ hσ J, hform_fst φ σ hσ J]
      simp only [hy']
    rw [e]
    exact ((hS _).1 ((hΛ y').1 hy'Λ z hz)).1
  · obtain ⟨z', hz'Λ, hz'e⟩ := h2 z hz
    have e : (φ (hform σ J z ((x : Matrix n n T) *ᵥ y))).2 = (φ (hform σ J z' y)).2 := by
      rw [hinv, hform_snd φ σ hσ J, hform_snd φ σ hσ J]
      simp only [hz'e]
    rw [e]
    exact ((hS _).1 ((hΛ y).1 hy z' hz'Λ)).2

include hσ hS hΛ in

theorem stab_of_first (x : GL n T) (hx : x ∈ UJ σ J)
    (h1 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ (((x : Matrix n n T) *ᵥ y) a)).1)
    (h2 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ ((((x⁻¹ : GL n T) : Matrix n n T) *ᵥ y) a)).1) :
    x ∈ stabGL Λ := by
  show ∀ y : n → T, y ∈ Λ ↔ (x : Matrix n n T) *ᵥ y ∈ Λ
  intro y
  constructor
  · exact map_of_first φ σ hσ Ov S hS J Λ hΛ x hx h1 h2 y
  · intro hxy
    have hxi : x⁻¹ ∈ UJ σ J := inv_mem hx
    have := map_of_first φ σ hσ Ov S hS J Λ hΛ x⁻¹ hxi h2 (by simpa using h1) _ hxy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem int_conj_iff {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n] (Ov : Subring K) (fr g : GL n K) :
    (∀ t : n → K, (∀ a, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ t) a ∈ Ov) →
      ∀ a, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((g : Matrix n n K) *ᵥ t)) a ∈ Ov) ↔
      ∀ a b, ((fr⁻¹ * g * fr : GL n K) : Matrix n n K) a b ∈ Ov := by
  have hmat : ∀ t : n → K, ((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((g : Matrix n n K) *ᵥ t) =
      ((fr⁻¹ * g * fr : GL n K) : Matrix n n K) *ᵥ (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ t) := by
    intro t
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  constructor
  · intro H a b
    have he : ((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((fr : Matrix n n K) *ᵥ Pi.single b 1) =
        Pi.single b 1 := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have h0 : ∀ c, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((fr : Matrix n n K) *ᵥ Pi.single b 1)) c ∈ Ov := by
      intro c
      rw [he]
      by_cases hc : c = b
      · subst hc; simp
      · simp [Pi.single_apply, hc]
    have := H _ h0 a
    rw [hmat, he] at this
    simpa [Matrix.mulVec_single] using this
  · intro H t ht a
    rw [hmat]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun b _ => mul_mem (H a b) (ht b)

end Formalism.L2.G.Cmp
