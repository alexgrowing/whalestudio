import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate

namespace GlobalTheory.WittTrace

open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt

section Abstract

variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]

theorem exists_dual_ne_zero (H : Submodule E V) {x y : V} (hx : x ∉ H) (hy : y ∉ H) :
    ∃ ψ : V →ₗ[E] E, (∀ h ∈ H, ψ h = 0) ∧ ψ x ≠ 0 ∧ ψ y ≠ 0 := by
  have kill : ∀ f : Module.Dual E V, H.map f = ⊥ → ∀ h ∈ H, f h = 0 := by
    intro f hf h hh
    have hm : f h ∈ H.map f := Submodule.mem_map_of_mem hh
    rw [hf] at hm
    exact (Submodule.mem_bot E).1 hm
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  obtain ⟨g, hgy, hg⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hy inferInstance
  have hf0 := kill f hf
  have hg0 := kill g hg
  by_cases hfy : f y = 0
  · by_cases hgx : g x = 0
    · refine ⟨f + g, fun h hh => ?_, ?_, ?_⟩
      · simp [hf0 h hh, hg0 h hh]
      · simpa [hgx] using hfx
      · simpa [hfy] using hgy
    · exact ⟨g, hg0, hgx, hgy⟩
  · exact ⟨f, hf0, hfx, hfy⟩

theorem exists_isometry_step (hs : ∀ b : E, c b = b → ∃ s : E, s ≠ 0 ∧ s + c s = b)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hrep : ∀ ψ : V →ₗ[E] E, ∃ w, ∀ z, B z w = ψ z) (S : Set V) {x y : V}
    (hx : x ∉ Submodule.span E S) (hy : y ∉ Submodule.span E S) (hxy : B x x = B y y)
    (hS : ∀ h ∈ S, B h x = B h y) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ γ x = y ∧ ∀ h ∈ S, γ h = h := by
  have hSxy : ∀ h ∈ S, B h (x - y) = 0 := fun h hh => by rw [map_sub, hS h hh, sub_self]
  by_cases hne : B x (x - y) = 0
  swap
  · obtain ⟨γ, hγ, hγx, hγu⟩ := exists_isometry_of_apply_sub_ne_zero hB hxy hne
    exact ⟨γ, hγ, hγx, fun h hh => hγu h (hSxy h hh)⟩
  obtain ⟨ψ, hψH, hψx, hψy⟩ := exists_dual_ne_zero (Submodule.span E S) hx hy
  obtain ⟨v, hv⟩ := hrep ψ
  obtain ⟨a, ha, hav⟩ := hs (B v v) (hB v v)
  have hca : c a ≠ 0 := (map_ne_zero c).2 ha
  have hvS : ∀ h ∈ S, B h v = 0 := fun h hh => by
    rw [hv]; exact hψH h (Submodule.subset_span hh)
  obtain ⟨σ, hσq⟩ : ∃ σ : V ≃ₗ[E] V, ∀ z, σ z = quasiRefl B v a z :=
    ⟨LinearEquiv.ofLinear (quasiRefl B v a) (quasiRefl B v (c a))
      (LinearMap.ext fun z => quasiRefl_quasiRefl B hca ha (by rw [add_comm]; exact hav) z)
      (LinearMap.ext fun z => quasiRefl_quasiRefl B ha hca hav z), fun _ => rfl⟩
  have hσ : ∀ z w, B (σ z) (σ w) = B z w := fun z w => by
    rw [hσq, hσq]; exact apply_quasiRefl_quasiRefl hB ha hav z w
  have hσS : ∀ h ∈ S, σ h = h := fun h hh => by
    rw [hσq, quasiRefl_apply, hvS h hh, mul_zero, zero_smul, sub_zero]
  have hσx : σ x = x - (a⁻¹ * B x v) • v := by rw [hσq, quasiRefl_apply]
  have key : B (σ x) (σ x - y) = a⁻¹ * B x v * B v y := by
    have h0 : B x x - B x y = 0 := by rw [← map_sub]; exact hne
    rw [map_sub, hσ x x, hσx]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination h0
  have hkey : B (σ x) (σ x - y) ≠ 0 := by
    rw [key]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero ha) (by rw [hv]; exact hψx)) ?_
    rw [← hB y v, hv]
    exact (map_ne_zero c).2 hψy
  obtain ⟨γ, hγ, hγx, hγu⟩ :=
    exists_isometry_of_apply_sub_ne_zero hB (by rw [hσ]; exact hxy) hkey
  refine ⟨σ.trans γ, fun z w => by simp only [LinearEquiv.trans_apply, hγ, hσ], ?_, ?_⟩
  · simp only [LinearEquiv.trans_apply]; exact hγx
  · intro h hh
    simp only [LinearEquiv.trans_apply, hσS h hh]
    refine hγu h ?_
    have e := hσ h x
    rw [hσS h hh] at e
    rw [map_sub, e, hS h hh, sub_self]

theorem exists_isometry_of_linearIndependent
    (hs : ∀ b : E, c b = b → ∃ s : E, s ≠ 0 ∧ s + c s = b)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hrep : ∀ ψ : V →ₗ[E] E, ∃ w, ∀ z, B z w = ψ z) {ι : Type*} [Finite ι] {x y : ι → V}
    (hx : LinearIndependent E x) (hy : LinearIndependent E y)
    (hxy : ∀ i j, B (x i) (x j) = B (y i) (y j)) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ i, γ (x i) = y i := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧
      ∀ i ∈ s, γ (x i) = y i by
    obtain ⟨γ, hγ, hγs⟩ := H Finset.univ
    exact ⟨γ, hγ, fun i => hγs i (Finset.mem_univ i)⟩
  intro s
  refine Finset.induction_on s ⟨LinearEquiv.refl E V, fun _ _ => rfl, by simp⟩ ?_
  intro j s hj ih
  obtain ⟨γ, hγ, hγs⟩ := ih
  have hjs : j ∉ (s : Set ι) := by simpa using hj
  have hyj : y j ∉ Submodule.span E (y '' ↑s) := hy.notMem_span_image hjs
  have himg : y '' ↑s = γ '' (x '' ↑s) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨x i, ⟨i, hi, rfl⟩, hγs i hi⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩; exact ⟨i, hi, (hγs i hi).symm⟩
  have hxj : γ (x j) ∉ Submodule.span E (y '' ↑s) := by
    rw [himg]
    intro hm
    exact hx.notMem_span_image hjs
      ((Submodule.apply_mem_span_image_iff_mem_span (f := (γ : V →ₗ[E] V)) γ.injective).1 hm)
  obtain ⟨γ₁, hγ₁, hγ₁x, hγ₁S⟩ := exists_isometry_step hs hc hB hrep (y '' ↑s) hxj hyj
    (by rw [hγ]; exact hxy j j) (by
      rintro _ ⟨i, hi, rfl⟩
      calc B (y i) (γ (x j)) = B (γ (x i)) (γ (x j)) := by rw [hγs i hi]
        _ = B (x i) (x j) := hγ _ _
        _ = B (y i) (y j) := hxy i j)
  refine ⟨γ.trans γ₁, fun z w => by simp only [LinearEquiv.trans_apply, hγ₁, hγ], ?_⟩
  intro i hi
  rcases Finset.mem_insert.1 hi with rfl | hi
  · simp only [LinearEquiv.trans_apply]; exact hγ₁x
  · simp only [LinearEquiv.trans_apply, hγs i hi]
    exact hγ₁S _ ⟨i, hi, rfl⟩

end Abstract

theorem linearIndependent_col_of_rank {K : Type*} [Field K] {n a : ℕ}
    {X : Matrix (Fin n) (Fin a) K} (h : X.rank = a) : LinearIndependent K X.col := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  rw [Matrix.rank_eq_finrank_span_cols] at h
  exact h.symm

private lemma exists_form_lemma {K : Type} [Field K] [StarRing K] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) K) :
    ∃ B : (Fin n → K) →ₗ[K] (Fin n → K) →ₛₗ[starRingEnd K] K,
      ∀ z w, B z w = star w ⬝ᵥ J *ᵥ z :=
  ⟨LinearMap.mk₂'ₛₗ (RingHom.id K) (starRingEnd K) (fun z w => star w ⬝ᵥ J *ᵥ z)
    (fun _ _ _ => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun _ _ _ => by simp [Matrix.mulVec_smul, dotProduct_smul])
    (fun _ _ _ => by simp [star_add, add_dotProduct])
    (fun _ _ _ => by simp [star_smul, smul_dotProduct, starRingEnd_apply]), fun _ _ => rfl⟩

private lemma entry_lemma_2 {K : Type} [Field K] [StarRing K] {n : ℕ} {m m' : Type*} [Fintype m]
    [Fintype m'] (J : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin n) m K) (Q : Matrix (Fin n) m' K)
    (i : m) (j : m') : (Pᴴ * J * Q) i j = star (P.col i) ⬝ᵥ J *ᵥ Q.col j := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]

private lemma transpose_mul_transpose_mul_map_star_eq {K : Type} [Field K] [StarRing K] {n : ℕ} {m : Type*}
    [Fintype m] (J : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin n) m K) :
    Pᵀ * Jᵀ * P.map star = (Pᴴ * J * P)ᵀ := by
  rw [transpose_mul, transpose_mul, conjTranspose_transpose, Matrix.mul_assoc]

private lemma eq_zero_of_mulVec_eq_zero_of_linearIndependent_col {K : Type} [Field K] {n a : ℕ} {X : Matrix (Fin n) (Fin a) K}
    (hX : LinearIndependent K X.col) (v : Fin a → K) (h : X *ᵥ v = 0) : v = 0 := by
  have e : X *ᵥ v = ∑ j, v j • X.col j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.col, Finset.sum_apply, mul_comm]
  rw [e] at h
  funext j
  exact Fintype.linearIndependent_iff.1 hX v h j

theorem exists_isometry_mul_eq (K : Type) [Field K] [StarRing K] (θ : K) (hθ : θ + star θ = 1)
    (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K) (hJ : Jᴴ = J)
    (hdet : IsUnit J.det) (hX : X.rank = a) (hY : Y.rank = a)
    (hXY : Xᴴ * J * X = Yᴴ * J * Y) :
    ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y := by
  have hXl := linearIndependent_col_of_rank hX
  have hYl := linearIndependent_col_of_rank hY
  by_cases h2 : (2 : K) = 0
  · obtain ⟨B, hBd⟩ := exists_form_lemma J
    have hc : ∀ t : K, starRingEnd K (starRingEnd K t) = t := fun t => by simp
    have hB : ∀ x y, starRingEnd K (B x y) = B y x := by
      intro x y
      rw [hBd, hBd, starRingEnd_apply, ← star_dotProduct_star, star_star, star_mulVec,
        ← dotProduct_mulVec, hJ]
    have hrep : ∀ ψ : (Fin n → K) →ₗ[K] K, ∃ w, ∀ z, B z w = ψ z := by
      intro ψ
      obtain ⟨r, hr⟩ : ∃ r : Fin n → K, ∀ z, ψ z = r ⬝ᵥ z :=
        ⟨fun k => ψ (fun j => if k = j then 1 else 0), fun z => by
          rw [LinearMap.pi_apply_eq_sum_univ ψ z]; simp [dotProduct, mul_comm]⟩
      refine ⟨star ((Jᵀ)⁻¹ *ᵥ r), fun z => ?_⟩
      have hdT : IsUnit Jᵀ.det := by rwa [det_transpose]
      rw [hBd, hr, star_star, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
        mul_nonsing_inv _ hdT, one_mulVec]
    have hs : ∀ b : K, starRingEnd K b = b → ∃ s : K, s ≠ 0 ∧ s + starRingEnd K s = b := by
      intro b hb
      by_cases hb0 : b = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        rw [map_one, hb0, one_add_one_eq_two, h2]
      · have hθ0 : θ ≠ 0 := by
          rintro rfl
          simp at hθ
        refine ⟨θ * b, mul_ne_zero hθ0 hb0, ?_⟩
        rw [map_mul, hb, starRingEnd_apply]
        linear_combination b * hθ
    have hxy : ∀ i j, B (X.col i) (X.col j) = B (Y.col i) (Y.col j) := by
      intro i j
      rw [hBd, hBd, ← entry_lemma_2, ← entry_lemma_2, hXY]
    obtain ⟨γ, hγ, hγX⟩ := exists_isometry_of_linearIndependent hs hc hB hrep hXl hYl hxy
    refine ⟨LinearMap.toMatrix' (γ : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩
    · set g := LinearMap.toMatrix' (γ : (Fin n → K) →ₗ[K] (Fin n → K))
      have hcol : ∀ j, g.col j = γ (Pi.single j 1) := fun j => by
        rw [← mulVec_single_one, LinearMap.toMatrix'_mulVec]; rfl
      ext i j
      rw [entry_lemma_2, hcol, hcol, ← hBd, hγ, hBd]
      simp
    · ext i j
      have e : (LinearMap.toMatrix' (γ : (Fin n → K) →ₗ[K] (Fin n → K)) * X).col j =
          LinearMap.toMatrix' (γ : (Fin n → K) →ₗ[K] (Fin n → K)) *ᵥ X.col j := by
        ext k
        simp [Matrix.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [LinearMap.toMatrix'_mulVec] at e
      have := congrFun e i
      simp only [LinearEquiv.coe_coe, hγX] at this
      exact this
  · have hc : ∀ t : K, starRingEnd K (starRingEnd K t) = t := fun t => by simp
    have hG : ∀ a b, starRingEnd K (Jᵀ a b) = Jᵀ b a := by
      intro a b
      rw [transpose_apply, transpose_apply, starRingEnd_apply, ← conjTranspose_apply, hJ]
    have hdT : Jᵀ.det ≠ 0 := by rw [det_transpose]; exact hdet.ne_zero
    have h0 : ∀ v, X *ᵥ v = 0 ↔ Y *ᵥ v = 0 := by
      intro v
      constructor
      · intro h; rw [eq_zero_of_mulVec_eq_zero_of_linearIndependent_col hXl v h, mulVec_zero]
      · intro h; rw [eq_zero_of_mulVec_eq_zero_of_linearIndependent_col hYl v h, mulVec_zero]
    have hXY' : Yᵀ * Jᵀ * Y.map (starRingEnd K) = Xᵀ * Jᵀ * X.map (starRingEnd K) := by
      have e := transpose_mul_transpose_mul_map_star_eq J X
      have e' := transpose_mul_transpose_mul_map_star_eq J Y
      change Yᵀ * Jᵀ * Y.map star = Xᵀ * Jᵀ * X.map star
      rw [e, e', hXY]
    obtain ⟨γ, hγ, hγX⟩ := exists_gl_isometry_mul_eq h2 hc hG hdT h0 hXY'
    refine ⟨γ, ?_, hγX⟩
    have e := transpose_mul_transpose_mul_map_star_eq J (γ : Matrix (Fin n) (Fin n) K)
    change (γ : Matrix (Fin n) (Fin n) K)ᵀ * Jᵀ * (γ : Matrix (Fin n) (Fin n) K).map star = Jᵀ at hγ
    rw [hγ] at e
    exact (transpose_inj.1 e).symm

end GlobalTheory.WittTrace
