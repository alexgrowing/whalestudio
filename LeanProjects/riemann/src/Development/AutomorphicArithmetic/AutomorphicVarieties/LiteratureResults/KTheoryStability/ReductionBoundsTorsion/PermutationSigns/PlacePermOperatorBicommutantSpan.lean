import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.MatDefs

noncomputable section

open Matrix

namespace PositivityTheory.KB.BlockInvariants

namespace WeightOneEmbedding

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Ω × Ω) :=
  (Matrix.ofLinearEquiv ℂ).symm ≪≫ₗ (LinearEquiv.curry ℂ ℂ Ω Ω).symm ≪≫ₗ
    (WithLp.linearEquiv 2 ℂ (Ω × Ω → ℂ)).symm

theorem inner_embE (x y : Matrix Ω Ω ℂ) :
    inner ℂ (embE x) (embE y) = trace (xᴴ * y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [embE, LinearEquiv.trans_apply, dotProduct, trace, diag, mul_apply, conjTranspose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem comm_left (A : Submodule ℂ (Matrix Ω Ω ℂ)) (T : Matrix Ω Ω ℂ)
    (hT : ∀ Z : Matrix Ω Ω ℂ, (∀ a ∈ A, Z * a = a * Z) → T * Z = Z * T)
    (S : Matrix Ω Ω ℂ →ₗ[ℂ] Matrix Ω Ω ℂ) (hS : ∀ a ∈ A, ∀ y, S (a * y) = a * S y)
    (y : Matrix Ω Ω ℂ) : S (T * y) = T * S y := by
  have key : ∀ (a : Matrix Ω Ω ℂ) (c j : Ω), a * single c j 1 = ∑ b, a b c • single b j 1 := by
    intro a c j
    ext x z
    simp only [mul_apply, Matrix.sum_apply, Matrix.smul_apply, single, of_apply, smul_eq_mul]
    by_cases h : j = z <;> simp [h, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  let Z : Ω → Ω → Matrix Ω Ω ℂ := fun j k => Matrix.of fun x c => S (single c j 1) x k
  have hZr : ∀ (a : Matrix Ω Ω ℂ) (j k x c : Ω), (Z j k * a) x c = S (a * single c j 1) x k := by
    intro a j k x c
    rw [key, map_sum, Matrix.sum_apply]
    simp only [Z, mul_apply, of_apply, map_smul, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hZl : ∀ (a : Matrix Ω Ω ℂ) (j k x c : Ω), (a * Z j k) x c = (a * S (single c j 1)) x k := by
    intro a j k x c
    simp only [Z, mul_apply, of_apply]
  have hZ : ∀ j k, T * Z j k = Z j k * T := fun j k => hT _ fun a ha => by
    ext x c; rw [hZr, hZl, hS a ha]
  have hsingle : ∀ c j, S (T * single c j 1) = T * S (single c j 1) := by
    intro c j
    ext x k
    rw [← hZr, ← hZl, hZ]
  rw [matrix_eq_sum_single y]
  simp only [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  have : single c j (y c j) = y c j • single c j (1 : ℂ) := by
    rw [smul_single, smul_eq_mul, mul_one]
  rw [this, mul_smul_comm, map_smul, hsingle, map_smul, mul_smul_comm]

theorem bic (A : Submodule ℂ (Matrix Ω Ω ℂ)) (h1 : (1 : Matrix Ω Ω ℂ) ∈ A)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hstar : ∀ a ∈ A, aᴴ ∈ A) (T : Matrix Ω Ω ℂ)
    (hT : ∀ Z : Matrix Ω Ω ℂ, (∀ a ∈ A, Z * a = a * Z) → T * Z = Z * T) : T ∈ A := by
  let K : Submodule ℂ (EuclideanSpace ℂ (Ω × Ω)) := A.map (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).toLinearMap
  let P : Matrix Ω Ω ℂ →ₗ[ℂ] Matrix Ω Ω ℂ :=
    (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ K.starProjection.toLinearMap ∘ₗ
      (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).toLinearMap
  have hPe : ∀ y, embE (P y) = K.starProjection (embE y) := fun y => by
    simp [P]
  have P1 : ∀ y, P y ∈ A := by
    intro y
    obtain ⟨a, ha, e⟩ := Submodule.mem_map.1 (K.starProjection_apply_mem (embE y))
    have : P y = a := by
      apply (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).injective
      rw [hPe]; exact e.symm
    rw [this]; exact ha
  have P2 : ∀ a ∈ A, P a = a := by
    intro a ha
    apply (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).injective
    rw [hPe]
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.mem_map_of_mem ha)
  have P3 : ∀ a ∈ A, ∀ y, P (a * y) = a * P y := by
    intro a ha y
    apply (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).injective
    rw [hPe]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact Submodule.mem_map_of_mem (hmul a ha _ (P1 y))
    · intro w hw
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hw
      have h0 := Submodule.starProjection_inner_eq_zero (K := K) (embE y)
        (embE (aᴴ * b)) (Submodule.mem_map_of_mem (hmul _ (hstar a ha) b hb))
      rw [← hPe, ← map_sub, inner_embE] at h0
      change inner ℂ (embE (a * y) - embE (a * P y)) (embE b) = 0
      rw [← map_sub, inner_embE, ← mul_sub, conjTranspose_mul, Matrix.mul_assoc]
      exact h0
  have := comm_left A T hT P P3 1
  rw [P2 1 h1, Matrix.mul_one] at this
  rw [← this]
  exact P1 T

end WeightOneEmbedding

open WeightOneEmbedding

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

theorem perm'_mul (σ τ : Equiv.Perm (Fin q)) (w v : Fin q → W) :
    (perm' (m := m) σ w) * perm' τ v = if v = w ∘ σ then perm' (σ * τ) w else 0 := by
  ext I K
  rw [mul_apply, Finset.sum_eq_single (I ∘ σ)]
  · simp only [perm', of_apply, Equiv.Perm.coe_mul]
    by_cases hv : v = w ∘ σ
    · subst hv
      rw [if_pos rfl, of_apply]
      by_cases hI : ∀ i, (I i).1 = w i
      · simp [hI, Function.comp_assoc]
      · simp [hI]
    · rw [if_neg hv, Matrix.zero_apply]
      by_cases hI : ∀ i, (I i).1 = w i
      · have : ¬ ∀ i, ((I ∘ σ) i).1 = v i := fun h => hv (funext fun i => by
          rw [← h i]; exact hI (σ i))
        simp only [this, false_and, if_false, mul_zero]
      · simp [hI]
  · intro J _ hJ
    simp only [perm', of_apply]
    rw [if_neg (fun h => hJ h.2), zero_mul]
  · simp

theorem perm'_star (σ : Equiv.Perm (Fin q)) (w : Fin q → W) :
    (perm' (m := m) σ w)ᴴ = perm' σ⁻¹ (w ∘ σ) := by
  ext I J
  simp only [perm', conjTranspose_apply, of_apply]
  have e : (∀ i, (J i).1 = w i) ∧ I = J ∘ σ ↔ (∀ i, (I i).1 = (w ∘ σ) i) ∧ J = I ∘ ⇑(σ⁻¹) := by
    constructor
    · rintro ⟨h1, rfl⟩
      refine ⟨fun i => h1 (σ i), ?_⟩
      funext i; simp
    · rintro ⟨h1, rfl⟩
      refine ⟨fun i => ?_, ?_⟩
      · have := h1 (σ⁻¹ i); simpa using this
      · funext i; simp
  by_cases h : (∀ i, (J i).1 = w i) ∧ I = J ∘ σ
  · rw [if_pos h, if_pos (e.1 h), star_one]
  · rw [if_neg h, if_neg (fun h' => h (e.2 h')), star_zero]

theorem one_eq_sum_perm' : (1 : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) = ∑ w, perm' 1 w := by
  ext I J
  rw [Matrix.sum_apply, Finset.sum_eq_single (fun i => (I i).1)]
  · simp only [perm', of_apply, Equiv.Perm.coe_one, Function.comp_id, one_apply]
    by_cases h : I = J
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro w _ hw
    simp only [perm', of_apply]
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hw (funext fun i => (h i).symm)
  · simp

theorem sw1 : PlacePermOperatorBicommutantSpan := by
  intro W _ _ m q T hT
  set S := Set.range fun p : Equiv.Perm (Fin q) × (Fin q → W) => (perm' (m := m) p.1 p.2)
  have hgen : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span ℂ S := by
    rintro _ ⟨⟨σ, w⟩, rfl⟩ _ ⟨⟨τ, v⟩, rfl⟩
    dsimp only
    rw [perm'_mul]
    split_ifs
    · exact Submodule.subset_span ⟨(σ * τ, w), rfl⟩
    · exact Submodule.zero_mem _
  refine bic (Submodule.span ℂ S) ?_ ?_ ?_ T ?_
  · rw [one_eq_sum_perm']
    exact Submodule.sum_mem _ fun w _ => Submodule.subset_span ⟨(1, w), rfl⟩
  · intro a ha b hb
    have := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at this
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hgen x hx y hy
  · intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨σ, w⟩, rfl⟩ := hx
      dsimp only
      rw [perm'_star]
      exact Submodule.subset_span ⟨(σ⁻¹, w ∘ σ), rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [conjTranspose_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [conjTranspose_smul]; exact Submodule.smul_mem _ _ hx
  · intro Z hZ
    exact hT Z fun σ w => hZ _ (Submodule.subset_span ⟨(σ, w), rfl⟩)

end PositivityTheory.KB.BlockInvariants

end
