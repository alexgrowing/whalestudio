import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieAlgebraVectorDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformBoundedRightInverse
open scoped Matrix

namespace GlobalTheory.UniformLieDecomp

theorem abstract {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T : Type} [TopologicalSpace T] (S : Set T) (hS : IsCompact S) (g p k : Submodule ℝ E)
    (φ : T → E →ₗ[ℝ] E) (hφ : ∀ y, ContinuousOn (fun t => φ t y) S)
    (hp : ∀ t ∈ S, ∀ y ∈ p, φ t y ∈ g) (hk : k ≤ g)
    (hs : ∀ t ∈ S, ∀ x ∈ g, ∃ y ∈ p, ∃ z ∈ k, x = φ t y + z) (X : E) (hX : X ∈ g) :
    ∃ (e e' : ℕ) (Yb : Fin e → E) (Zb : Fin e' → E) (C : ℝ), (∀ j, Yb j ∈ p) ∧ (∀ j, Zb j ∈ k) ∧
      ∀ t ∈ S, ∃ (c : Fin e → ℝ) (c' : Fin e' → ℝ), (∀ j, |c j| ≤ C) ∧ (∀ j, |c' j| ≤ C) ∧
        X = ∑ j, c j • φ t (Yb j) + ∑ j, c' j • Zb j := by
  obtain ⟨π, hπ⟩ := g.subtype.exists_leftInverse_of_injective g.ker_subtype
  have hπ' : ∀ x ∈ g, ((π x : g) : E) = x := fun x hx => by
    have := LinearMap.congr_fun hπ ⟨x, hx⟩
    simpa using congrArg Subtype.val this
  let bp := Module.finBasis ℝ p
  let bk := Module.finBasis ℝ k
  let P : (Fin (Module.finrank ℝ p) → ℝ) →ₗ[ℝ] E := p.subtype ∘ₗ bp.equivFun.symm.toLinearMap
  let K : (Fin (Module.finrank ℝ k) → ℝ) →ₗ[ℝ] E := k.subtype ∘ₗ bk.equivFun.symm.toLinearMap
  let L : T → ((Fin (Module.finrank ℝ p) → ℝ) × (Fin (Module.finrank ℝ k) → ℝ)) →ₗ[ℝ] g :=
    fun t => π ∘ₗ (LinearMap.coprod (φ t ∘ₗ P) K)
  have hL : ∀ t v, L t v = π (φ t (P v.1) + K v.2) := fun t v => rfl
  obtain ⟨C, hC⟩ := GlobalTheory.exists_uniform_preimage_bound_of_isCompact T _ g S hS L
    (fun v => by
      simp only [hL]
      exact π.continuous_of_finiteDimensional.comp_continuousOn ((hφ _).add continuousOn_const))
    (fun t ht x => by
      obtain ⟨y, hy, z, hz, h⟩ := hs t ht x x.2
      refine ⟨(bp.equivFun ⟨y, hy⟩, bk.equivFun ⟨z, hz⟩), Subtype.ext ?_⟩
      have h1 : P (bp.equivFun ⟨y, hy⟩) = y := by
        simp only [P, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        rfl
      have h2 : K (bk.equivFun ⟨z, hz⟩) = z := by
        simp only [K, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        rfl
      rw [hL]
      dsimp only
      rw [h1, h2, ← h, hπ' _ x.2])
  refine ⟨_, _, fun j => bp j, fun j => bk j, C * ‖(⟨X, hX⟩ : g)‖, fun j => (bp j).2,
    fun j => (bk j).2, fun t ht => ?_⟩
  obtain ⟨v, h1, h2⟩ := hC t ht ⟨X, hX⟩
  refine ⟨v.1, v.2, fun j => ?_, fun j => ?_, ?_⟩
  · exact ((norm_le_pi_norm v.1 j).trans (norm_fst_le v)).trans h2
  · exact ((norm_le_pi_norm v.2 j).trans (norm_snd_le v)).trans h2
  · have h3 := congrArg Subtype.val h1
    have hP : P v.1 ∈ p := (bp.equivFun.symm v.1).2
    have hK : K v.2 ∈ k := (bk.equivFun.symm v.2).2
    rw [hL, hπ' _ (g.add_mem (hp t ht _ hP) (hk hK))] at h3
    refine Eq.trans h3.symm ?_
    simp [P, K, map_sum]

variable {n : ℕ}

theorem conj_mem (A B R X : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnit R.det) (hB : Rᴴ * A * R = B)
    (hX : Xᴴ * A + A * X = 0) : (R⁻¹ * X * R)ᴴ * B + B * (R⁻¹ * X * R) = 0 := by
  have h1 : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have h2 : R⁻¹ᴴ * Rᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc _ = Rᴴ * Xᴴ * (R⁻¹ᴴ * Rᴴ) * A * R + Rᴴ * A * (R * R⁻¹) * X * R := by
        rw [← hB]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Rᴴ * (Xᴴ * A + A * X) * R := by
        rw [h1, h2]; simp only [Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX]; simp

theorem inv_form (A B R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnit R.det) (hB : Rᴴ * A * R = B) :
    R⁻¹ᴴ * B * R⁻¹ = A := by
  have h1 : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have h2 : R⁻¹ᴴ * Rᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc _ = (R⁻¹ᴴ * Rᴴ) * A * (R * R⁻¹) := by rw [← hB]; simp only [Matrix.mul_assoc]
    _ = A := by rw [h1, h2]; simp

theorem iso_vec (A B R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnit R.det) (hB : Rᴴ * A * R = B)
    (v : Fin n → ℂ) (hv : star v ⬝ᵥ A *ᵥ v = 0) : star (R⁻¹ *ᵥ v) ⬝ᵥ B *ᵥ (R⁻¹ *ᵥ v) = 0 := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    inv_form A B R hR hB, hv]

theorem decomp : ∀ (n : ℕ) (A R : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool), Aᴴ = A →
    Rᴴ * A * R = Matrix.diagonal (fun i => if ε i then (1 : ℂ) else -1) →
    ∀ v : Fin n → ℂ, star v ⬝ᵥ A *ᵥ v = 0 →
    ∀ (T : Type) [TopologicalSpace T] (S : Set T), IsCompact S →
    ∀ m : T → Matrix (Fin n) (Fin n) ℂ, ContinuousOn m S → (∀ t ∈ S, (m t)ᴴ * A * m t = A) →
    ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * A + A * X = 0 →
      ∃ (e e' : ℕ) (Yb : Fin e → Matrix (Fin n) (Fin n) ℂ) (l : Fin e → ℂ) (Zb : Fin e' → Matrix (Fin n) (Fin n) ℂ) (C : ℝ),
        (∀ j, (Yb j)ᴴ * A + A * Yb j = 0 ∧ Yb j *ᵥ v = l j • v) ∧
        (∀ j, (Zb j)ᴴ * A + A * Zb j = 0 ∧ (R⁻¹ * Zb j * R)ᴴ = -(R⁻¹ * Zb j * R)) ∧
        ∀ t ∈ S, ∃ (c : Fin e → ℝ) (c' : Fin e' → ℝ), (∀ j, |c j| ≤ C) ∧ (∀ j, |c' j| ≤ C) ∧
          X = ∑ j, c j • ((m t)⁻¹ * Yb j * m t) + ∑ j, c' j • Zb j := by
  intro n A R ε _ hR v hv T _ S hS m hm hmA X hX
  have hD : (Rᴴ * A * R).det ≠ 0 := by
    rw [hR, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by by_cases h : ε i <;> simp [h]
  rw [Matrix.det_mul, Matrix.det_mul] at hD
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hD)
  have hA0 : A.det ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hD)
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA0
  have hmu : ∀ t ∈ S, IsUnit (m t).det := fun t ht => by
    have h := congrArg Matrix.det (hmA t ht)
    rw [Matrix.det_mul] at h
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul (h ▸ hA0))
  have hminv : ∀ t ∈ S, (m t)⁻¹ = A⁻¹ * (m t)ᴴ * A := fun t ht => by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ A, hmA t ht,
      Matrix.nonsing_inv_mul A hAu]
  let g : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {Z | Zᴴ * A + A * Z = 0}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add] at *
        rw [add_add_add_comm, ha, hb, add_zero]
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
          star_trivial] at *
        rw [← smul_add, ha, smul_zero] }
  let p : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := g ⊓
    { carrier := {Y | ∃ c : ℂ, Y *ᵥ v = c • v}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := fun {a b} ⟨c, hc⟩ ⟨d, hd⟩ => ⟨c + d, by rw [Matrix.add_mulVec, hc, hd, add_smul]⟩
      smul_mem' := fun r a ⟨c, hc⟩ => ⟨r • c, by rw [Matrix.smul_mulVec, hc, smul_assoc]⟩ }
  let k : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := g ⊓
    { carrier := {Z | (R⁻¹ * Z * R)ᴴ = -(R⁻¹ * Z * R)}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_add, ha, hb, neg_add]
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_smul, ha, star_trivial,
          smul_neg] }
  let φ : T → Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := fun t =>
    { toFun := fun Y => (m t)⁻¹ * Y * m t
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hφ : ∀ y, ContinuousOn (fun t => φ t y) S := fun y => by
    have : ContinuousOn (fun t => A⁻¹ * (m t)ᴴ * A * y * m t) S :=
      (((continuousOn_const.mul (continuous_id.matrix_conjTranspose.comp_continuousOn hm)).mul
        continuousOn_const).mul continuousOn_const).mul hm
    refine this.congr fun t ht => ?_
    show (m t)⁻¹ * y * m t = _
    rw [hminv t ht]
  have hp : ∀ t ∈ S, ∀ y ∈ p, φ t y ∈ g := fun t ht y hy =>
    conj_mem A A (m t) y (hmu t ht) (hmA t ht) hy.1
  have hs : ∀ t ∈ S, ∀ x ∈ g, ∃ y ∈ p, ∃ z ∈ k, x = φ t y + z := by
    intro t ht x hx
    obtain ⟨Z, c, h1, h2, h3⟩ := GlobalTheory.LieIwasawa.decomp n ε _ rfl _
      (iso_vec A _ R hRu hR _ (iso_vec A A (m t) (hmu t ht) (hmA t ht) v hv)) _
      (conj_mem A _ R x hRu hR hx)
    have r1 : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
    have r2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
    have m1 : m t * (m t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hmu t ht)
    have m2 : (m t)⁻¹ * m t = 1 := Matrix.nonsing_inv_mul _ (hmu t ht)
    have hZ : R * Z * R⁻¹ ∈ g := by
      have := conj_mem _ A R⁻¹ Z (Matrix.isUnit_nonsing_inv_det R hRu) (inv_form A _ R hRu hR) h2
      rwa [Matrix.nonsing_inv_nonsing_inv R hRu] at this
    have hZZ : R⁻¹ * (R * Z * R⁻¹) * R = Z := by
      calc _ = (R⁻¹ * R) * Z * (R⁻¹ * R) := by simp only [Matrix.mul_assoc]
        _ = Z := by rw [r2]; simp
    refine ⟨m t * (x - R * Z * R⁻¹) * (m t)⁻¹, ⟨?_, c, ?_⟩, R * Z * R⁻¹, ⟨hZ, ?_⟩, ?_⟩
    · have := conj_mem A A (m t)⁻¹ _ (Matrix.isUnit_nonsing_inv_det _ (hmu t ht))
        (inv_form A A (m t) (hmu t ht) (hmA t ht)) (g.sub_mem hx hZ)
      rwa [Matrix.nonsing_inv_nonsing_inv _ (hmu t ht)] at this
    · have h4 := congrArg (fun w => (m t * R) *ᵥ w) h3
      simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec] at h4
      have e1 : m t * R * (R⁻¹ * (m t)⁻¹) = 1 := by
        calc _ = m t * (R * R⁻¹) * (m t)⁻¹ := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [r1, Matrix.mul_one, m1]
      have e2 : m t * R * ((R⁻¹ * x * R - Z) * (R⁻¹ * (m t)⁻¹)) =
          m t * (x - R * Z * R⁻¹) * (m t)⁻¹ := by
        calc _ = m t * ((R * R⁻¹) * x * (R * R⁻¹) - R * Z * R⁻¹) * (m t)⁻¹ := by
              simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
          _ = _ := by rw [r1]; simp
      rw [e1, e2, Matrix.one_mulVec] at h4
      exact h4
    · show (R⁻¹ * (R * Z * R⁻¹) * R)ᴴ = -(R⁻¹ * (R * Z * R⁻¹) * R)
      rw [hZZ, h1]
    · show x = (m t)⁻¹ * (m t * (x - R * Z * R⁻¹) * (m t)⁻¹) * m t + R * Z * R⁻¹
      calc x = ((m t)⁻¹ * m t) * (x - R * Z * R⁻¹) * ((m t)⁻¹ * m t) + R * Z * R⁻¹ := by
            rw [m2]; simp
        _ = _ := by simp only [Matrix.mul_assoc]
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  obtain ⟨e, e', Yb, Zb, C, hY, hZ, h⟩ :=
    abstract S hS g p k φ hφ hp inf_le_left hs X hX
  choose l hl using fun j => (hY j).2
  exact ⟨e, e', Yb, l, Zb, C, fun j => ⟨(hY j).1, hl j⟩, fun j => ⟨(hZ j).1, (hZ j).2⟩, h⟩

end GlobalTheory.UniformLieDecomp
