import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HolomorphicExtensionCompactRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqZeroOnKCOfEqZeroOnKsetStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestWeightVectorFixedByLowerUnitriangularStatement

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Dec.TauExt

variable {n : ℕ} {ε : Fin n → Bool}

theorem conj_mul (a b : Matrix (Fin n) (Fin n) ℂ) : (a * b).map star = a.map star * b.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem conj_one : (1 : Matrix (Fin n) (Fin n) ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem conj_conj (a : Matrix (Fin n) (Fin n) ℂ) : (a.map star).map star = a := by
  ext i j; simp

theorem conj_Jm : (Jm ε).map star = Jm ε := by
  ext i j
  by_cases h : i = j
  · subst h; by_cases h' : ε i = true <;> simp [Jm, h']
  · simp [Jm, h]

theorem conj_mem {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k.map star ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    have h : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
    have e : star (k.map star) = (star k).map star := by ext i j; simp
    rw [e, ← conj_mul, h, conj_one]
  · have := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hk.2
    simpa only [conj_mul, conj_Jm] using this

theorem mem_KC {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

theorem one_mem_K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem isOpen_units : IsOpen {y : Fin n → Fin n → ℂ | IsUnit (Matrix.of y)} := by
  simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact isOpen_ne_fun (Continuous.matrix_det (A := fun y : Fin n → Fin n → ℂ => Matrix.of y) continuous_id)
    continuous_const

theorem conj_torus (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).map star =
      Matrix.diagonal fun a => Complex.exp (((-θ) a : ℂ) * Complex.I) := by
  rw [Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  rw [Complex.star_def, ← Complex.exp_conj]
  simp

section Mul

variable {B : Type} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] {τ : Matrix (Fin n) (Fin n) ℂ → B}

omit [CompleteSpace B] in
theorem differentiableOn_mul
    (hd : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)})
    {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a) (hb : IsUnit b) :
    DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (a * Matrix.of y * b)) {y | Matrix.of y ∈ KC ε} := by
  have h : Differentiable ℂ fun y : Fin n → Fin n → ℂ => fun i j => (a * Matrix.of y * b) i j := by
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact hd.comp h.differentiableOn fun y hy => (ha.mul hy.1).mul hb

theorem mul_on_KC
    (hd : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)})
    (hm : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, τ (a * b) = τ a * τ b) :
    ∀ a ∈ KC ε, ∀ b ∈ KC ε, τ (a * b) = τ a * τ b := by
  have hd' : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | Matrix.of y ∈ KC ε} :=
    hd.mono fun y hy => hy.1
  have h1 : ∀ a ∈ Kset ε, ∀ b ∈ KC ε, τ (a * b * 1) - τ a * τ b = 0 := fun a ha =>
    GlobalTheory.T.eq_zero_on_KC_of_eq_zero_on_Kset' n ε B (fun y => τ (a * y * 1) - τ a * τ y)
      ((differentiableOn_mul hd (mem_KC ha).1 isUnit_one).sub (hd'.const_mul _))
      fun k hk => by rw [Matrix.mul_one, hm a ha k hk, sub_self]
  intro a ha b hb
  have h2 := GlobalTheory.T.eq_zero_on_KC_of_eq_zero_on_Kset' n ε B (fun y => τ (1 * y * b) - τ y * τ b)
    ((differentiableOn_mul hd isUnit_one hb.1).sub (hd'.mul_const _))
    (fun k hk => by simpa using h1 k hk b hb) a ha
  simpa [sub_eq_zero] using h2

end Mul

theorem adj_on_KC {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}
    (hd : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)})
    (hK : ∀ y ∈ Kset ε, ∀ u v : W, ⟪τ y u, v⟫_ℂ = ⟪u, τ yᴴ v⟫_ℂ) :
    ∀ y ∈ KC ε, ∀ u v : W, ⟪τ y u, v⟫_ℂ = ⟪u, τ yᴴ v⟫_ℂ := by
  intro y hy u v
  have hc : ∀ u v : W, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => ⟪u, τ (Matrix.of y) v⟫_ℂ)
      {y | IsUnit (Matrix.of y)} := fun u v =>
    ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ W v)).differentiable.comp_differentiableOn hd
  have ht : Differentiable ℂ fun y : Fin n → Fin n → ℂ => fun i j => y j i := by fun_prop
  have h1 : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => star ⟪u, τ (Matrix.of y)ᴴ v⟫_ℂ)
      {y | Matrix.of y ∈ KC ε} := by
    intro z hz
    have hz' : IsUnit (Matrix.of fun i j => (star z) j i) := by
      exact hz.1.star
    have h2 := (((hc u v).differentiableAt (isOpen_units.mem_nhds hz')).comp (star z) (ht (star z))).star_star
    rw [star_star] at h2
    exact h2.differentiableWithinAt
  have h3 := GlobalTheory.T.eq_zero_on_KC_of_eq_zero_on_Kset' n ε ℂ (fun y => ⟪v, τ y u⟫_ℂ - star ⟪u, τ yᴴ v⟫_ℂ)
    (((hc v u).mono fun y hy => hy.1).sub h1)
    (fun k hk => by rw [← hK k hk, Complex.star_def, inner_conj_symm, sub_self]) y hy
  rw [← inner_conj_symm, sub_eq_zero.1 h3, Complex.star_def, Complex.conj_conj]

theorem tauExists : TauExists := by
  intro n ε abelian₂ H _ _ σ S w ⟨⟨h1, hmul⟩, hiso, hcont⟩ ⟨hfin, hst, hirr, _, hdom⟩ hw hwt
  classical
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  let π : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S) := fun k =>
    if h : k ∈ Kset ε then ((σ (k.map star)).comp S.subtypeL).codRestrict S
      fun v => hst _ (conj_mem h) _ v.2 else 0
  have hπ : ∀ k ∈ Kset ε, ∀ v : S, (π k v : H) = σ (k.map star) v := fun k hk v => by
    simp only [π, dif_pos hk]; rfl
  have hπ1 : π 1 = 1 := by
    ext v
    rw [hπ 1 one_mem_K, conj_one, h1]; rfl
  have hπm : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, π (a * b) = π a * π b := by
    intro a ha b hb
    ext v
    rw [hπ _ (Kset_mul ε ha hb), conj_mul, hmul _ (conj_mem ha) _ (conj_mem hb), ContinuousLinearMap.mul_apply,
      hπ a ha, hπ b hb]
    rfl
  have hπc : ContinuousOn π (Kset ε) := by
    refine continuousOn_clm_apply.2 fun v => ?_
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr ((hcont v).comp ?_ fun k hk => conj_mem hk) fun k hk => hπ k hk v
    exact (continuous_id.matrix_map continuous_star).continuousOn
  obtain ⟨τ, hd, hτ⟩ := GlobalTheory.T.holomorphic_extension_compact_rep n ε (S →L[ℂ] S) π hπ1 hπm hπc
  have hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v := fun k hk v => by
    rw [hτ k hk, hπ k hk]
  have hτ1 : τ 1 = 1 := by rw [hτ 1 one_mem_K, hπ1]
  have hτm : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, τ (a * b) = τ a * τ b := fun a ha b hb => by
    rw [hτ _ (Kset_mul ε ha hb), hτ a ha, hτ b hb, hπm a ha b hb]
  have hrep : IsCRepOn (KC ε) τ := ⟨hτ1, mul_on_KC hd hτm⟩
  have hwτ : ∀ (μ : Fin n → ℝ) (v : S), IsWtOn (Kset ε) τ (-μ) v ↔ IsWtOn (Kset ε) σ μ (v : H) := by
    intro μ v
    constructor
    · intro h θ hθ
      have hθ' := conj_mem hθ
      rw [conj_torus] at hθ'
      have := congrArg Subtype.val (h (-θ) hθ')
      rw [hτσ _ hθ', conj_torus, neg_neg] at this
      simpa using this
    · intro h θ hθ
      have hθ' := conj_mem hθ
      rw [conj_torus] at hθ'
      apply Subtype.ext
      rw [hτσ _ hθ, conj_torus, h (-θ) hθ']
      simp
  refine ⟨τ, ⟨hfin, hrep, fun u v => ?_, adj_on_KC hd fun k hk u v => ?_, fun S' hS' => ?_, hw,
    (hwτ abelian₂ w).2 hwt, ?_⟩, hτσ⟩
  · exact ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ S v)).differentiable.comp_differentiableOn
      (hd.mono fun y hy => hy.1)
  · have hk' : kᴴ ∈ Kset ε := Kset_star ε hk
    have hi : ∀ x : S, ‖τ k x‖ = ‖x‖ := fun x => by
      rw [Submodule.coe_norm, hτσ k hk, hiso _ (conj_mem hk), Submodule.coe_norm]
    have e : τ k (τ kᴴ v) = v := by
      have : k * kᴴ = 1 := Unitary.mul_star_self_of_mem hk.1
      rw [← ContinuousLinearMap.mul_apply, ← hτm k hk _ hk', this, hτ1]; rfl
    conv_lhs => rw [← e]
    exact LinearIsometry.inner_map_map ⟨(τ k).toLinearMap, hi⟩ u _
  · have hs : IsKStableOn ε σ (S'.map S.subtype) := by
      rintro g hg _ ⟨v, hv, rfl⟩
      refine ⟨τ (g.map star) v, hS' _ (conj_mem hg) v hv, ?_⟩
      have := hτσ _ (conj_mem hg) v
      rwa [conj_conj] at this
    rcases hirr _ (S.map_subtype_le S') hs with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_subtype_top])
  · refine GlobalTheory.T.lowest_weight_vector_fixed_by_lower_unitriangular n ε abelian₂ S τ w hrep (hd.differentiableAt (isOpen_units.mem_nhds ?_))
      ((hwτ abelian₂ w).2 hwt) fun μ v hv h => hdom μ v v.2 (fun e => hv (Subtype.ext e)) ((hwτ μ v).1 h)
    exact (isUnit_one : IsUnit (1 : Matrix (Fin n) (Fin n) ℂ))

end GlobalTheory.Dec.TauExt
