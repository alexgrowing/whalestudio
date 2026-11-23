import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary

open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.HighestWeightMap

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_line {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

end

theorem raising_eq_zero {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} (E : Fin k → Fin k → Module.End ℂ W) (Δ : W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z →
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) Δ) (∑ a, ∑ b, Z a b • E a b Δ) 0)
    (hd : DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) Δ)
      (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j))
    {a b : Fin k} (hab : ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) : E a b Δ = 0 := by
  obtain ⟨D, hD⟩ := hd
  let Φ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W :=
    { toFun := fun Z => ∑ a, ∑ b, Z a b • E a b Δ
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, mul_smul] }
  let Ψ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W :=
    { toFun := fun Z => D fun i j => Z i j
      map_add' := fun x y => D.map_add x y
      map_smul' := fun c x => D.map_smul c x }
  have hskew : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → Φ Z = Ψ Z := by
    intro Z hZ
    have h1 : HasDerivAt (fun t : ℝ => fun i j => NormedSpace.exp ((t : ℂ) • Z) i j) (fun i j => Z i j) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_exp_line Z i j
    have h2 := (hD.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 h1 (by simp)
    exact (hE Z hZ).unique h2
  have hall : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Φ Z = Ψ Z := by
    intro Z
    have e : Z = (1 / 2 : ℂ) • (Z - Zᴴ) + (-Complex.I / 2) • (Complex.I • (Z + Zᴴ)) := by
      have : -Complex.I / 2 * Complex.I = 1 / 2 := by
        linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      rw [smul_smul, this]
      module
    have s1 := hskew (Z - Zᴴ) (by simp)
    have s2 := hskew (Complex.I • (Z + Zᴴ)) (by simp [conjTranspose_smul, add_comm])
    rw [e, map_add, map_add, map_smul, map_smul (Ψ), s1, map_smul Φ (-Complex.I / 2), map_smul Ψ (-Complex.I / 2), s2]
  have h3 : Φ (Matrix.single a b 1) = E a b Δ := by
    show ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • E c d Δ = _
    simp [Matrix.single_apply, ite_and, ite_smul]
  have h4 : HasDerivAt (fun s : ℂ => fun i j => (1 + Matrix.single a b s : Matrix (Fin k) (Fin k) ℂ) i j)
      (fun i j => Matrix.single a b (1 : ℂ) i j) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [Matrix.add_apply, Matrix.single_apply]
    split_ifs
    · exact (hasDerivAt_id' _).const_add _
    · exact hasDerivAt_const _ _
  have h5 : HasDerivAt (fun s : ℂ => π (1 + Matrix.single a b s) Δ) (Ψ (Matrix.single a b 1)) 0 :=
    hD.comp_hasDerivAt_of_eq 0 h4 (by
      funext i j
      show _ = (1 : Matrix (Fin k) (Fin k) ℂ) i j + Matrix.single a b (0 : ℂ) i j
      simp)
  simp only [hab] at h5
  rw [← h3, hall, h5.unique (hasDerivAt_const _ _)]

open Formalism.REAL in

theorem exists_lie_map {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [NormedAddCommGroup V₂]
    [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] {n : ℕ}
    (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ)
    (v₁ : V₁) (v₂ : V₂) (hE₁ : GlRel E₁) (hE₂ : GlRel E₂)
    (hU : ∀ a b x y, ⟪E₂ a b x, y⟫_ℂ = ⟪x, E₂ b a y⟫_ℂ)
    (h₁ : ∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hw₁ : IsHW E₁ ν v₁) (hw₂ : IsHW E₂ ν v₂) (hv₁ : v₁ ≠ 0) :
    ∃ L : V₁ →ₗ[ℂ] V₂, (∀ a b x, L (E₁ a b x) = E₂ a b (L x)) ∧ L v₁ = v₂ := by
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  let K : Submodule ℂ V₂ := S.comap (LinearMap.inr ℂ V₁ V₂)
  have hK : ∀ a b, ∀ x ∈ K, E₂ a b x ∈ K := fun a b x hx => by
    have := hS a b _ hx
    simpa [hEap, K] using this
  have hK' : ∀ a b, ∀ x ∈ Kᗮ, E₂ a b x ∈ Kᗮ := fun a b x hx =>
    (Submodule.mem_orthogonal _ _).2 fun u hu => by
      rw [← hU]
      exact (Submodule.mem_orthogonal _ _).1 hx _ (hK _ _ _ hu)
  have hv₂ : v₂ ∈ Kᗮ := by
    obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal v₂
    have hyw : ∀ a, E₂ a a y = ν a • y := fun a => by
      have e := hw₂.1 a
      rw [hyz, map_add, smul_add] at e
      have e' : E₂ a a y - ν a • y = -(E₂ a a z - ν a • z) := by
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, e, add_comm]
      rw [← sub_eq_zero]
      refine Submodule.disjoint_def.1 K.orthogonal_disjoint _ (K.sub_mem (hK _ _ _ hy) (K.smul_mem _ hy)) ?_
      rw [e']
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (hK' _ _ _ hz) (Submodule.smul_mem _ _ hz))
    obtain ⟨c, hc⟩ := htop (0, y) hy fun a => by simp [hEap, hyw]
    have hc1 : (0 : V₁) = c • v₁ := congrArg Prod.fst hc
    have hc2 : y = c • v₂ := congrArg Prod.snd hc
    rw [(smul_eq_zero.1 hc1.symm).resolve_right hv₁, zero_smul] at hc2
    rw [hyz, hc2, zero_add]
    exact hz
  let T : Submodule ℂ (V₁ × V₂) := S ⊓ Kᗮ.comap (LinearMap.snd ℂ V₁ V₂)
  have hT : ∀ a b, ∀ x ∈ T, E a b x ∈ T := fun a b x hx => ⟨hS a b x hx.1, hK' a b _ hx.2⟩
  have hvT : (v₁, v₂) ∈ T := ⟨hvS, hv₂⟩
  have hb : Function.Bijective ((LinearMap.fst ℂ V₁ V₂).comp T.subtype) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨⟨x, y⟩, hx⟩ h0
      obtain rfl : x = 0 := h0
      obtain rfl : y = 0 := Submodule.disjoint_def.1 K.orthogonal_disjoint y hx.1 hx.2
      rfl
    · rcases h₁ (T.map (LinearMap.fst ℂ V₁ V₂)) (by
        rintro a b _ ⟨x, hx, rfl⟩
        exact ⟨E a b x, hT a b x hx, rfl⟩) with h | h
      · have hm : v₁ ∈ T.map (LinearMap.fst ℂ V₁ V₂) := ⟨_, hvT, rfl⟩
        rw [h] at hm
        exact absurd hm hv₁
      · intro y
        have hm : y ∈ T.map (LinearMap.fst ℂ V₁ V₂) := by rw [h]; trivial
        obtain ⟨x, hx, rfl⟩ := hm
        exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨((LinearMap.snd ℂ V₁ V₂).comp T.subtype).comp (LinearEquiv.ofBijective _ hb).symm.toLinearMap, ?_, ?_⟩
  · intro a b x
    obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ hb).surjective x
    have h : E₁ a b (LinearEquiv.ofBijective _ hb y)
        = LinearEquiv.ofBijective _ hb ⟨E a b y, hT a b y y.2⟩ := rfl
    rw [h]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  · have h : v₁ = LinearEquiv.ofBijective _ hb ⟨(v₁, v₂), hvT⟩ := rfl
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, (LinearEquiv.symm_apply_eq _).2 h]
    rfl

open Formalism.MainNotions.S in

theorem exists_intertwiner : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (Δ : E), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ Λ ⊤ → IsURepOn (UJset (allPos k)) π → (∀ w : E, DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w) (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j)) → Δ ≠ 0 → (∀ a b : Fin k, a < b → ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) → IsWtOn (Formalism.REAL.Kset (allPos k)) π Λ Δ → ∃ L : H →ₗ[ℂ] E, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = π g (L u)) ∧ ∃ v, L v = Δ := by
  intro k Λ H _ _ _ τ E _ _ _ π Δ hτ hK hπ hd _ hup hwt
  have : Nontrivial H := by
    obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
    exact nontrivial_of_ne v 0 hv
  have hτ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) τ := hτ
  have hπ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π := hπ
  obtain ⟨E₁, g₁, d₁, i₁, x₁, hx₁, w₁⟩ :=
    GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest (Λ := Λ) hτ' hK
  obtain ⟨E₂, g₂, u₂, d₂⟩ := GlobalTheory.UnitaryDerived.exists_derived_action k E π hπ'
  have w₂ : Formalism.REAL.IsHW E₂ (fun a => (Λ a : ℂ)) Δ :=
    ⟨GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E₂ d₂ Λ Δ hwt,
      fun a b hab => raising_eq_zero E₂ Δ (fun Z hZ => d₂ Z hZ Δ) (hd Δ) (hup a b hab)⟩
  obtain ⟨L, hL, hLx⟩ := exists_lie_map E₁ E₂ _ x₁ Δ g₁ g₂
    (fun a b x y => by simpa [Formalism.REAL.sgn, PI.UpqRep.allPos] using u₂ a b x y) i₁ w₁ w₂ hx₁
  refine ⟨L, fun g hg x => ?_, x₁, hLx⟩
  obtain ⟨Y, hY, hg', -⟩ := Formalism.REAL.compact_exponential_surjective k (PI.UpqRep.allPos k) g
    ((GlobalTheory.UnitaryHighestWeight.mem_K_iff g).2 hg)
  have hZ : Yᴴ = -Y := by
    have h : Yᴴ * PI.UpqRep.Jm (PI.UpqRep.allPos k) + PI.UpqRep.Jm (PI.UpqRep.allPos k) * Y = 0 := hY.1
    rw [GlobalTheory.UnitaryHighestWeight.Jm_allPos, Matrix.mul_one, Matrix.one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  have h := GlobalTheory.UnitaryHighestWeightUnique.intertwine_group
    (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E₁ a b)
    (GlobalTheory.UnitaryHighestWeight.group_zero hτ' _) (GlobalTheory.UnitaryHighestWeight.group_add hτ' hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using d₁ _ hZ w)
    (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E₂ a b)
    (GlobalTheory.UnitaryHighestWeight.group_zero hπ' _) (GlobalTheory.UnitaryHighestWeight.group_add hπ' hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using d₂ _ hZ w)
    L (fun w => by simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hL]) x 1
  simpa [hg'] using h

end GlobalTheory.HighestWeightMap
