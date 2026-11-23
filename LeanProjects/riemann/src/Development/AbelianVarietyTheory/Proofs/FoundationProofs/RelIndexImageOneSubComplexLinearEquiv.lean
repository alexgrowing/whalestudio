import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.ThetaCovIndex

open GlobalTheory.ThetaInter Module

section General

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
set_option backward.isDefEq.respectTransparency false in

theorem relIndex_eq_abs_det {ι : Type} [Fintype ι] [DecidableEq ι] (b₁ b₂ : Basis ι ℝ W) {L₁ L₂ : AddSubgroup W}
    (h₁ : (Submodule.span ℤ (Set.range b₁)).toAddSubgroup = L₁)
    (h₂ : (Submodule.span ℤ (Set.range b₂)).toAddSubgroup = L₂) (h : L₁ ≤ L₂) :
    (L₁.relIndex L₂ : ℝ) = |b₂.det b₁| := by
  subst h₁ h₂
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ h (b₁.restrictScalars ℤ) (b₂.restrictScalars ℤ),
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  have := b₂.restrictScalars_repr_apply ℤ
    ⟨b₁.restrictScalars ℤ j, h (Submodule.coe_mem _)⟩ i
  refine this.trans ?_
  simp

theorem exists_basis_finrank {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ W)) ℝ W, (Submodule.span ℤ (Set.range b)).toAddSubgroup = A := by
  have : DiscreteTopology A.toIntSubmodule := hA
  have : IsZLattice ℝ A.toIntSubmodule := ⟨hsp⟩
  let b₀ := Module.finBasisOfFinrankEq ℤ A.toIntSubmodule (ZLattice.rank ℝ A.toIntSubmodule)
  refine ⟨b₀.ofZLatticeBasis ℝ A.toIntSubmodule, ?_⟩
  rw [Basis.ofZLatticeBasis_span]
  rfl

theorem relIndex_map {A B : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (f : W ≃ₗ[ℝ] W) (hB : B ≤ A)
    (hf : B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ≤ A) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ B, m • x = f y) :
    B.relIndex A ≠ 0 ∧ ((B.map (f : W →ₗ[ℝ] W).toAddMonoidHom).relIndex A : ℝ) =
      B.relIndex A * |LinearMap.det (f : W →ₗ[ℝ] W)| := by
  have hBd : DiscreteTopology B := DiscreteTopology.of_subset hA hB
  have hBs : Submodule.span ℝ (B : Set W) = ⊤ := by
    have h1 : (Submodule.span ℝ (B : Set W)).map (f : W →ₗ[ℝ] W) = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      intro x hxA
      obtain ⟨y, hy, e⟩ := hx x hxA
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      refine ⟨(m : ℝ)⁻¹ • y, Submodule.smul_mem _ _ (Submodule.subset_span hy), ?_⟩
      simp only [LinearEquiv.coe_coe, map_smul]
      rw [← e, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := (h1.ge (Submodule.mem_top (x := f x)))
    exact f.injective e ▸ hy
  obtain ⟨a, ha⟩ := exists_basis_finrank hA hsp
  obtain ⟨b, hb⟩ := exists_basis_finrank hBd hBs
  have hb₁ : (Submodule.span ℤ (Set.range (b.map f))).toAddSubgroup =
      B.map (f : W →ₗ[ℝ] W).toAddMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    have : f x ∈ B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ↔ x ∈ B :=
      AddSubgroup.mem_map_iff_mem (f := (f : W →ₗ[ℝ] W).toAddMonoidHom) f.injective
    rw [this, ← hb, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
      Module.Basis.mem_span_iff_repr_mem, Module.Basis.mem_span_iff_repr_mem]
    simp
  have e1 := relIndex_eq_abs_det b a hb ha hB
  generalize B.map (f : W →ₗ[ℝ] W).toAddMonoidHom = C at hf hb₁ ⊢
  have e2 := relIndex_eq_abs_det (b.map f) a hb₁ ha hf
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, Nat.cast_zero, eq_comm, abs_eq_zero] at e1
    exact IsUnit.ne_zero (a.isUnit_det b) e1
  · rw [e2, e1, ← abs_mul, mul_comm, ← a.det_comp (f : W →ₗ[ℝ] W) b, Basis.coe_map]
    rfl

end General

theorem relIndex_image_one_sub_complexLinearEquiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {A A₁ : AddSubgroup W} (t₁ : DiscreteTopology A) (s₁ : Submodule.span ℝ (A : Set W) = ⊤)
    (u : W ≃ₗ[ℂ] W) (hA : ∀ x, x ∈ A ↔ u x ∈ A₁)
    (hdet : LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W)) ≠ 0) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) :
    A₁.relIndex A ≠ 0 ∧
      (((A.map (LinearMap.id - (u.symm : W →ₗ[ℂ] W)).toAddMonoidHom).relIndex A : ℕ) : ℝ) =
        (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W))‖ ^ 2 := by
  set g : W →ₗ[ℂ] W := LinearMap.id - (u.symm : W →ₗ[ℂ] W) with hg
  have hgy : ∀ y, g y = y - u.symm y := fun y => rfl
  let f : W ≃ₗ[ℝ] W := (LinearMap.equivOfDetNeZero g hdet).restrictScalars ℝ
  have hfg : (f : W →ₗ[ℝ] W) = g.restrictScalars ℝ := by
    ext1 y; simp [f]
  have hfy : ∀ y, f y = y - u.symm y := fun y => congrArg (fun φ => φ y) hfg
  have hA' : ∀ y, u.symm y ∈ A ↔ y ∈ A₁ := fun y => by rw [hA, u.apply_symm_apply]
  have hinf : (A₁ ⊓ A).map (f : W →ₗ[ℝ] W).toAddMonoidHom = A.map g.toAddMonoidHom ⊓ A := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy₁, hy⟩, rfl⟩
      refine ⟨⟨y, hy, (hfy y).symm⟩, ?_⟩
      change f y ∈ A
      rw [hfy]
      exact A.sub_mem hy ((hA' y).2 hy₁)
    · rintro ⟨⟨y, hy, rfl⟩, h2⟩
      refine ⟨y, ⟨(hA' y).1 ?_, hy⟩, hfy y⟩
      have h3 : y - u.symm y ∈ A := h2
      simpa using A.sub_mem hy h3
  have key := relIndex_map (B := A₁ ⊓ A) t₁ s₁ f inf_le_right (hinf.le.trans inf_le_right) hm
    fun x hxA => by
      obtain ⟨y, hy, hy', e⟩ := hx x hxA
      exact ⟨y, ⟨(hA' y).1 hy', hy⟩, e.trans (hfy y).symm⟩
  rw [hinf, AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_right, hfg,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity)] at key
  exact key

theorem relIndex_one_sub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → A₁.relIndex A ≠ 0 ∧ ((((A.map (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')).toAddMonoidHom).relIndex A : ℕ) : ℝ)) = (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ ^ 2 := by
  intro D cc δ hc N N' A A₁ h₁ _ u _ hA hdet ⟨m, hm, hx⟩
  obtain ⟨f₁, s₁, d₁, -⟩ := klat_facts hc h₁
  have t₁ := discrete_of_selfDual (isHerm_sesqOf D (tor0 D cc δ) N N') d₁ f₁
  exact relIndex_image_one_sub_complexLinearEquiv t₁ s₁ u hA hdet hm hx

end GlobalTheory.ThetaCovIndex
