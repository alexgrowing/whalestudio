import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DualLattice

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.almost_selfdual_swap {A : Type} [CommRing A] {F V : Type} [Field F]
    [Algebra A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V]
    (Bf : LinearMap.BilinForm F V) (hs : Bf.IsSymm) {M N : Submodule A V}
    (h : M ≤ Bf.dualSubmodule N) : N ≤ Bf.dualSubmodule M := by
  intro x hx
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  have h1 := (Bf.mem_dualSubmodule).1 (h hy) x hx
  rwa [hs.eq] at h1

private theorem UpperTheory.V.AlgebraTools.almost_selfdual_move {A : Type} [CommRing A] {F V : Type} [Field F]
    [Algebra A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V]
    (Bf : LinearMap.BilinForm F V) (I : Ideal A) {M N : Submodule A V}
    (h : I • M ≤ Bf.dualSubmodule N) : M ≤ Bf.dualSubmodule (I • N) := by
  intro x hx
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro z hz
  refine Submodule.smul_induction_on (p := fun z => Bf x z ∈ (1 : Submodule A F)) hz ?_ ?_
  · intro a ha n hn
    have h1 := (Bf.mem_dualSubmodule).1 (h (Submodule.smul_mem_smul ha hx)) n hn
    have e1 : Bf x (a • n) = algebraMap A F a * Bf x n := by
      rw [← algebraMap_smul F a n, map_smul, smul_eq_mul]
    have e2 : Bf (a • x) n = algebraMap A F a * Bf x n := by
      rw [← algebraMap_smul F a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
    show Bf x (a • n) ∈ (1 : Submodule A F)
    rw [e1, ← e2]
    exact h1
  · intro y z hy hz
    show Bf x (y + z) ∈ (1 : Submodule A F)
    rw [map_add]
    exact Submodule.add_mem _ hy hz

private theorem UpperTheory.V.AlgebraTools.almost_selfdual_smul {A : Type} [CommRing A] {F V : Type} [Field F]
    [Algebra A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V]
    (f : Module.End F V) (I : Ideal A) {M : Submodule A V} (h : ∀ y ∈ M, f y ∈ M) :
    ∀ y ∈ I • M, f y ∈ I • M := by
  intro y hy
  refine Submodule.smul_induction_on (p := fun y => f y ∈ I • M) hy ?_ ?_
  · intro a ha n hn
    show f (a • n) ∈ I • M
    rw [← algebraMap_smul F a n, map_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul ha (h n hn)
  · intro y z hy hz
    show f (y + z) ∈ I • M
    rw [map_add]
    exact Submodule.add_mem _ hy hz

private theorem UpperTheory.V.AlgebraTools.map_mem_dualSubmodule_of_bilinForm_similitude {A : Type} [CommRing A] {F V G : Type} [Field F]
    [Algebra A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Group G]
    (Bf : LinearMap.BilinForm F V) (r : G →* Module.End F V) (σ : G → G) (u : G → A)
    (hr : ∀ g y z, Bf (r g y) (r (σ g) z) = algebraMap A F (u g) * Bf y z)
    {Y : Submodule A V} (hY : ∀ g, ∀ y ∈ Y, r g y ∈ Y) :
    ∀ g, ∀ y ∈ Bf.dualSubmodule Y, r g y ∈ Bf.dualSubmodule Y := by
  intro g y hy
  rw [LinearMap.BilinForm.mem_dualSubmodule] at hy ⊢
  intro z hz
  have hz' : r (σ g) (r (σ g)⁻¹ z) = z := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hy _ (hY _ _ hz))
  rw [← hz', hr, ← ha, ← map_mul]
  exact Submodule.mem_one.mpr ⟨_, rfl⟩

private theorem UpperTheory.V.AlgebraTools.end_apply_mem_sup_of_apply_mem {A : Type} [CommRing A] {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] [Module A V] (f : Module.End F V) {P Q : Submodule A V}
    (hP : ∀ y ∈ P, f y ∈ P) (hQ : ∀ y ∈ Q, f y ∈ Q) : ∀ y ∈ P ⊔ Q, f y ∈ P ⊔ Q := by
  intro y hy
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add]
  exact Submodule.add_mem_sup (hP p hp) (hQ q hq)

theorem UpperTheory.V.AlgebraTools.almost_selfdual :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F V G : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Module.Finite F V] [Group G] (Bf : LinearMap.BilinForm F V) (r : G →* Module.End F V) (σ : G → G) (u : G → A), Bf.IsSymm → Bf.Nondegenerate → Function.Surjective σ → (∀ g y z, Bf (r g y) (r (σ g) z) = algebraMap A F (u g) * Bf y z) → ∀ Y₀ : Submodule A V, Submodule.IsLattice F Y₀ → (∀ g, ∀ y ∈ Y₀, r g y ∈ Y₀) → ∃ Y : Submodule A V, Submodule.IsLattice F Y ∧ (∀ g, ∀ y ∈ Y, r g y ∈ Y) ∧ (∀ g, ∀ y ∈ Bf.dualSubmodule Y, r g y ∈ Bf.dualSubmodule Y) ∧ Y ≤ Bf.dualSubmodule Y ∧ maximalIdeal A • Bf.dualSubmodule Y ≤ Y := by
  intro A _ _ _ F V G _ _ _ _ _ _ _ _ _ Bf r σ u hs hnd hσ hr Y₀ hY₀ hst₀
  classical
  have anti : ∀ {P Q : Submodule A V}, P ≤ Q → Bf.dualSubmodule Q ≤ Bf.dualSubmodule P :=
    fun hPQ x hx => (Bf.mem_dualSubmodule).2 fun y hy => (Bf.mem_dualSubmodule).1 hx y (hPQ hy)
  have dst : ∀ Y : Submodule A V, (∀ g, ∀ y ∈ Y, r g y ∈ Y) →
      ∀ g, ∀ y ∈ Bf.dualSubmodule Y, r g y ∈ Bf.dualSubmodule Y :=
    fun Y hY => UpperTheory.V.AlgebraTools.map_mem_dualSubmodule_of_bilinForm_similitude Bf r σ u hr hY
  have key : ∀ n : ℕ, ∀ Y : Submodule A V, Submodule.IsLattice F Y → (∀ g, ∀ y ∈ Y, r g y ∈ Y) →
      Y ≤ Bf.dualSubmodule Y → maximalIdeal A ^ n • Bf.dualSubmodule Y ≤ Y →
      ∃ Y : Submodule A V, Submodule.IsLattice F Y ∧ (∀ g, ∀ y ∈ Y, r g y ∈ Y) ∧
        (∀ g, ∀ y ∈ Bf.dualSubmodule Y, r g y ∈ Bf.dualSubmodule Y) ∧ Y ≤ Bf.dualSubmodule Y ∧
        maximalIdeal A • Bf.dualSubmodule Y ≤ Y := by
    intro n
    induction n with
    | zero =>
      intro Y hY hst hle hn
      refine ⟨Y, hY, hst, dst Y hst, hle, le_trans Submodule.smul_le_right ?_⟩
      simpa using hn
    | succ n ih =>
      intro Y hY hst hle hn
      rcases n with _ | k
      · exact ⟨Y, hY, hst, dst Y hst, hle, by simpa using hn⟩
      · have hDY := (UpperTheory.V.AlgebraTools.dual_lattice Bf hs hnd Y hY).1
        have hDDY : Y ≤ Bf.dualSubmodule (Bf.dualSubmodule Y) :=
          UpperTheory.V.AlgebraTools.almost_selfdual_swap Bf hs le_rfl
        have hsm : maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y ≤ Bf.dualSubmodule Y :=
          Submodule.smul_le_right
        have hYW : Y ≤ Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y := le_sup_left
        have hWD : Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y ≤ Bf.dualSubmodule Y :=
          sup_le hle hsm
        have hWl : Submodule.IsLattice F (Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y) := by
          haveI := hY
          haveI := hDY
          refine Submodule.IsLattice.of_le_of_isLattice_of_fg F hYW ?_
          have : IsNoetherian A ↥(Bf.dualSubmodule Y) := inferInstance
          have : IsNoetherian A
              ↥(Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y : Submodule A V) :=
            isNoetherian_of_le hWD
          exact Module.Finite.iff_fg.mp inferInstance
        have hWst : ∀ g, ∀ y ∈ Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y,
            r g y ∈ Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y := fun g =>
          UpperTheory.V.AlgebraTools.end_apply_mem_sup_of_apply_mem (r g) (hst g)
            (UpperTheory.V.AlgebraTools.almost_selfdual_smul (r g) _ (dst Y hst g))
        have hsq : maximalIdeal A ^ (k + 1) • (maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y) ≤
            Bf.dualSubmodule (Bf.dualSubmodule Y) := by
          rw [← Submodule.mul_smul, ← pow_add]
          refine le_trans (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl)
            (le_trans hn hDDY)
        have hWW : Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y ≤
            Bf.dualSubmodule (Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y) := by
          refine sup_le (UpperTheory.V.AlgebraTools.almost_selfdual_swap Bf hs hWD) ?_
          refine UpperTheory.V.AlgebraTools.almost_selfdual_swap Bf hs (sup_le ?_ ?_)
          · exact UpperTheory.V.AlgebraTools.almost_selfdual_swap Bf hs hsm
          · exact UpperTheory.V.AlgebraTools.almost_selfdual_move Bf _ hsq
        have hWdual : maximalIdeal A ^ (k + 1) •
            Bf.dualSubmodule (Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y) ≤
            Y ⊔ maximalIdeal A ^ (k + 1) • Bf.dualSubmodule Y :=
          le_trans (Submodule.smul_mono le_rfl (anti hYW)) le_sup_right
        exact ih _ hWl hWst hWW hWdual
  have hD₀ := (UpperTheory.V.AlgebraTools.dual_lattice Bf hs hnd Y₀ hY₀).1
  haveI := hY₀
  haveI := hD₀
  have hY₁ : Submodule.IsLattice F (Y₀ ⊓ Bf.dualSubmodule Y₀) := inferInstance
  have hst₁ : ∀ g, ∀ y ∈ Y₀ ⊓ Bf.dualSubmodule Y₀, r g y ∈ Y₀ ⊓ Bf.dualSubmodule Y₀ :=
    fun g y hy => Submodule.mem_inf.mpr
      ⟨hst₀ g y (Submodule.mem_inf.mp hy).1, dst Y₀ hst₀ g y (Submodule.mem_inf.mp hy).2⟩
  have hle₁ : Y₀ ⊓ Bf.dualSubmodule Y₀ ≤ Bf.dualSubmodule (Y₀ ⊓ Bf.dualSubmodule Y₀) :=
    le_trans inf_le_right (anti inf_le_left)
  obtain ⟨s, hs'⟩ := (UpperTheory.V.AlgebraTools.dual_lattice Bf hs hnd _ hY₁).2.2 _
    (UpperTheory.V.AlgebraTools.dual_lattice Bf hs hnd _ hY₁).1
  exact key s _ hY₁ hst₁ hle₁ hs'
