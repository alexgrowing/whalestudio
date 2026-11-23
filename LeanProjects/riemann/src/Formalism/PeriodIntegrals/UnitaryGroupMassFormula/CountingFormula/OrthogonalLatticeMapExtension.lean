import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeSameGenus
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AutSubApplyMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

namespace OrbitSumPf

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

def split (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (hz0 : h1 z z ≠ 0) : VecSplit h1 (hPerp h1 z) where
  x₀ := z
  ι := (wPerp h1 z).subtype
  inj := Subtype.val_injective
  hx₀ := hz0
  isom := fun _ _ => rfl
  orth := fun a => a.2
  cover := fun v => ⟨h1 z v / h1 z z, ⟨v - (h1 z v / h1 z z) • z, by
      show h1 z (v - (h1 z v / h1 z z) • z) = 0
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz0, sub_self]⟩, by simp⟩

variable {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1}

theorem one_mem_hz : (1 : V1 ≃ₗ[K] V1) ∈ hz h1 z := ⟨one_mem _, rfl⟩

theorem mul_mem_hz {σ τ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) (hτ : τ ∈ hz h1 z) : σ * τ ∈ hz h1 z := by
  simp only [hz, Set.mem_setOf_eq] at *
  refine ⟨mul_mem hσ.1 hτ.1, ?_⟩
  show σ (τ z) = z
  rw [hτ.2, hσ.2]

theorem inv_mem_hz {σ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) : σ⁻¹ ∈ hz h1 z := by
  simp only [hz, Set.mem_setOf_eq] at *
  refine ⟨inv_mem hσ.1, ?_⟩
  show σ.symm z = z
  rw [LinearEquiv.symm_apply_eq, hσ.2]

theorem glue_gmap {σ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) {M : Submodule (𝓞 K) V1} (hM : IsGlueLat h1 z M) :
    IsGlueLat h1 z (Formalism.HermitianLatticesTheory.gmap σ M) := by
  obtain ⟨hL, hU, hzM, hp⟩ := hM
  obtain ⟨_, _, _, hUi, hLi⟩ := Formalism.HermitianLatticesTheory.isomAct (𝓞 K) K V1 h1 σ hσ.1 M
  refine ⟨hLi.2 hL, hUi.2 hU, ?_, ?_⟩
  · rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, SplitBAux.symm_fix hσ.2]
    exact hzM
  · intro c hc
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, map_smul, SplitBAux.symm_fix hσ.2] at hc
    exact hp c hc

variable (hz0 : h1 z z ≠ 0)

theorem extOf_mem_hz (hs : h1.IsSymm) {a : wPerp h1 z ≃ₗ[K] wPerp h1 z}
    (ha : a ∈ Formalism.HermitianLatticesTheory.isom (hPerp h1 z)) : SplitBAux.extOf (split h1 z hz0) a ∈ hz h1 z :=
  ⟨SplitBAux.extOf_mem_isom hs _ ha, SplitBAux.extOf_x₀ (split h1 z hz0) a⟩

theorem orthogonal_lattice_map_extension (a : wPerp h1 z ≃ₗ[K] wPerp h1 z) (M : Submodule (𝓞 K) V1) :
    l0 h1 z (Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf (split h1 z hz0) a) M) = Formalism.HermitianLatticesTheory.gmap a (l0 h1 z M) :=
  StabilizerLattices.cut_gmap_extOf (split h1 z hz0) a M

def resZ {σ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) : wPerp h1 z ≃ₗ[K] wPerp h1 z :=
  SplitBAux.res (split h1 z hz0) σ hσ.1 hσ.2

theorem resZ_mem {σ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) : resZ hz0 hσ ∈ Formalism.HermitianLatticesTheory.isom (hPerp h1 z) :=
  SplitBAux.res_mem_isom _ σ hσ.1 hσ.2

theorem orthogonal_lattice_map_restrict {σ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) (M : Submodule (𝓞 K) V1) :
    Formalism.HermitianLatticesTheory.gmap (resZ hz0 hσ) (l0 h1 z M) = l0 h1 z (Formalism.HermitianLatticesTheory.gmap σ M) :=
  SplitBAux.gmap_res _ σ hσ.1 hσ.2 rfl

theorem extOf_resZ {σ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) :
    SplitBAux.extOf (split h1 z hz0) (resZ hz0 hσ) = σ :=
  LIOrb.OrbF.extOf_res _ hσ.1 hσ.2

theorem resZ_extOf (hs : h1.IsSymm) {a : wPerp h1 z ≃ₗ[K] wPerp h1 z}
    (ha : a ∈ Formalism.HermitianLatticesTheory.isom (hPerp h1 z)) :
    resZ hz0 (extOf_mem_hz hz0 hs ha) = a := by
  ext w
  have := SplitBAux.res_spec (split h1 z hz0) _ (extOf_mem_hz hz0 hs ha).1 (extOf_mem_hz hz0 hs ha).2 w
  rw [SplitBAux.extOf_ι] at this
  exact congrArg Subtype.val ((split h1 z hz0).inj this)

private theorem gmap_mul_lemma {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (a b : W ≃ₗ[K] W) (N : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.gmap (a * b) N = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b N) := by
  simp only [Formalism.HermitianLatticesTheory.gmap, ← Submodule.map_comp]
  rfl

theorem gmap_inv_gmap' {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (a : W ≃ₗ[K] W) (N : Submodule (𝓞 K) W) : Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a N) = N := by
  rw [← gmap_mul_lemma, inv_mul_cancel]
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem card_stabZ_conj {τ : V1 ≃ₗ[K] V1} (hτ : τ ∈ hz h1 z) (M : Submodule (𝓞 K) V1) :
    Nat.card (stabZ h1 z (Formalism.HermitianLatticesTheory.gmap τ M)) = Nat.card (stabZ h1 z M) := by
  apply Nat.card_congr
  refine
    { toFun := fun σ => ⟨τ⁻¹ * σ.1 * τ, ?_⟩
      invFun := fun σ => ⟨τ * σ.1 * τ⁻¹, ?_⟩
      left_inv := fun σ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun σ => Subtype.ext (by simp [mul_assoc]) }
  · obtain ⟨a1, a2⟩ := σ.2
    exact ⟨mul_mem_hz (mul_mem_hz (inv_mem_hz hτ) a1) hτ, by
      rw [gmap_mul_lemma, gmap_mul_lemma, a2, gmap_inv_gmap']⟩
  · obtain ⟨a1, a2⟩ := σ.2
    refine ⟨mul_mem_hz (mul_mem_hz hτ a1) (inv_mem_hz hτ), ?_⟩
    rw [gmap_mul_lemma, gmap_mul_lemma, gmap_inv_gmap', a2]

@[reducible] def actL (L : Submodule (𝓞 K) (wPerp h1 z)) :
    MulAction (autSub (hPerp h1 z) L) (Submodule (𝓞 K) V1) where
  smul a M := Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf (split h1 z hz0) a.1) M
  one_smul M := by
    change Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf (split h1 z hz0) 1) M = M
    rw [LIOrb.OrbF.extOf_one, autSub_gmap_one]
  mul_smul a b M := by
    change Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf (split h1 z hz0) (a.1 * b.1)) M = _
    rw [LIOrb.OrbF.extOf_mul, autSub_gmap_mul]
    rfl

theorem memAut {h0 : wPerp h1 z →ₗ⋆[K] wPerp h1 z →ₗ[K] K} {L : Submodule (𝓞 K) (wPerp h1 z)}
    (a : autSub h0 L) : a.1 ∈ Formalism.HermitianLatticesTheory.isom h0 ∧ Formalism.HermitianLatticesTheory.gmap a.1 L = L := a.2

end OrbitSumPf

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
