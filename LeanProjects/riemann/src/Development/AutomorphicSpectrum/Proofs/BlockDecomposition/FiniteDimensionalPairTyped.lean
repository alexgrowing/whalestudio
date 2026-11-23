import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInfStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.FdPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_eq_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ = prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩
  · refine Submodule.span_mono ?_
    rintro F ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
    exact ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem map_typed {N : ℕ} (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E)))
    (W : Submodule ℂ (Kinf E N → ℂ)) :
    U.map (Sm E N).subtype ⊓ typeF K W = (typed U K W).map (Sm E N).subtype := by
  ext f
  constructor
  · rintro ⟨⟨φ, hφ, rfl⟩, hS⟩
    exact ⟨φ, ⟨hφ, hS⟩, rfl⟩
  · rintro ⟨φ, ⟨hφ, hS⟩, rfl⟩
    exact ⟨⟨φ, hφ, rfl⟩, hS⟩

theorem slice_left {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (y : GA E b) : (fun x => F (x, y)) ∈ typeF K₁ W₁ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have := hF.1 u hu 1 K₂.one_mem (g, y)
    simpa using this
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
      { toFun := fun f k => f (k, 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hL : Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
        ≤ W₁.comap L := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨w₁, h₁, w₂, h₂, rfl⟩
      have : L (fun k => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
        funext k
        simp [L, mul_comm]
      show L _ ∈ W₁
      rw [this]
      exact W₁.smul_mem _ h₁
    have := hL (hF.2 (g, y))
    simpa [L] using this

theorem slice_right {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (x : GA E a) : (fun y => F (x, y)) ∈ typeF K₂ W₂ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have := hF.1 1 K₁.one_mem u hu (x, g)
    simpa using this
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) :=
      { toFun := fun f k => f (1, k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hL : Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
        ≤ W₂.comap L := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨w₁, h₁, w₂, h₂, rfl⟩
      have : L (fun k => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
        funext k
        simp [L]
      show L _ ∈ W₂
      rw [this]
      exact W₂.smul_mem _ h₂
    have := hL (hF.2 (x, g))
    simpa [L] using this

theorem finiteDimensional_pairSpace_inf_typeHF : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)),
    FiniteDimensional ℂ (typed U₁ K₁ W₁) → FiniteDimensional ℂ (typed U₂ K₂ W₂) →
    FiniteDimensional ℂ ((pairSpace U₁ U₂ ⊓ typeHF K₁ K₂ W₁ W₂ : Submodule ℂ (H E a b → ℂ))) := by
  intro E _ _ _ a b U₁ U₂ K₁ K₂ W₁ W₂ h₁ h₂
  have f₁ : FiniteDimensional ℂ (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁ : Submodule ℂ (GA E a → ℂ)) := by
    rw [map_typed]; infer_instance
  have f₂ : FiniteDimensional ℂ (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂ : Submodule ℂ (GA E b → ℂ)) := by
    rw [map_typed]; infer_instance
  haveI hfd := GlobalTheory.T.finiteDimensional_prodSpan (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁) (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂) f₁ f₂
  refine Submodule.finiteDimensional_of_le (S₂ := prodSpan (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁)
    (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂)) ?_
  rintro F ⟨hU, hT⟩
  rw [SetLike.mem_coe, pairSpace_eq_prodSpan] at hU
  exact GlobalTheory.T.mem_prodSpan_inf _ _ _ _ F hU (fun y => slice_left hT y) (fun x => slice_right hT x)

end GlobalTheory.CompanionTheory.LimV.FdPair
