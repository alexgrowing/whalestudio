import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.Slices

variable {A B : Type}

theorem span_eval_eq_top (W : Submodule ℂ (B → ℂ)) [FiniteDimensional ℂ W] :
    Submodule.span ℂ (Set.range fun y : B =>
      ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) = ⊤ := by
  set E := Submodule.span ℂ (Set.range fun y : B =>
      ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) with hE
  have hbot : E.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have : (w : B → ℂ) = 0 := by
      funext y
      exact hw _ (Submodule.subset_span ⟨y, rfl⟩)
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := E)
  rw [hbot] at h
  rw [← h]
  simp

theorem mem_prodSpan_inf_left (U S : Submodule ℂ (A → ℂ)) (V : Submodule ℂ (B → ℂ))
    (G : A × B → ℂ) (hG : G ∈ prodSpan U V) (hS : ∀ y, (fun x => G (x, y)) ∈ S) :
    G ∈ prodSpan (U ⊓ S) V := by
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.1 hG
  choose a ha b hb hg using fun i => (g i).2
  let W : Submodule ℂ (B → ℂ) := Submodule.span ℂ (Set.range b)
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  have hWV : W ≤ V := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  let bw : Fin n → W := fun i => ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  let T : A → W := fun x => ∑ i, (f i * a i x) • bw i
  have hG' : ∀ x y, G (x, y) = ∑ i, f i * a i x * b i y := by
    intro x y
    rw [← hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, hg, smul_eq_mul, mul_assoc]
  have hT : ∀ x y, (T x : B → ℂ) y = G (x, y) := by
    intro x y
    rw [hG']
    simp [T, bw]
  have hφS : ∀ φ : Module.Dual ℂ W, (fun x => φ (T x)) ∈ S := by
    intro φ
    have hφ : φ ∈ Submodule.span ℂ (Set.range fun y : B =>
        ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) := by
      rw [span_eval_eq_top]; trivial
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨y, rfl⟩ := h
      simpa [hT] using hS y
    | zero => exact S.zero_mem
    | add φ ψ _ _ h₁ h₂ => exact S.add_mem h₁ h₂
    | smul r φ _ h => exact S.smul_mem r h
  have hφU : ∀ φ : Module.Dual ℂ W, (fun x => φ (T x)) ∈ U := by
    intro φ
    have : (fun x => φ (T x)) = ∑ i, (f i * φ (bw i)) • a i := by
      funext x
      simp only [T, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact U.sum_mem fun i _ => U.smul_mem _ (ha i)
  let c := Module.finBasis ℂ W
  have hdec : G = ∑ j, fun p : A × B => c.coord j (T p.1) * (c j : B → ℂ) p.2 := by
    funext ⟨x, y⟩
    rw [← hT, Finset.sum_apply]
    have h := congrArg (fun w : W => (w : B → ℂ) y) (c.sum_repr (T x))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    simpa [Module.Basis.coord_apply] using h.symm
  rw [hdec]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span
    ⟨_, ⟨hφU (c.coord j), hφS (c.coord j)⟩, _, hWV (c j).2, rfl⟩

theorem swap_mem_prodSpan (U : Submodule ℂ (A → ℂ)) (V : Submodule ℂ (B → ℂ))
    (G : A × B → ℂ) (hG : G ∈ prodSpan U V) : (fun p : B × A => G p.swap) ∈ prodSpan V U := by
  induction hG using Submodule.span_induction with
  | mem F h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact Submodule.subset_span ⟨b, hb, a, ha, by funext p; simp [mul_comm]⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

theorem mem_prodSpan_inf_of_slices : ∀ {A B : Type} (U₁ S₁ : Submodule ℂ (A → ℂ))
    (U₂ S₂ : Submodule ℂ (B → ℂ)) (G : A × B → ℂ), G ∈ prodSpan U₁ U₂ →
    (∀ y, (fun x => G (x, y)) ∈ S₁) → (∀ x, (fun y => G (x, y)) ∈ S₂) →
    G ∈ prodSpan (U₁ ⊓ S₁) (U₂ ⊓ S₂) := by
  intro A B U₁ S₁ U₂ S₂ G hG h₁ h₂
  have hL := mem_prodSpan_inf_left U₁ S₁ U₂ G hG h₁
  have hR := mem_prodSpan_inf_left U₂ S₂ (U₁ ⊓ S₁) (fun p : B × A => G p.swap)
    (swap_mem_prodSpan _ _ G hL) (fun x => h₂ x)
  simpa using swap_mem_prodSpan _ _ _ hR

end GlobalTheory.CompanionTheory.LimV.Slices

end
