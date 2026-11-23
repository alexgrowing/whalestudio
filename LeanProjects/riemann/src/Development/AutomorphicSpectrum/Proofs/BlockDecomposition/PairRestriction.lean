import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV

namespace GlobalTheory.CompanionTheory.EGlue.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_le_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ ≤ prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem prodSpan_le_pairSpace (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) ≤ pairSpace U₁ U₂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem slice_mem (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) (m₁ : GA E a) :
    (fun y => F (m₁, y)) ∈ U₂.map (Sm E b).subtype := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, by funext y; simp⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.EGlue.Restrict

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairRestrict_holds : PairRestrict := by
  intro E _ _ _ a b U₁ U₂ U₂' F hF hs
  have hS₂ : ∀ m₁, (fun y => F (m₁, y)) ∈ U₂'.map (Sm E b).subtype := by
    intro m₁
    obtain ⟨φ, -, hφ⟩ := Restrict.slice_mem U₁ U₂ F hF m₁
    exact ⟨φ, hs m₁ φ hφ, hφ⟩
  have h := GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices (U₁.map (Sm E a).subtype) ⊤
    (U₂.map (Sm E b).subtype) (U₂'.map (Sm E b).subtype) F
    (Restrict.pairSpace_le_prodSpan U₁ U₂ hF) (fun _ => Submodule.mem_top) hS₂
  refine Restrict.prodSpan_le_pairSpace U₁ U₂' ?_
  refine Submodule.span_mono ?_ h
  rintro _ ⟨p, hp, q, hq, rfl⟩
  exact ⟨p, hp.1, q, hq.2, rfl⟩

end GlobalTheory.CompanionTheory.EGlue

end
