import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinC
import Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.CompactStandardSubgroup.KCptPf
import GroundTheory.PAdicHodge.NormalizedTrace

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (d : SD σ)

def kfS : Submodule ℂ d.Fn where
  carrier := {Φ | ∃ N : Submodule ℂ d.Fn, FiniteDimensional ℂ N ∧ N ≤ d.sch ∧ Φ ∈ N ∧ ∀ k ∈ d.K, ∀ Ψ ∈ N, d.om k Ψ ∈ N}
  zero_mem' := ⟨⊥, inferInstance, bot_le, zero_mem _, fun k _ g hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro f g ⟨N, _, h0, h1, h2⟩ ⟨N', _, h0', h1', h2'⟩
    refine ⟨N ⊔ N', inferInstance, sup_le h0 h0', Submodule.add_mem_sup h1 h1', fun k hk g hg => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
    rw [map_add]
    exact Submodule.add_mem_sup (h2 k hk x hx) (h2' k hk y hy)
  smul_mem' := fun c _ ⟨N, h, h0, h1, h2⟩ => ⟨N, h, h0, N.smul_mem c h1, h2⟩

variable {d}

theorem kFin_of_mem {Φ : d.Fn} (h : Φ ∈ kfS d) : d.KFin Φ := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  refine ⟨h0 h1, Submodule.finiteDimensional_of_le (S₂ := N) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨k, rfl⟩
  exact h2 k.1 k.2 Φ h1

theorem mem_sch {Φ : d.Fn} (h : Φ ∈ kfS d) : Φ ∈ d.sch := by
  obtain ⟨N, _, h0, h1, -⟩ := h
  exact h0 h1

end PositivityTheory.SiegelWeilFormula.KK

end
