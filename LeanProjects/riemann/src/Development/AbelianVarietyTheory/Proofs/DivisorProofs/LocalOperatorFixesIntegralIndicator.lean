import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.VacFix

open scoped GlobalTheory.VacAny

variable {F : Type} [Field F] [NumberField F]

theorem eventually_evFin_mem (a : AF F) : ∀ᶠ v in cofinite, evFin F v a ∈ v.adicCompletionIntegers F := by
  filter_upwards [a.2.2] with v hv
  exact hv

theorem schr_indicator {κ : Type} [Fintype κ] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ)
    (hψ : ∀ y ∈ v.adicCompletionIntegers F, ψ₀ y = 1) (h2 : ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F)
    (w : (κ → Fv F v) × (κ → Fv F v)) (h1 : ∀ k, w.1 k ∈ v.adicCompletionIntegers F)
    (h2' : ∀ k, w.2 k ∈ v.adicCompletionIntegers F) :
    schr ψ₀ w (Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  funext x
  simp only [schr]
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have hs : ∀ i, (x + w.1) i ∈ v.adicCompletionIntegers F := fun i => add_mem (hx i) (h1 i)
    have hd : ∀ a b : κ → Fv F v, (∀ i, a i ∈ v.adicCompletionIntegers F) → (∀ i, b i ∈ v.adicCompletionIntegers F) →
        a ⬝ᵥ b ∈ v.adicCompletionIntegers F := fun a b ha hb =>
      sum_mem fun i _ => mul_mem (ha i) (hb i)
    rw [Set.indicator_of_mem (show x + w.1 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hs),
      Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx),
      hψ _ (add_mem (hd _ _ hx h2') (mul_mem h2 (hd _ _ h1 h2')))]
    simp
  · have hs : ¬ ∀ i, (x + w.1) i ∈ v.adicCompletionIntegers F := fun h => hx fun i => by
      have := sub_mem (h i) (h1 i)
      simpa using this
    rw [Set.indicator_of_notMem (show x + w.1 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hs),
      Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), mul_zero]

theorem eventually_locOp_rho_indicator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ u : Matrix (Fin n) (Fin d) (AE F E), ∀ᶠ v in cofinite,
      locOp v (M.co.rho ψ (partFin v u)) (Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
        Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ u
  have hO := (GlobalTheory.PsiStdCond.psi_std_conductor F ψ hψ).1
  have h2 := eventually_evFin_mem (F := F) (⅟(2 : AF F))
  have hc1 : ∀ᶠ v in cofinite, ∀ k, evFin F v ((M.co.e u).1 k) ∈ v.adicCompletionIntegers F :=
    eventually_all.2 fun k => eventually_evFin_mem _
  have hc2 : ∀ᶠ v in cofinite, ∀ k, evFin F v ((M.co.e u).2 k) ∈ v.adicCompletionIntegers F :=
    eventually_all.2 fun k => eventually_evFin_mem _
  filter_upwards [hO, h2, hc1, hc2] with v hv h2v h1v h2v'
  rw [(locOp_rho M.co hψ.1 v u (GlobalTheory.StdVacuum.indicator_mem_SB v)).2]
  refine schr_indicator v _ (fun y hy => ?_) (by rwa [GlobalTheory.VacAny.evFin_invOf_two] at h2v) _ h1v h2v'
  have h := (hv 1).2 (one_mem _) y hy
  rw [one_mul] at h
  exact h

end GlobalTheory.VacFix
