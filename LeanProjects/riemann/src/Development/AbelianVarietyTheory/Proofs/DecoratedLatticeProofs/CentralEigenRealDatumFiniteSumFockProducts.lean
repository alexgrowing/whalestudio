import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.FinRank

theorem span_eval_eq_top {α : Type*} (E : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ E] :
    Submodule.span ℂ (Set.range fun u : α => (LinearMap.proj u : (α → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) = ⊤ := by
  set Sp := Submodule.span ℂ (Set.range fun u : α => (LinearMap.proj u : (α → ℂ) →ₗ[ℂ] ℂ).comp E.subtype)
  have hb : Sp.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext u
    have := hx _ (Submodule.subset_span ⟨u, rfl⟩)
    simpa using this
  have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Sp)
  rw [← this, hb, Submodule.dualAnnihilator_bot]

theorem sum_prod_of_slices {α β : Type*} (C : α → β → ℂ) (E : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ E]
    (E' : Submodule ℂ (β → ℂ)) (hl : ∀ v, (fun u => C u v) ∈ E) (hr : ∀ u, C u ∈ E') :
    ∃ (n : ℕ) (e : Fin n → α → ℂ) (g : Fin n → β → ℂ), (∀ i, e i ∈ E) ∧ (∀ i, g i ∈ E') ∧
      ∀ u v, C u v = ∑ i, e i u * g i v := by
  let b := Module.finBasis ℂ E
  let ev : α → Module.Dual ℂ E := fun u => (LinearMap.proj u : (α → ℂ) →ₗ[ℂ] ℂ).comp E.subtype
  have hsurj : ∀ φ : Module.Dual ℂ E, ∃ a : α →₀ ℂ, Finsupp.linearCombination ℂ ev a = φ := by
    intro φ
    have h1 : φ ∈ LinearMap.range (Finsupp.linearCombination ℂ ev) := by
      rw [Finsupp.range_linearCombination]
      rw [span_eval_eq_top E]
      trivial
    exact h1
  choose a ha using fun i => hsurj (b.coord i)
  refine ⟨Module.finrank ℂ E, fun i => (b i : α → ℂ), fun i => ∑ u ∈ (a i).support, a i u • C u,
    fun i => (b i).2, fun i => Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (hr u), ?_⟩
  intro u v
  have hs := b.sum_repr ⟨fun u => C u v, hl v⟩
  have h2 := congrArg (fun w : E => (w : α → ℂ) u) hs
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 1
  have h3 := congrArg (fun φ : Module.Dual ℂ E => φ ⟨fun u => C u v, hl v⟩) (ha i)
  simp only [Module.Basis.coord_apply] at h3
  rw [← h3, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  simp [ev, Finset.sum_apply]

end GlobalTheory.SeeSaw.FinRank

namespace GlobalTheory.SeeSaw.FinRank

theorem biVac_sum_fock : ∀ (D : D7), CenFock D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (χ' : GA D S → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k.om (a, 1) (fun u => C u v) = χ a • fun u => C u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k'.om (b, 1) (C u) = χ' b • C u) → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := by
  intro D hF ψ θ hθ A S A' x y z hx hy hz k k' hk hk' χ χ' C hC hχ hχ'
  obtain ⟨W, hW, hWf⟩ := hF ψ θ hθ A S x y hx hy k hk χ
  obtain ⟨W', _, hWf'⟩ := hF ψ θ hθ S A' y z hy hz k' hk' χ'
  haveI := hW
  let T := pureTensorO ψ θ A S x.s y.s x.B y.B k.vac
  let T' := pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac
  have hl : ∀ v, (fun u => C u v) ∈ W.map T := by
    intro v
    obtain ⟨P, hP, e⟩ := hWf _ (hC.left v).1 (hC.left v).2 (fun a ha hc => hχ a ha hc v)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  have hr : ∀ u, C u ∈ W'.map T' := by
    intro u
    obtain ⟨P, hP, e⟩ := hWf' _ (hC.right u).1 (hC.right u).2 (fun b hb hc => hχ' b hb hc u)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  obtain ⟨n, e, g, he, hg, hs⟩ := sum_prod_of_slices C (W.map T) (W'.map T') hl hr
  choose P _ hP using fun i => Submodule.mem_map.1 (he i)
  choose P' _ hP' using fun i => Submodule.mem_map.1 (hg i)
  refine ⟨n, P, P', fun u v => ?_⟩
  rw [hs u v]
  refine Finset.sum_congr rfl fun i _ => ?_
  show e i u * g i v = T (P i) u * T' (P' i) v
  rw [hP i, hP' i]

end GlobalTheory.SeeSaw.FinRank

end
