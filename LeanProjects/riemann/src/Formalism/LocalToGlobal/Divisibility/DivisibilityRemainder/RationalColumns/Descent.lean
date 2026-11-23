import Formalism.LocalRingCardinality.DataBu

noncomputable section

namespace Formalism.L2.DIV.PerDescent

open Formalism.BasicNotions

theorem perCol_smul (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (c : ℂ) (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (c • F) = c * D.what₂.perCol u D.what₂.mu0 φ F := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, smul_eq_mul]

def perLin (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) : D.what₂.Amb D.what₂.mu0 →ₗ[ℂ] ℂ where
  toFun F := D.what₂.perCol u D.what₂.mu0 φ F
  map_add' F G := D.perCol_add u φ F G
  map_smul' c F := by simpa using perCol_smul D u φ c F

theorem exists_ext (D : D7) (γ : D.div.RR.V →ₗ[D.what₂.LL] D.what₂.LL) :
    ∃ Λ : D.what₂.EE →ₗ[ℂ] ℂ, ∀ v, Λ (D.jEE v) = D.what₂.embLL (γ v) := by
  let B : Module.Basis D.div.RR.ι ℂ D.what₂.EE := Module.Basis.mk D.jEE_basis.1 (le_of_eq D.jEE_basis.2.symm)
  refine ⟨B.constr ℂ fun i => D.what₂.embLL (γ (D.div.RR.b i)), fun v => ?_⟩
  have hB : ∀ i, B i = D.jEE (D.div.RR.b i) := fun i => Module.Basis.mk_apply _ _ i
  conv_lhs => rw [← D.div.RR.b.linearCombination_repr v]
  conv_rhs => rw [← D.div.RR.b.linearCombination_repr v]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, map_smul, ← hB, Module.Basis.constr_basis, map_smul, smul_eq_mul, smul_eq_mul, map_mul]

theorem per_sec (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) {n d : ℕ} (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0)
    (a : (Fin n → D.what₂.LL) → D.what₂.Amb μ)
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) (p : (Fin n → D.what₂.LL) → (Fin d → D.what₂.LL))
    (β : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] D.what₂.LL)
    (hp : Function.Surjective p)
    (hV : D.what₂.V0 μ = Submodule.span ℂ (Set.range a))
    (hι : ∀ F, D.what₂.iota μ (a F) = D.jEE (e (p F)))
    (hper : ∀ F, D.what₂.perCol u μ φ (a F) = D.what₂.embLL (β (p F))) (y : Fin d → D.what₂.LL) :
    D.what₂.perCol u D.what₂.mu0 φ (D.what₂.sec D.what₂.mu0 (D.jEE (e y))) = D.what₂.embLL (β y) := by
  subst hμ
  obtain ⟨Λ, hΛ⟩ := exists_ext D (β ∘ₗ e.symm.toLinearMap)

  have hEq : ∀ F ∈ D.what₂.V0 D.what₂.mu0, perLin D u φ F = (Λ ∘ₗ D.what₂.iota D.what₂.mu0) F := by
    intro F hF
    rw [hV] at hF
    refine LinearMap.eqOn_span (f := perLin D u φ) (g := Λ ∘ₗ D.what₂.iota D.what₂.mu0) ?_ hF
    rintro _ ⟨G, rfl⟩
    show D.what₂.perCol u D.what₂.mu0 φ (a G) = Λ (D.what₂.iota D.what₂.mu0 (a G))
    rw [hper, hι, hΛ]
    simp
  obtain ⟨F, rfl⟩ := hp y
  have hF : a F ∈ D.what₂.V0 D.what₂.mu0 := by
    rw [hV]; exact Submodule.subset_span ⟨F, rfl⟩
  set nn : D.what₂.Amb D.what₂.mu0 := (D.what₂.Usp D.what₂.mu0).starProjection (a F) with hn
  have hnU : nn ∈ D.what₂.Usp D.what₂.mu0 := Submodule.starProjection_apply_mem _ _
  have hq : a F - nn ∈ D.what₂.Qsp D.what₂.mu0 :=
    ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal (a F)⟩
  have hιq : D.what₂.iota D.what₂.mu0 (a F - nn) = D.jEE (e (p F)) := by
    have : D.what₂.iota D.what₂.mu0 nn = 0 := hnU.2
    rw [map_sub, this, sub_zero, hι]
  rw [← hιq, D.what₂.sec_iota _ _ hq]
  have := hEq _ hq.1
  show perLin D u φ (a F - nn) = _
  rw [this, LinearMap.comp_apply, hιq, hΛ]
  simp

end Formalism.L2.DIV.PerDescent

end
