import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.RatIntUnifDiscrete

namespace PI.UnitaryGroupMassFormula.TBDisc

open NumberField ReciprocityTheory.ChartRestriction.G.TB

theorem discOfProdLower : DiscOfProdLowerSt := by
  intro K _ _ V _ _ _ Nf M A h
  refine ⟨Real.exp (-|A|), Real.exp_pos _, fun f hf hs => ?_⟩
  by_contra hne
  have hA := h f hf hne
  have hpos : ∀ σ, 0 < Nf.N σ f := fun σ =>
    lt_of_le_of_ne (Nf.nonneg σ f) (fun h0 => hne (Nf.eq_zero σ f h0.symm))
  have hlt : ∑ σ : K →+* ℂ, Real.log (Nf.N σ f) < ∑ _σ : K →+* ℂ, (-|A|) := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun σ _ => ?_)
    have := Real.log_lt_log (hpos σ) (hs σ)
    rwa [Real.log_exp] at this
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  have hc : (1 : ℝ) ≤ (Fintype.card (K →+* ℂ) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1 : (Fintype.card (K →+* ℂ) : ℝ) * (-|A|) ≤ -|A| := by
    nlinarith [abs_nonneg A]
  linarith [le_abs_self A]

section FG

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

theorem normFam_zero (Nf : NormFam K V) (σ : K →+* ℂ) : Nf.N σ 0 = 0 := by
  have h := Nf.smul σ 0 0
  simpa using h

theorem normFam_sum_le (Nf : NormFam K V) (σ : K →+* ℂ) {ι : Type*} (s : Finset ι)
    (g : ι → V) : Nf.N σ (∑ i ∈ s, g i) ≤ ∑ i ∈ s, Nf.N σ (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [normFam_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Nf.add σ _ _).trans (by linarith)

variable [FiniteDimensional K V]

noncomputable def coordMap : V →+ ((K →+* ℂ) → Fin (Module.finrank K V) → ℂ) where
  toFun v σ i := σ ((Module.finBasis K V).repr v i)
  map_zero' := by ext; simp
  map_add' v w := by ext; simp

theorem norm_le_coord (Nf : NormFam K V) (σ : K →+* ℂ) (v : V) :
    Nf.N σ v ≤ ‖coordMap (K := K) v‖ * ∑ i, Nf.N σ (Module.finBasis K V i) := by
  have hv : v = ∑ i, (Module.finBasis K V).repr v i • Module.finBasis K V i :=
    ((Module.finBasis K V).sum_repr v).symm
  have hle : ∀ i, ‖σ ((Module.finBasis K V).repr v i)‖ ≤ ‖coordMap (K := K) v‖ := fun i =>
    (norm_le_pi_norm (coordMap (K := K) v σ) i).trans (norm_le_pi_norm (coordMap (K := K) v) σ)
  calc Nf.N σ v = Nf.N σ (∑ i, (Module.finBasis K V).repr v i • Module.finBasis K V i) := by
        conv_lhs => rw [hv]
    _ ≤ ∑ i, Nf.N σ ((Module.finBasis K V).repr v i • Module.finBasis K V i) := normFam_sum_le Nf σ _ _
    _ = ∑ i, ‖σ ((Module.finBasis K V).repr v i)‖ * Nf.N σ (Module.finBasis K V i) := by
        simp only [Nf.smul]
    _ ≤ ∑ i, ‖coordMap (K := K) v‖ * Nf.N σ (Module.finBasis K V i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (Nf.nonneg _ _)
    _ = ‖coordMap (K := K) v‖ * ∑ i, Nf.N σ (Module.finBasis K V i) := by rw [Finset.mul_sum]

theorem fg_of_unifDiscrete [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nf : NormFam K V)
    (M : Submodule (𝓞 K) V) (hM : UnifDiscrete Nf M) : M.FG := by
  obtain ⟨ε, hε, hsmall⟩ := hM
  set C : ℝ := ∑ σ : K →+* ℂ, ∑ i, Nf.N σ (Module.finBasis K V i) + 1 with hC
  have hS : ∀ σ, ∑ i, Nf.N σ (Module.finBasis K V i) ≤ C - 1 := fun σ => by
    rw [hC, add_sub_cancel_right]
    exact Finset.single_le_sum (f := fun σ => ∑ i, Nf.N σ (Module.finBasis K V i))
      (fun τ _ => Finset.sum_nonneg (fun i _ => Nf.nonneg _ _)) (Finset.mem_univ σ)
  have hCpos : 0 < C := by
    have : 0 ≤ C - 1 :=
      (Finset.sum_nonneg (fun i _ => Nf.nonneg _ _)).trans (hS (Classical.arbitrary _))
    linarith
  have hδ : 0 < ε / C := div_pos hε hCpos
  have key : ∀ f ∈ M, ‖coordMap (K := K) f‖ < ε / C → f = 0 := by
    intro f hf hlt
    refine hsmall f hf (fun σ => ?_)
    have h1 := norm_le_coord Nf σ f
    have h2 : ‖coordMap (K := K) f‖ * ∑ i, Nf.N σ (Module.finBasis K V i) ≤
        ‖coordMap (K := K) f‖ * C :=
      mul_le_mul_of_nonneg_left (by linarith [hS σ]) (norm_nonneg _)
    have h3 : ‖coordMap (K := K) f‖ * C < ε := by
      rwa [lt_div_iff₀ hCpos] at hlt
    linarith
  let P : Submodule ℤ V := M.restrictScalars ℤ
  let Ψ : P →ₗ[ℤ] ((K →+* ℂ) → Fin (Module.finrank K V) → ℂ) :=
    (coordMap (K := K) (V := V)).toIntLinearMap.comp P.subtype
  have hΨ : ∀ x : P, ‖Ψ x‖ < ε / C → x = 0 := fun x hx => Subtype.ext (key x x.2 hx)
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    have : x - y = 0 := hΨ _ (by rw [map_sub, hxy, sub_self, norm_zero]; exact hδ)
    exact sub_eq_zero.mp this
  have : DiscreteTopology (LinearMap.range Ψ) := by
    refine discreteTopology_iff_isOpen_singleton.mpr (fun z => Metric.isOpen_singleton_iff.mpr
      ⟨ε / C, hδ, fun y hy => ?_⟩)
    obtain ⟨_, ⟨x, rfl⟩⟩ := z
    obtain ⟨_, ⟨x', rfl⟩⟩ := y
    rw [Subtype.dist_eq, dist_eq_norm, ← map_sub] at hy
    have := hΨ _ hy
    rw [sub_eq_zero] at this
    subst this
    rfl
  have : Module.Finite ℤ P := Module.Finite.equiv (LinearEquiv.ofInjective Ψ hinj).symm
  obtain ⟨s, hs⟩ : P.FG := Module.Finite.iff_fg.mp inferInstance
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    have : x ∈ P := by rw [← hs]; exact Submodule.subset_span hx
    exact this
  · intro x hx
    have hxP : x ∈ P := hx
    rw [← hs] at hxP
    exact Submodule.span_le_restrictScalars ℤ (𝓞 K) (s : Set V) hxP

end FG

theorem fGOfDisc : FGOfDiscSt := fun _ _ _ _ _ _ _ _ _ Nf M hM => fg_of_unifDiscrete Nf M hM

theorem isLatticeOfDisc : IsLatticeOfDiscSt := fun _ _ _ _ _ _ _ _ _ Nf M hM hsp => ⟨fg_of_unifDiscrete Nf M hM, hsp⟩

end PI.UnitaryGroupMassFormula.TBDisc
