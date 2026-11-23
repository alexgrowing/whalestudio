import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TopTheta
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacCore
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ClmCircleIntegral
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem roots_bound (d : Polynomial ℂ) (hd : d ≠ 0) : ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → d.eval z ≠ 0 := by
  refine ⟨∑ r ∈ d.roots.toFinset, |r.re|, fun z hz h0 => ?_⟩
  have hm : z ∈ d.roots.toFinset := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr h0)
  have h1 : |z.re| ≤ ∑ r ∈ d.roots.toFinset, |r.re| :=
    Finset.single_le_sum (f := fun r : ℂ => |r.re|) (fun r _ => abs_nonneg _) hm
  linarith [le_abs_self z.re]

theorem top_E [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (hD : CayleyBlocksInvertible)
    (hHP : HolParam) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} (hnbc : Continuous nb)
    {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {cz : ℂ → ℂ}
    (hczd : Differentiable ℂ cz)
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G → ℂ} {σ : ℝ} (hUo : IsOpen U) (hUr : GlobalTheory.Cont.IsRightDomain U)
    (hd : d ≠ 0) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ))
    (hEr : ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
        ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g q‖ ≤ u q) ∧
      ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g) :
    ∀ z ∈ U, ∀ g, Top μ ι p q e a b nb ψ (E z) g = cz (z - s₀) * E z g := by
  have hsm : ∀ (c : ℂ) (F : G → ℂ) (g : G),
      Top μ ι p q e a b nb ψ (fun x => c * F x) g = c * Top μ ι p q e a b nb ψ F g := by
    intro c F g
    simp only [Top, mul_assoc c]
    simp_rw [integral_const_mul, mul_left_comm _ c, integral_const_mul]
  intro z hzU g
  have hdiff : DifferentiableOn ℂ
      (fun w => Top μ ι p q e a b nb ψ (E w) g - cz (w - s₀) * E w g) U := by
    have h1 : DifferentiableOn ℂ (fun w => Top μ ι p q e a b nb ψ (E w) g) U :=
      top_hol (p := p) (q := q) (e := e) (a := a) (b := b) μ hD hHP hG.ιcont hnbc hψc hψs hUo E hEc hEh g
    have h2 : DifferentiableOn ℂ (fun w => cz (w - s₀)) U :=
      (hczd.comp (differentiable_id.sub_const s₀)).differentiableOn
    exact h1.sub (h2.mul (hEh g))
  have hVo : IsOpen (connectedComponentIn U z) := hUo.connectedComponentIn
  have hVU : connectedComponentIn U z ⊆ U := connectedComponentIn_subset U z
  have han := (hdiff.mono hVU).analyticOnNhd hVo
  have hray : (fun t : ℝ => z + (t : ℂ)) '' Ici 0 ⊆ connectedComponentIn U z := by
    apply IsPreconnected.subset_connectedComponentIn
    · exact isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => z + (t : ℂ)).continuousOn
    · exact ⟨0, Set.mem_Ici.mpr le_rfl, by simp⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hUr.2 z hzU t ht
  have hT : (0 : ℝ) ≤ max 0 (σ - z.re) + 1 := by
    have := le_max_left 0 (σ - z.re)
    linarith
  have hw0 : z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ) ∈ connectedComponentIn U z := hray ⟨_, hT, rfl⟩
  have hre : σ < (z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ)).re := by
    have := le_max_right 0 (σ - z.re)
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hev : (fun w => Top μ ι p q e a b nb ψ (E w) g - cz (w - s₀) * E w g)
      =ᶠ[𝓝 (z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ))] 0 := by
    have hopen : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hre] with w hw
    have hEw : E w = fun x => d.eval w * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w) x :=
      funext fun x => (hEr w hw).2 x
    have hs := top_sum μ hL hG hD hG.ιcont hnbc hψc hψs hceig w (hEr w hw).1 g
    simp only [Pi.zero_apply]
    rw [hEw, hsm (d.eval w) (fun x => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w) x), hs]
    ring
  have h := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
    hw0 hev (mem_connectedComponentIn hzU)
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.mp h

end PositivityTheory.Rg.Sw.AbsSt.Vac
