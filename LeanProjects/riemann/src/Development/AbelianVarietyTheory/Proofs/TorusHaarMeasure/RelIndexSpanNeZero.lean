import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SpanIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.SpanIndex.relIndex_span_ne_zero : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) ≠ 0) := by
  classical
  intro r X ι _ _ w _ hw
  set V := Submodule.span E (Set.range w)
  set N := Submodule.span (𝓞 E) (Set.range w)
  set M : Submodule (𝓞 E) (Fin r → E) := X.Λ ⊓ V.restrictScalars (𝓞 E)
  have hK : X.Λ.toAddSubgroup ⊓ V.toAddSubgroup = M.toAddSubgroup := rfl
  rw [hK]
  have hMfg : M.FG := by
    haveI : IsNoetherian (𝓞 E) X.Λ := isNoetherian_of_fg_of_noetherian X.Λ X.Λ_fg
    exact Submodule.FG.of_le_of_isNoetherian inf_le_left
  haveI : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.mpr hMfg
  haveI : Module.Finite ℤ (M ⧸ N.comap M.subtype) := Module.Finite.trans (𝓞 E) _
  have htors : Module.IsTorsion ℤ (M ⧸ N.comap M.subtype) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨v, hv⟩ := x
      have hvV : v ∈ V := (Submodule.mem_inf.mp hv).2
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hvV
      obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
      refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap]
      have hint : ∀ a, IsIntegral ℤ (y • c a) := fun a =>
        hy _ (Finset.mem_image_of_mem c (Finset.mem_univ a))
      have hsum : y • v = ∑ a, (⟨y • c a, hint a⟩ : 𝓞 E) • w a := by
        rw [← hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ext i
        change _ = ((⟨y • c a, hint a⟩ : 𝓞 E) : E) * w a i
        simp [zsmul_eq_mul, mul_assoc]
      change y • v ∈ N
      rw [hsum]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  haveI : Finite (M ⧸ N.comap M.subtype) := Module.finite_of_fg_torsion _ htors
  exact AddSubgroup.index_ne_zero_of_finite (hH := this)

end GlobalTheory.SpanIndex
