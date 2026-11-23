import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm

noncomputable section

namespace GlobalTheory.ArcPts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

section
variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {T : ℝ} (hT : A.IsConvLine T) {j : ℕ} [NeZero j]
include hT

theorem fsum_mem_halfRing {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (v : A.V) :
    ∃ hm : A.FSum j α th v ∈ Conv.halfRing T, ∀ w hw, Conv.ev T w hw ⟨_, hm⟩ = A.Sum j α th w v :=
  ⟨fun _ hw => (AnArc.hasSum_coeff_FSum hT h hw v).summable,
    fun _ hw => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_coeff_FSum hT h hw v)⟩

theorem exists_dfsum_halfRing {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (z₀ : A.V) :
    ∃ F : Conv.halfRing T, IsDFSum A j α th z₀ F ∧
      ∀ w hw, Conv.ev T w hw F = fderiv ℂ (A.Sum j α th w) 0 z₀ := by
  let S : ℂ⸨X⸩ := HahnSeries.ofSuppBddBelow (fun n => fderiv ℂ (fun v => (A.FSum j α th v).coeff n) 0 z₀)
    ⟨-A.be α α, fun n hn => by
      by_contra hlt
      exact hn (by simp only [AnArc.fderiv_coeff_FSum_eq_zero (not_le.1 hlt), ContinuousLinearMap.zero_apply])⟩
  exact ⟨⟨S, fun _ hw => (AnArc.hasSum_fderiv_coeff_FSum hT h hw 0 z₀).summable⟩, fun _ => rfl,
    fun _ hw => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_fderiv_coeff_FSum hT h hw 0 z₀)⟩

theorem differentiable_ev_comb (f : A.V → Conv.halfRing T) (hf : IsComb A j (Conv.halfRing T) (fun v => f v))
    (w : ℂ) (hw : T < w.im) : Differentiable ℂ (fun v => Conv.ev T w hw (f v)) := by
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  have key : (fun v => Conv.ev T w hw (f v)) =
      fun v => ∑ i, Conv.ev T w hw ⟨r i, (h1 i).1⟩ * A.Sum j (α i) (th i) w v := by
    funext v
    choose hm hv using fun i => fsum_mem_halfRing hT (h1 i).2 v
    have e : f v = ∑ i, (⟨r i, (h1 i).1⟩ : Conv.halfRing T) * ⟨_, hm i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      exact h2 v
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv i w hw]
  rw [key]
  exact Differentiable.fun_sum fun i _ =>
    (AnArc.differentiable_Sum hT (NeZero.ne j) (h1 i).2 hw).const_mul _

end

theorem exists_formal_convergence : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (j : ℕ) [NeZero j], (∀ α, ∀ th ∈ A.Theta j α, (∀ v, ∃ h : A.FSum j α th v ∈ Conv.halfRing T, ∀ w hw, Conv.ev T w hw ⟨_, h⟩ = A.Sum j α th w v) ∧ ∀ z₀, ∃ F : Conv.halfRing T, IsDFSum A j α th z₀ F ∧ ∀ w hw, Conv.ev T w hw F = fderiv ℂ (A.Sum j α th w) 0 z₀) ∧ ∀ f : A.V → Conv.halfRing T, IsComb A j (Conv.halfRing T) (fun v => f v) → ∀ w hw, Differentiable ℂ (fun v => Conv.ev T w hw (f v)) := by
  intro O _ _ A
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  refine ⟨T₀, fun T hT j _ => ?_⟩
  have h := h₀.mono hT
  exact ⟨fun α th hth => ⟨fsum_mem_halfRing h hth, exists_dfsum_halfRing h hth⟩, differentiable_ev_comb h⟩

end GlobalTheory.ArcPts
