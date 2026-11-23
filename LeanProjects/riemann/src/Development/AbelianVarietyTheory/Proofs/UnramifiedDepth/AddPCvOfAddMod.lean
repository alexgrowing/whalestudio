import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem nEval_cvAt {Ω A : Type} [Field Ω] [CommRing A] [Algebra Ω A] (s : MvPowerSeries (Fin 2) Ω)
    (hs : MvPowerSeries.constantCoeff s = 0) (f : PowerSeries Ω) (v : Fin 2 → A) (hv : ∀ i, IsNilpotent (v i)) :
    nEval (cvAt s f) v = nEval (σ := Unit) f (fun _ => nEval s v) :=
  ChartCompare.nEval_subst (σ := Unit) (fun _ => s) (fun _ => hs) f v hv

theorem formalAdd_cv_of_addMod :
    ∀ (Ω : Type) [Field Ω] (p d : ℕ) (F : Fin d → PS Ω 2 d) (ga : Fin d → PowerSeries Ω), (∀ j, PowerSeries.constantCoeff (ga j) = 0) → AddMod p F ga → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → addP F (cv ga a) (cv ga a') = cv ga (a + a') := by
  intro Ω _ p d F ga h0 hadd A _ _ a a' ha ha'
  funext i
  have hp : ∀ k : Fin 2, (![a, a'] : Fin 2 → A) k ^ p = 0 := fun k => by
    fin_cases k
    · exact ha
    · exact ha'
  have hv : ∀ k : Fin 2, IsNilpotent ((![a, a'] : Fin 2 → A) k) := fun k => ⟨p, hp k⟩
  have hz : nEval (MvPowerSeries.subst (fun q : Fin 2 × Fin d => cvAt (MvPowerSeries.X q.1) (ga q.2)) (F i) -
      cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (ga i)) (![a, a'] : Fin 2 → A) = 0 := by
    rw [evBasic_nEval_eq_tEval _ _ p hp, evBasic_tEval_eq_sum]
    refine Finset.sum_eq_zero fun e he => ?_
    rw [Fintype.mem_piFinset] at he
    rw [hadd i _ (Finset.mem_range.1 (he 0)) (Finset.mem_range.1 (he 1)), map_zero, zero_mul]
  have hc : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) Ω) (ga q.2)) = 0 := fun q =>
    MvPowerSeries.constantCoeff_subst_eq_zero (a := fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) Ω))
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _)
      (fun _ => MvPowerSeries.constantCoeff_X _) (h0 q.2)
  rw [nEval_sub hv, sub_eq_zero, ChartCompare.nEval_subst _ hc _ _ hv, nEval_cvAt _ (by simp) _ _ hv,
    nEval_add hv, ChartCompare.nEval_X _ hv, ChartCompare.nEval_X _ hv] at hz
  refine Eq.trans ?_ hz
  unfold addP evP
  congr 1
  funext q
  rw [nEval_cvAt _ (MvPowerSeries.constantCoeff_X _) _ _ hv, ChartCompare.nEval_X _ hv]
  obtain ⟨k, j⟩ := q
  fin_cases k <;> rfl

end GlobalTheory.AlphaPair
end
