import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo

namespace LeviFormCombination
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviComb

theorem levi_sum_add {e : ℕ} {ι : Type} (s : Finset ι) (a : ι → ℝ) (f : ι → (Fin e → ℂ) → ℝ)
    (g : (Fin e → ℂ) → ℝ) {y : Fin e → ℂ} (hf : ∀ i, ContDiffAt ℝ 2 (f i) y) (hg : ContDiffAt ℝ 2 g y)
    (w : Fin e → ℂ) :
    ContDiffAt ℝ 2 (fun z => ∑ i ∈ s, a i * f i z + g z) y ∧
      levi (fun z => ∑ i ∈ s, a i * f i z + g z) y w = ∑ i ∈ s, a i * levi (f i) y w + levi g y w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert b s hb ih =>
    have he : (fun z => ∑ i ∈ insert b s, a i * f i z + g z) =
        fun z => (∑ i ∈ s, a i * f i z + g z) + a b * f b z := by
      funext z
      rw [Finset.sum_insert hb]
      ring
    rw [he, Finset.sum_insert hb]
    refine ⟨ih.1.add (contDiffAt_const.mul (hf b)), ?_⟩
    rw [levi_add_smul (a b) ih.1 (hf b) w, ih.2]
    ring

theorem leviAt_combPot (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ι : Type) [Fintype ι]
    (P : ι → LocPot X) (a : ι → ℝ) (u : X → ℝ) (hP : ∀ i, IsPotential A (P i)) (hu : A.Smooth u) :
    ∀ j, ∀ y ∈ (A.chart j).target, ∀ w,
      leviAt A (InhabCalc.combPot P a u) j y w = ∑ i, a i * leviAt A (P i) j y w + leviAt A (LocPot.ofFun u) j y w := by
  intro j y hy w
  have hU : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
    ((hu j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm isOpen_univ).mem_nhds ⟨hy, Set.mem_univ _⟩)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hL := (levi_sum_add Finset.univ a
    (fun i => (P i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) (u ∘ (A.chart j).symm)
    (y := y) (fun i => Deg.potential_chart_contDiffAt_two A (hP i) j hy) hU w).2
  exact hL

end GlobalTheory.CompanionTheory.LeviComb

end
end

end LeviFormCombination
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.leviAt_linear_combination_potential : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ι : Type) [Fintype ι] (P : ι → LocPot X) (a : ι → ℝ) (u : X → ℝ), (∀ i, IsPotential A (P i)) → A.Smooth u → ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A (InhabCalc.combPot P a u) j y w = ∑ i, a i * leviAt A (P i) j y w + leviAt A (LocPot.ofFun u) j y w := by
  first | exact @LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.leviAt_combPot | exact LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.leviAt_combPot | (intros; apply LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.leviAt_combPot <;> assumption)

end
