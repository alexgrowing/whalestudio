import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open Filter Topology

namespace GlobalTheory

theorem limsupExt_upperSemicontinuous (Y : Type) [TopologicalSpace Y] (S : Set Y) (u : Y → ℝ) :
    UpperSemicontinuous (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt S u) := by
  intro y b hb
  obtain ⟨c, hc, hcb⟩ := exists_between hb
  have hev : ∀ᶠ y' in 𝓝[S] y, (u y' : EReal) < c :=
    Filter.eventually_lt_of_limsup_lt hc
  obtain ⟨O, hOy, hO⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
  obtain ⟨O', hO'O, hO'open, hyO'⟩ := mem_nhds_iff.mp hOy
  filter_upwards [hO'open.mem_nhds hyO'] with y'' hy''
  have h2 : ∀ᶠ y' in 𝓝[S] y'', (u y' : EReal) ≤ c := by
    have : S ∩ O ∈ 𝓝[S] y'' :=
      inter_mem_nhdsWithin S (mem_of_superset (hO'open.mem_nhds hy'') hO'O)
    filter_upwards [this] with z hz using (hO ⟨hz.2, hz.1⟩).le
  have : GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt S u y'' ≤ c := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt
    exact Filter.limsup_le_of_le (by isBoundedDefault) h2
  exact lt_of_le_of_lt this hcb

theorem limsupExt_usc_all : ∀ (Y : Type) [TopologicalSpace Y] (S : Set Y) (u : Y → ℝ),
    UpperSemicontinuous (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt S u) :=
  fun Y _ S u => limsupExt_upperSemicontinuous Y S u

end GlobalTheory
