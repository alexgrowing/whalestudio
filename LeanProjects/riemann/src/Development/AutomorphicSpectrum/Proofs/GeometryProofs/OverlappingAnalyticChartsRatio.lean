import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare

theorem eq_val_mul : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U U' : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T T' : Ω) (d d' : ℕ) (B : Set (Fin d → ℂ)) (B' : Set (Fin d' → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (Y' : (Fin d' → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) (H' : (Fin d' → ℂ) → ℂ) (b₁ : Fin d → ℂ) (b₂ : Fin d' → ℂ) (r : ℂ), IsCptGen ξ → HChart s ξ W U F T B Y H → HChart s ξ W U' F T' B' Y' H' → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U → q ∈ W → unitAt ξ ⟨q, hq⟩ T) → (∀ (q : X) (hq : genPt ξ ⤳ q), q ∈ U' → q ∈ W → unitAt ξ ⟨q, hq⟩ T') → b₁ ∈ B → b₂ ∈ B' → Y b₁ = Y' b₂ → ValAt ξ (Y b₁) (T' / T) r → H b₁ = r * H' b₂ := by
  intro X s Ω _ ξ W U U' F T T' d d' B B' Y Y' H H' b₁ b₂ r hξ hC hC' hT hT' hb₁ hb₂ hY hval
  obtain ⟨hsp, st, hst1, -⟩ := id hval
  have hreg : T' / T ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre (Y b₁), hsp⟩ := by
    unfold GlobalTheory.CompanionTheory.Ar.regAt
    exact RingHom.mem_range.mpr ⟨st, hst1⟩
  obtain ⟨N, hqN, v, -, hv⟩ := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_section hsp hreg ⊤ (by simp)
  have hgN : GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ N := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genPt_mem hsp hqN
  have hvg : GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genV ξ N hgN v = T' / T := by
    rw [← GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genMap_germ N hsp hqN hgN v]
    exact hv
  have hvalg : ∀ b ∈ B, ∀ hbN : GlobalTheory.CompanionTheory.Ar.centre (Y b) ∈ N,
      GlobalTheory.CompanionTheory.Ar.ValAt ξ (Y b) (T' / T) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v) := by
    intro b hb hbN
    apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.of_section hbN (hC.cpt b hb)
    rw [GlobalTheory.CompanionTheory.Ar.Flat.GagaC.genMap_germ N (hC.cpt b hb) hbN hgN v]
    exact hvg
  have hr : ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b₁) N v = r :=
    GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.unique hξ (hvalg b₁ hb₁ hqN) hval
  obtain ⟨ε, κ, hε, -, hκd, hκ1, hκ⟩ :=
    hC'.chart.factor d B Y hC.chart.isOpen hC.chart.hol hC.chart.isOver b₁ hb₁ b₂ hb₂ hY
  obtain ⟨hOopen, hgd⟩ := hC.chart.hol N v
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Fin d → ℂ),
      S = {b | b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (Y b).base).obj N} := ⟨_, rfl⟩
  have hmemS : ∀ b, b ∈ S ↔ b ∈ B ∧ GlobalTheory.CompanionTheory.Ar.centre (Y b) ∈ N := by
    intro b
    rw [hSdef, Set.mem_ofPred_eq, GlobalTheory.CompanionTheory.Ar.Flat.GagaC.top_le_iff_centre]
  have hSo : IsOpen S := by
    rw [hSdef]
    exact hOopen
  have hSg : DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v) S := by
    rw [hSdef]
    exact hgd
  have hOo : IsOpen (S ∩ Metric.ball b₁ ε) := hSo.inter Metric.isOpen_ball
  have h1 : ContinuousOn H (S ∩ Metric.ball b₁ ε) :=
    (hC.hol.mono fun b hb => ((hmemS b).mp hb.1).1).continuousOn
  have h2 : ContinuousOn (fun b => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v) (S ∩ Metric.ball b₁ ε) :=
    (hSg.mono fun b hb => hb.1).continuousOn
  have h3 : ContinuousOn (fun b => H' (κ b)) (S ∩ Metric.ball b₁ ε) := by
    have hc : DifferentiableOn ℂ (H' ∘ κ) (Metric.ball b₁ ε) :=
      hC'.hol.comp hκd (fun b hb => (hκ b hb).1)
    exact (hc.mono fun b hb => hb.2).continuousOn
  have hcont : ContinuousOn (fun b => H b - ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v * H' (κ b))
      (S ∩ Metric.ball b₁ ε) := h1.sub (h2.mul h3)
  have hzero : ∀ b ∈ S ∩ Metric.ball b₁ ε, GlobalTheory.CompanionTheory.Ar.centre (Y b) ∈ W →
      H b - ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v * H' (κ b) = 0 := by
    intro b hbO hbW
    obtain ⟨hbB, hbN⟩ := (hmemS b).mp hbO.1
    obtain ⟨hκB, hYκ⟩ := hκ b hbO.2
    have hcb := hC.cpt b hbB
    have hTu := hT (GlobalTheory.CompanionTheory.Ar.centre (Y b)) hcb (hC.inU b hbB) hbW
    obtain ⟨r₁, hr₁, e₁⟩ := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.exists_ne_zero hξ hcb hTu
    have hcb' := hC'.cpt (κ b) hκB
    have hW' : GlobalTheory.CompanionTheory.Ar.centre (Y' (κ b)) ∈ W := by
      rw [← hYκ]
      exact hbW
    have hT'u := hT' (GlobalTheory.CompanionTheory.Ar.centre (Y' (κ b))) hcb' (hC'.inU (κ b) hκB) hW'
    obtain ⟨r₂, -, e₂⟩ := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.exists_ne_zero hξ hcb' hT'u
    have f₁ := hC.rel b hbB hbW r₁ e₁
    have f₂ := hC'.rel (κ b) hκB hW' r₂ e₂
    have hm := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.mul (hvalg b hbB hbN) e₁
    have hTT : T' / T * T = T' := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self hTu.1, _root_.mul_one]
    rw [hTT] at hm
    have e₂' : GlobalTheory.CompanionTheory.Ar.ValAt ξ (Y b) T' r₂ := by
      rw [hYκ]
      exact e₂
    have hu := GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ValAt.unique hξ hm e₂'
    rw [hYκ] at f₁
    rw [f₁, ← hu] at f₂
    have hH : H b = ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b) N v * H' (κ b) := by
      apply mul_right_cancel₀ hr₁
      rw [f₂]
      ring
    rw [hH, sub_self]
  have hb1O : b₁ ∈ S ∩ Metric.ball b₁ ε := ⟨(hmemS b₁).mpr ⟨hb₁, hqN⟩, Metric.mem_ball_self hε⟩
  have hφ : H b₁ - ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (Y b₁) N v * H' (κ b₁) = 0 := by
    by_contra hne
    have hopen := hcont.isOpen_inter_preimage hOo (isOpen_compl_singleton (x := (0 : ℂ)))
    obtain ⟨b, hb, hbW⟩ := hC.dense _ hopen (fun b hb => ((hmemS b).mp hb.1.1).1) ⟨b₁, hb1O, hne⟩
    exact hb.2 (hzero b hb.1 hbW)
  rw [hr, hκ1] at hφ
  exact sub_eq_zero.mp hφ

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Compare
