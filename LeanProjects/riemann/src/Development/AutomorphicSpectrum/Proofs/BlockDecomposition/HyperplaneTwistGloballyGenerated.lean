import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.CompanionTheory.SerreBpf

open GlobalTheory.QCoh GlobalTheory.Twist CechPic GlobalTheory.LB in

theorem eventually_basePointFree (Y : Var ℂ) (i : Fin (Y.N + 1))
    (hi : Y.ι (genericPoint Y.X) ∈ ProjSpace.chart ℂ Y.N i) (Δ : Y.Dv) :
    ∀ᶠ m : ℕ in Filter.atTop, ∃ (L : LB Y.X) (r : L.ι → Y.Fnˣ) (n : ℕ) (b : Fin n → L.Sec),
      L.IsLB ∧ Presents (Δ + m • Y.hyp hi) L r ∧ ⨆ j, nonzeroLocus (b j) = ⊤ := by
  have hA : GlobalTheory.IsAmpleLB Y.O1 := Y.isAmple_projective_O_one
  have hK : (GlobalTheory.Cartier.toLB (-Δ)).IsLB := GlobalTheory.Cartier.isLB_toLB _
  have hL0 : (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))).IsLB := GlobalTheory.CechPic.isLB_dual hK
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL0
  haveI := GlobalTheory.LB.isFiniteType_toMod hL0
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))) :=
    GlobalTheory.QCoh.IsFiniteQC.of_isFiniteType
  filter_upwards [hA.eventually_isGloballyGenerated_twist
    (GlobalTheory.LB.toMod (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))))] with m hm
  have hM : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb Y.isLineBundle_twistingSheafOne _ _
  have hN : (GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi)).IsLB := GlobalTheory.Cartier.isLB_toLB _
  have h1 : GlobalTheory.QCoh.IsGloballyGenerated
      (GlobalTheory.twist (GlobalTheory.twist (GlobalTheory.LB.unitMod Y.X) (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ))))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)) := by
    haveI : Epi (GlobalTheory.Twist.map (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
        (GlobalTheory.Twist.unitTwistIso (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))).inv) :=
      (GlobalTheory.Twist.epi_map_iff hM _).2 inferInstance
    exact hm.of_epi (GlobalTheory.Twist.map (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
      (GlobalTheory.Twist.unitTwistIso (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))).inv)
  have hiso : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow Y.O1 m)
      ((GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi)).div (GlobalTheory.CechPic.dual (GlobalTheory.Cartier.toLB (-Δ)))) := by
    rw [← GlobalTheory.CechPic.tens_eq_div, ← GlobalTheory.CechPic.cls_eq_iff hM (GlobalTheory.CechPic.isLB_tens hN hK),
      GlobalTheory.CechPic.cls_tens hN hK, GlobalTheory.CechPic.cls_lbPow Y.isLineBundle_twistingSheafOne, ← GlobalTheory.Cartier.toPic_apply,
      ← GlobalTheory.Cartier.toPic_apply, ← (Y.presents_hyp hi).toPic_eq, map_add, map_neg, map_nsmul]
    abel
  obtain ⟨e⟩ := GlobalTheory.Twist.nonempty_twistTwistIso (F := GlobalTheory.LB.unitMod Y.X) hL0 hM hN hiso
  have h2 : GlobalTheory.QCoh.IsGloballyGenerated (GlobalTheory.LB.toMod (GlobalTheory.Cartier.toLB (Δ + m • Y.hyp hi))) :=
    (GlobalTheory.QCoh.isGloballyGenerated_iff_of_iso (e ≪≫ GlobalTheory.Twist.unitTwistIso _)).1 h1
  obtain ⟨n, s, hs⟩ := ((GlobalTheory.isGloballyGenerated_toMod_iff hN).1 h2).exists_fin_succ
  exact ⟨_, _, n + 1, s, hN, GlobalTheory.Cartier.presents_toLB _, hs⟩

end GlobalTheory.CompanionTheory.SerreBpf
