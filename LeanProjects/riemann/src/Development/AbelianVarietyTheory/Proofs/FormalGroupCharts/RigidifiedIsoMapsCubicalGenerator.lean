import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open TopologicalSpace Opposite Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigCub

theorem cover_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i := by
  have h : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 h

theorem div_cover {X : Scheme.{0}} {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) (x : X) :
    ∃ p, x ∈ (LB.div M L).U p := by
  obtain ⟨i, hi⟩ := cover_of_isLB hM x
  obtain ⟨j, hj⟩ := cover_of_isLB hL x
  exact ⟨(i, j), hi, hj⟩

theorem unit_eq_one_of_local {X : Scheme.{0}} {κ : Type} (V : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ V i)
    (v : Γ(X, ⊤)ˣ) (h : ∀ i, res (le_top : V i ≤ ⊤) v = 1) : v = 1 := by
  refine Units.ext ?_
  apply TopCat.Presheaf.section_ext X.sheaf ⊤
  intro x _
  obtain ⟨i, hi⟩ := hcov x
  have e1 := X.presheaf.germ_res_apply (homOfLE (le_top : V i ≤ ⊤)) x hi v.val
  have e3 : (X.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op).hom v.val = 1 := congrArg Units.val (h i)
  rw [e3, map_one] at e1
  exact e1.symm.trans (map_one _).symm

theorem linCombIso_punit {X Y : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) (φ0 : Y ⟶ X)
    (p : (PUnit.{1} → M.ι) × (PUnit.{1} → L.ι)) :
    (LB.linCombIso w (K := PUnit.{1}) (fun _ => φ0) (fun _ => 1)).s p =
      res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit.{1} => φ0) p.1 ⟨⟩))
        (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit.{1} => φ0) p.2 ⟨⟩)))
        (pullU φ0 _ (w.s (p.1 ⟨⟩, p.2 ⟨⟩))) := by
  simp only [LB.linCombIso, zpow_one]
  exact Fintype.prod_subsingleton _ PUnit.unit

section Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rigIso_eq (hGF : GlobalFnsSt) {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S}
    (m : SABMap t' t f) (hab : IsAbelianScheme t'.G) {w w₀ : LB.Iso t'.PP.L (t.PP.L.pull m.φ)}
    (hw : RigIso m w) (hw₀ : w₀.IsGen)
    (hr₀ : LB.Gen.Maps (LB.linCombIso w₀ (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (m.cm.rigPull t.PP.L t.PP.rig)) : w = w₀ := by
  have hLp : (t.PP.L.pull m.φ).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB t.PP.L t.PP.isLB _ _
  obtain ⟨u, hu⟩ := exists_ratio_gen (div_cover hLp t'.PP.isLB) hw.1 hw₀
  suffices hu1 : u = 1 by
    cases w
    cases w₀
    congr 1
    funext p
    exact (hu p).trans (by rw [hu1, map_one, _root_.one_mul])
  apply unit_eq_one_of_eSec hGF t'.G hab u
  have hA : ((t'.PP.L).pull (eSec t'.G)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB t'.PP.L t'.PP.isLB _ _
  have hB : ((t.PP.L.pull m.φ).pull (eSec t'.G)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hLp _ _
  have hloc : ∀ p : ((t.PP.L.pull m.φ).pull (eSec t'.G)).ι × ((t'.PP.L).pull (eSec t'.G)).ι,
      res (le_top : ((t.PP.L.pull m.φ).pull (eSec t'.G)).U p.1 ⊓ ((t'.PP.L).pull (eSec t'.G)).U p.2 ≤ ⊤)
        (pullU (eSec t'.G) ⊤ u : Γ((𝟙_ (Over S')).left, ⊤)ˣ) = 1 := by
    rintro ⟨p1, p2⟩
    have e3 := mul_right_cancel ((hw.2 (p1, p2)).symm.trans (hr₀ (p1, p2)))
    have e3' := (linCombIso_punit w (eSec t'.G) (p1, p2)).symm.trans (e3.trans (linCombIso_punit w₀ (eSec t'.G) (p1, p2)))
    have hu' : ∀ a b, w.s (a, b) = res le_top u * w₀.s (a, b) := fun a b => hu (a, b)
    rw [hu', map_mul] at e3'
    have e5 := mul_right_cancel (((map_mul _ _ _).symm.trans e3').trans (_root_.one_mul _).symm)
    rw [ReciprocityTheory.ChartRestriction.G.DVR.pullU_res] at e5
    exact (ReciprocityTheory.ChartRestriction.G.DVR.res_res' _ _ _).symm.trans e5
  have hv1 := unit_eq_one_of_local _ (fun y => by
      obtain ⟨p1, hp1⟩ := cover_of_isLB hB y
      obtain ⟨p2, hp2⟩ := cover_of_isLB hA y
      exact ⟨(p1, p2), hp1, hp2⟩) (pullU (eSec t'.G) ⊤ u : Γ((𝟙_ (Over S')).left, ⊤)ˣ) hloc
  exact congrArg Units.val hv1

end Rig

theorem rigIso_cub : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → IsAbelianScheme t'.G → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) := by
  intro hGF E _ _ _ H X0 X1 t t' f mp w hw hab
  obtain ⟨w₀, h₀, h₁, h₂⟩ := mp.lin
  rw [rigIso_eq hGF mp hab hw h₀ h₁]
  exact h₂

end GlobalTheory.RigCub
