import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FBDescent

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FBMap

variable {R k : Type} [CommRing R] [CommRing k] {f : R →+* k} {d : ℕ}

theorem map_inj (hf : Function.Injective f) {σ : Type} {a b : MvPowerSeries σ R}
    (h : MvPowerSeries.map f a = MvPowerSeries.map f b) : a = b := by
  ext m
  apply hf
  have := congrArg (coeff m) h
  simpa only [coeff_map] using this

theorem mapPt_inj (hf : Function.Injective f) {n : ℕ} {a b : Pt R n d}
    (h : mapPt f a = mapPt f b) : a = b :=
  funext fun i => map_inj hf (congrFun h i)

theorem nc_of_map (hf : Function.Injective f) {n : ℕ} {a : Pt R n d} (h : NoConst (mapPt f a)) :
    NoConst a := fun i => by
  apply hf
  have := h i
  rw [mapPt, MvPowerSeries.constantCoeff_map] at this
  rw [this, map_zero]

local macro "no_const" : tactic =>
  `(tactic| repeat' first
    | exact nc_zero
    | exact nc_pt _
    | exact nc_law _
    | exact nc_act _ _
    | assumption
    | apply nc_comp1
    | apply nc_addOf)

local macro "push_map" : tactic =>
  `(tactic| simp (disch := no_const) only [map_mul, map_one, map_ev1, map_ev2, map_ev3,
    mapPt_zero, mapPt_pt, mapPt_comp1, mapPt_addOf, FGLaw.add])

theorem exists_law (hf : Function.Injective f) (G : FGLaw k d) (F : Pt R 2 d) (hF : G.F = mapPt f F) :
    ∃ G' : FGLaw R d, G'.F = F := by
  have c : NoConst F := nc_of_map hf (hF ▸ nc_law G)
  refine ⟨⟨F, c, fun i => ?_, fun i => ?_, fun i => ?_⟩, rfl⟩
  · have h := G.unit i
    rw [hF] at h
    apply map_inj hf
    rw [map_X]
    push_map
    exact h
  · have h := G.comm i
    rw [hF] at h
    apply map_inj hf
    push_map
    exact h
  · have h := G.assoc i
    rw [hF] at h
    change ev (n := 3) ![addOf F (pt R d 0) (pt R d 1), pt R d 2] (F i) =
        ev (n := 3) ![pt R d 0, addOf F (pt R d 1) (pt R d 2)] (F i)
    apply map_inj hf
    push_map
    exact h

variable {O : Type} [CommRing O]

theorem exists_act (hf : Function.Injective f) {G : FGLaw k d} (A : OAct O G) (G' : FGLaw R d)
    (hF : G.F = mapPt f G'.F) (act : O → Pt R 1 d) (hA : ∀ a, A.act a = mapPt f (act a)) :
    ∃ A' : OAct O G', A'.act = act := by
  have c : ∀ a, NoConst (act a) := fun a => nc_of_map hf (hA a ▸ nc_act A a)
  refine ⟨⟨act, c, fun a => ?_, fun a b => ?_, fun a b => ?_, ?_⟩, rfl⟩
  · have h := A.hom a
    have ca := c a
    simp only [FGLaw.add, hF, hA] at h
    apply mapPt_inj hf
    push_map
    exact h
  · have h := A.add_act a b
    have ca := c a
    have cb := c b
    simp only [FGLaw.add, hF, hA] at h
    apply mapPt_inj hf
    push_map
    exact h
  · have h := A.mul_act a b
    have ca := c a
    have cb := c b
    simp only [hA] at h
    apply mapPt_inj hf
    push_map
    exact h
  · have h := A.one_act
    simp only [hA] at h
    apply mapPt_inj hf
    push_map
    exact h

def descFB [StarRing O] (hf : Function.Injective f) (B : FB k d O) (G' : FGLaw R d) (A' : OAct O G')
    (ph1 ph2 : PS R 3 d) (sy : PS R 2 d) (ad : O → PS R 2 d)
    (hF : B.G.F = mapPt f G'.F) (hA : ∀ a, B.A.act a = mapPt f (A'.act a))
    (h1 : B.ph1 = MvPowerSeries.map f ph1) (h2 : B.ph2 = MvPowerSeries.map f ph2)
    (hs : B.sy = MvPowerSeries.map f sy) (ha : ∀ a, B.ad a = MvPowerSeries.map f (ad a)) : FB R d O where
  G := G'
  A := A'
  ph1 := ph1
  ph2 := ph2
  sy := sy
  ad := ad
  cocycleLeft_zero_fst := by
    have h := B.cocycleLeft_zero_fst
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  cocycleLeft_zero_snd := by
    have h := B.cocycleLeft_zero_snd
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  cocycleLeft_zero_thd := by
    have h := B.cocycleLeft_zero_thd
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  cocycleRight_zero_fst := by
    have h := B.cocycleRight_zero_fst
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  cocycleRight_zero_snd := by
    have h := B.cocycleRight_zero_snd
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  cocycleRight_zero_thd := by
    have h := B.cocycleRight_zero_thd
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  symmetry_zero_fst := by
    have h := B.symmetry_zero_fst
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  symmetry_zero_snd := by
    have h := B.symmetry_zero_snd
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  adjoint_zero_fst a := by
    have h := B.adjoint_zero_fst a
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  adjoint_zero_snd a := by
    have h := B.adjoint_zero_snd a
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  cocycleLeft_assoc := by
    have h := B.cocycleLeft_assoc
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  cocycleLeft_comm := by
    have h := B.cocycleLeft_comm
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  cocycleRight_assoc := by
    have h := B.cocycleRight_assoc
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  cocycleRight_comm := by
    have h := B.cocycleRight_comm
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  interchange := by
    have h := B.interchange
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  sy_inv := by
    have h := B.sy_inv
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  sy_law := by
    have h := B.sy_law
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  adjoint_compat_left a := by
    have h := B.adjoint_compat_left a
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  adjoint_compat_right a := by
    have h := B.adjoint_compat_right a
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  ad_one := by
    have h := B.ad_one
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  ad_mul a b := by
    have h := B.ad_mul a b
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  ad_add a b := by
    have h := B.ad_add a b
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h
  ad_sy a := by
    have h := B.ad_sy a
    simp only [FGLaw.add, hF, hA, h1, h2, hs, ha] at h
    apply map_inj hf
    push_map
    exact h

theorem exists_fb [StarRing O] (hf : Function.Injective f) (B : FB k d O)
    (F : Pt R 2 d) (act : O → Pt R 1 d) (ph1 ph2 : PS R 3 d) (sy : PS R 2 d) (ad : O → PS R 2 d)
    (hF : ∀ j, B.G.F j = MvPowerSeries.map f (F j))
    (hA : ∀ a j, B.A.act a j = MvPowerSeries.map f (act a j))
    (h1 : B.ph1 = MvPowerSeries.map f ph1) (h2 : B.ph2 = MvPowerSeries.map f ph2)
    (hs : B.sy = MvPowerSeries.map f sy) (ha : ∀ a, B.ad a = MvPowerSeries.map f (ad a)) :
    ∃ B' : FB R d O, B'.G.F = F ∧ B'.A.act = act ∧ B'.ph1 = ph1 ∧ B'.ph2 = ph2 ∧ B'.sy = sy ∧ B'.ad = ad := by
  obtain ⟨G', rfl⟩ := exists_law hf B.G F (funext hF)
  obtain ⟨A', rfl⟩ := exists_act hf B.A G' (funext hF) act (fun a => funext (hA a))
  exact ⟨descFB hf B G' A' ph1 ph2 sy ad (funext hF) (fun a => funext (hA a)) h1 h2 hs ha,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem map_tower {F : Type} [CommRing F] [Algebra R k] [Algebra k F] [Algebra R F] [IsScalarTower R k F]
    {σ : Type} (g : MvPowerSeries σ R) :
    MvPowerSeries.map (algebraMap R F) g =
      MvPowerSeries.map (algebraMap k F) (MvPowerSeries.map (algebraMap R k) g) := by
  ext m
  simp only [coeff_map]
  exact IsScalarTower.algebraMap_apply R k F _

theorem gauge_iff [StarRing O] (B' : FB R d O) (B : FB k d O) (F : Type) [CommRing F] [Algebra ℚ F]
    [Algebra R F] [Algebra k F] (hF : B'.FK F = B.FK F) (hA : ∀ a, B'.actK F a = B.actK F a)
    (h1 : FB.toK F B'.ph1 = FB.toK F B.ph1) (h2 : FB.toK F B'.ph2 = FB.toK F B.ph2)
    (hs : FB.toK F B'.sy = FB.toK F B.sy) (ha : ∀ a, FB.toK F (B'.ad a) = FB.toK F (B.ad a))
    (h : PS F 2 d) : B'.IsCanonGauge F h ↔ B.IsCanonGauge F h := by
  constructor
  · intro H
    refine ⟨H.ax0, H.ax1, ?_, ?_, ?_, fun a => ?_⟩
    · rw [← h1, ← hF]; exact H.ph1
    · rw [← h2, ← hF]; exact H.ph2
    · rw [← hs]; exact H.sy
    · rw [← ha, ← hA, ← hA]; exact H.ad a
  · intro H
    refine ⟨H.ax0, H.ax1, ?_, ?_, ?_, fun a => ?_⟩
    · rw [h1, hF]; exact H.ph1
    · rw [h2, hF]; exact H.ph2
    · rw [hs]; exact H.sy
    · rw [ha, hA, hA]; exact H.ad a

theorem exists_fb_gauge [StarRing O] [Algebra R k] [Algebra ℚ k] (hf : Function.Injective (algebraMap R k))
    (B : FB k d O) (h0 : PS k 2 d) (H0 : B.IsCanonGauge k h0)
    (G : Pt R 2 d) (act : O → Pt R 1 d) (ph1 ph2 : PS R 3 d) (sy : PS R 2 d) (ad : O → PS R 2 d)
    (hF : ∀ j, B.G.F j = MvPowerSeries.map (algebraMap R k) (G j))
    (hA : ∀ a j, B.A.act a j = MvPowerSeries.map (algebraMap R k) (act a j))
    (h1 : B.ph1 = MvPowerSeries.map (algebraMap R k) ph1) (h2 : B.ph2 = MvPowerSeries.map (algebraMap R k) ph2)
    (hs : B.sy = MvPowerSeries.map (algebraMap R k) sy)
    (ha : ∀ a, B.ad a = MvPowerSeries.map (algebraMap R k) (ad a)) :
    ∃ B' : FB R d O, B'.G.F = G ∧ B'.A.act = act ∧ B'.ph1 = ph1 ∧ B'.ph2 = ph2 ∧ B'.sy = sy ∧ B'.ad = ad ∧
      ∀ (F : Type) [CommRing F] [Algebra ℚ F] [Algebra k F] [Algebra R F] [IsScalarTower R k F],
        B'.FK F = B.FK F ∧ (∀ a, B'.actK F a = B.actK F a) ∧
        (∀ h, B'.IsCanonGauge F h ↔ B.IsCanonGauge F h) ∧
        B.IsCanonGauge F (MvPowerSeries.map (algebraMap k F) h0) := by
  obtain ⟨B', rfl, rfl, rfl, rfl, rfl, rfl⟩ := exists_fb hf B G act ph1 ph2 sy ad hF hA h1 h2 hs ha
  refine ⟨B', rfl, rfl, rfl, rfl, rfl, rfl, fun F _ _ _ _ _ => ?_⟩
  have eF : B'.FK F = B.FK F := by
    funext i
    change MvPowerSeries.map _ (B'.G.F i) = MvPowerSeries.map _ (B.G.F i)
    rw [hF, ← map_tower]
  have eA : ∀ a, B'.actK F a = B.actK F a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B'.A.act a i) = MvPowerSeries.map _ (B.A.act a i)
    rw [hA, ← map_tower]
  refine ⟨eF, eA, gauge_iff B' B F eF eA ?_ ?_ ?_ (fun a => ?_), ?_⟩
  · rw [h1]; exact map_tower _
  · rw [h2]; exact map_tower _
  · rw [hs]; exact map_tower _
  · rw [ha]; exact map_tower _
  · exact GaugeBaseChange.isCanonGauge_map B (Algebra.ofId k F) H0

end GlobalTheory.FBDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem integralChart_formalBiext : IntFBSt := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C
  letI := io.toAlgebra
  obtain ⟨hF, hA, h1, h2, hs, ha, -⟩ := C.gen.1
  obtain ⟨B', e1, e2, e3, e4, e5, e6, e7⟩ :=
    FBDescent.exists_fb_gauge (IsFractionRing.injective T.V T.Fr) C.ch.B C.ch.h C.ch.gauge
      C.FT C.actT C.ph1T C.ph2T C.syT C.adT hF hA h1 h2 hs ha
  exact ⟨B', e1, e2, e3, e4, e5, e6, fun F _ _ _ _ _ => e7 F⟩

end GlobalTheory
