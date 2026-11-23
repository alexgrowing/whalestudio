import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrS
import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrRP
import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrEF
import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPlB
import Formalism.LocalToGlobal.CharacterGerms.RowTiePEmbIntSt

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds CharacteristicFromRanks ValuationFitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section RR

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem isUnit_RR {x : V.RR} (hx : V.v (x : C) = 0) : IsUnit x := by
  have hx0 : (x : C) ≠ 0 := by
    intro h
    rw [h, V.v.map_zero] at hx
    exact WithTop.top_ne_zero hx
  have hi : V.Ge 0 ((x : C)⁻¹) := by
    have h1 : V.v ((x : C) * (x : C)⁻¹) = 0 := by rw [mul_inv_cancel₀ hx0, V.v.map_one]
    rw [V.v.map_mul, hx, zero_add] at h1
    unfold VF.Ge
    rw [h1]
    rfl
  exact IsUnit.of_mul_eq_one (⟨(x : C)⁻¹, hi⟩ : V.RR) (Subtype.ext (mul_inv_cancel₀ hx0))

theorem v_of_isUnit_RR {x : V.RR} (hx : IsUnit x) : V.v (x : C) = 0 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h1 : V.v ((x : C) * (y : C)) = 0 := by
    have : (x : C) * (y : C) = 1 := congrArg Subtype.val hy
    rw [this, V.v.map_one]
  rw [V.v.map_mul] at h1
  have hx0 : (0 : WithTop ℝ) ≤ V.v (x : C) := x.2
  have hy0 : (0 : WithTop ℝ) ≤ V.v (y : C) := y.2
  exact le_antisymm (by calc V.v (x : C) ≤ V.v (x : C) + V.v (y : C) := le_add_of_nonneg_right hy0
                          _ = 0 := h1) hx0

theorem not_isUnit_l {T : Type} [CommRing T] (i0 : T →+* C) (hint : ∀ t, V.Ge 0 (i0 t)) :
    ¬ IsUnit ((V.l : ℕ) : T) := by
  intro h
  have h1 := v_of_isUnit_RR (h.map (i0.codRestrict V.RR hint))
  have h2 : (((i0.codRestrict V.RR hint) ((V.l : ℕ) : T) : V.RR) : C) = (V.l : C) := map_natCast i0 _
  rw [h2, V.v_l] at h1
  exact one_ne_zero h1

theorem upChar_of_upFLaw_RR [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (hPlace : Pl.PlaceCriterionOfIdempotent)
    (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp) (Hc : ∀ g, (Y.raw p).CartHyp V g)
    (T : Type) [CommRing T] (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hL : UpFLaw V.l T OE dd FT actT)
    (i0 : T →+* C) (hint : ∀ t, V.Ge 0 (i0 t)) (hloc : ∀ t, V.v (i0 t) = 0 → IsUnit t)
    (hF : ∀ i, Y.B.G.F i = MvPowerSeries.map i0 (FT i))
    (hact : ∀ a i, Y.B.A.act a i = MvPowerSeries.map i0 (actT a i))
    (hdisc : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) : UPCharSt Y p Hc := by
  obtain ⟨P⟩ := ringPkSt_holds C V Y.cpl
  let _ := P.loc
  let _ := P.alg
  have : Fact ¬IsUnit ((V.l : ℕ) : V.RR) := ⟨P.nonunit⟩
  have := P.cpl
  let iota : T →+* V.RR := i0.codRestrict V.RR hint
  have hcomp : ∀ {n : ℕ} (f : PS T n dd), toC (C := C) (MvPowerSeries.map iota f) = MvPowerSeries.map i0 f := by
    intro n f
    ext mu
    simp only [MvPowerSeries.coeff_map]
    rfl
  let emR : Fin 2 → ZMod d → OE →+* V.RR := fun g a => (p.em g a).codRestrict V.RR (p.em_int g a)
  have hem : ∀ g a x, algebraMap V.RR C (emR g a x) = p.em g a x := fun _ _ _ => rfl
  have hlocI : IsLocalHom iota := ⟨fun t ht => hloc t (v_of_isUnit_RR ht)⟩
  have hlm : ((V.l : ℕ) : V.RR) ∈ maximalIdeal V.RR := (mem_maximalIdeal _).2 P.nonunit
  have hPl : ∀ g, PlaceIn V.l OE V.RR d (emR g) := by
    intro g
    refine placeSt_of_X hPlace V.l OE V.RR hlm hdisc d (emR g) (fun a x => P.mm _ ?_) (fun a a' haa => ?_) ?_
    · exact p.em_frob g a x
    · obtain ⟨x, hx⟩ := p.em_sep (g, a) (g, a') (fun h => haa (Prod.mk.inj h).2)
      exact ⟨x, fun hm => (mem_maximalIdeal _).1 hm (isUnit_RR hx)⟩
    · obtain ⟨ε, h1, h2, h3⟩ := p.em_unr g
      refine ⟨ε, h1, fun a => P.mm _ (h2 a), fun x hx => h3 x fun a => ?_⟩
      have h4 : (0 : WithTop ℝ) ≤ V.v (p.em g a x) := p.em_int g a x
      exact lt_of_le_of_ne h4 fun h5 => (mem_maximalIdeal _).1 (hx a) (isUnit_RR (x := emR g a x) h5.symm)
  have hEig : EigIn p V.RR (fun a i => MvPowerSeries.map iota (actT a i)) emR :=
    eigIn_of_free eigFreeSt_holds p P.vm P.int (fun x hx => ⟨⟨x, hx⟩, rfl⟩) (fun x => x.2) _
      (fun a i => by rw [hcomp]; exact hact a i) emR hem
  exact upChar_of_upFLaw Y p hr Hc P.vm V.RR P.tie P.int P.pos P.lt (fun x hx => P.mm x hx) T FT actT hL
    iota hlocI (fun i => by rw [hcomp]; exact hF i) emR hem hPl hEig

theorem upChar_of_upF_RR [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (hUp : UpFSt V.l) (hPlace : Pl.PlaceCriterionOfIdempotent)
    (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp) (Hc : ∀ g, (Y.raw p).CartHyp V g)
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T]
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (aG : OE → (G ⟶ G)) (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hG : GeoJ T G OE aG dd FT actT)
    (i0 : T →+* C) (hint : ∀ t, V.Ge 0 (i0 t)) (hloc : ∀ t, V.v (i0 t) = 0 → IsUnit t)
    (hF : ∀ i, Y.B.G.F i = MvPowerSeries.map i0 (FT i))
    (hact : ∀ a i, Y.B.A.act a i = MvPowerSeries.map i0 (actT a i))
    (hdisc : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) : UPCharSt Y p Hc :=
  upChar_of_upFLaw_RR hPlace Y p hr Hc T FT actT
    (upFLaw_of_geoJ hUp Y.l_odd T (not_isUnit_l i0 hint) G aG FT actT hG hdisc) i0 hint hloc hF hact hdisc

end RR

section Chart

open Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def GeoJA3St : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y),
    GeoJ T.V C3.I.G.G (𝓞 E) (fun a => C3.I.G.act.act a) (chD C3.ch) C3.FT C3.actT

def UpperCharacterUnramified : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ie : T.Fr →+* C), EmbOK T V ie →
    ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ie k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ie lab) (hg : LabGeo C3 ie Y lab),
    lab.RankOK Dw → ∀ o (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g), UPCharSt Y (pairOfLab ha hg o) Hc

def CharacterHypothesisUnramified : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ie : T.Fr →+* C), EmbOK T V ie →
    ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ie k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ie lab) (hg : LabGeo C3 ie Y lab),
    lab.RankOK Dw → ∀ o (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc

theorem chart_hypothesis_unramified_of_upper (h : UpperCharacterUnramified Xo c) : CharacterHypothesisUnramified Xo c :=
  fun hstar T io y C3 C _ _ V ie hie hd k Y hY Orb d _ lab ha hg hr o Hc =>
    chSt_of_upChar Y (pairOfLab ha hg o) (rankHyp_ofLab ha hg hr o) Hc
      (h hstar T io y C3 C V ie hie hd k Y hY Orb d lab ha hg hr o Hc)

theorem vV_pos (T : CDVR) {t : T.V} (ht : ¬ IsUnit t) (h0 : t ≠ 0) : 0 < vV T.V (algebraMap T.V T.Fr t) := by
  unfold vV
  have hne : valV T.V (algebraMap T.V T.Fr t) ≠ 0 :=
    valV_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 h0)
  have h1 : valV T.V (algebraMap T.V T.Fr t) < 1 := by
    unfold valV
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ t).2 ((mem_maximalIdeal t).2 ht)
  have h2 : WithZero.log (valV T.V (algebraMap T.V T.Fr t)) < 0 :=
    (WithZero.log_lt_iff_lt_exp hne).2 (by simpa using h1)
  omega

variable {Xo c} in

theorem chart_ties {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
    {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C} (hie : EmbOK T V ie)
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y) :
    (∀ t, V.Ge 0 ((ie.comp (algebraMap T.V T.Fr)) t)) ∧
    (∀ t, V.v ((ie.comp (algebraMap T.V T.Fr)) t) = 0 → IsUnit t) ∧
    (∀ i, Y.B.G.F i = MvPowerSeries.map (ie.comp (algebraMap T.V T.Fr)) (C3.FT i)) ∧
    (∀ a i, Y.B.A.act a i = MvPowerSeries.map (ie.comp (algebraMap T.V T.Fr)) (C3.actT a i)) := by
  have hl0 : ((V.l : ℕ) : T.Fr) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
  have hvl : (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) ≠ 0 := by
    intro h0
    have := hie _ hl0
    rw [map_natCast, V.v_l, h0, div_zero] at this
    simp at this
  have hvl' : (0 : ℝ) < (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
    have := vV_algebraMap_nonneg T (V.l : T.V)
    rw [map_natCast] at this
    exact lt_of_le_of_ne (by exact_mod_cast this) (Ne.symm hvl)
  refine ⟨fun t => embIntSt_holds T C V ie hie t, fun t ht => ?_, fun i => ?_, fun a i => ?_⟩
  · by_contra hu
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [map_zero, V.v.map_zero] at ht
      exact WithTop.top_ne_zero ht
    have hne : algebraMap T.V T.Fr t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 ht0
    have h1 := hie _ hne
    rw [RingHom.comp_apply] at ht
    rw [ht] at h1
    have h2 : (0 : ℝ) = (vV T.V (algebraMap T.V T.Fr t) : ℝ) / (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) :=
      WithTop.coe_injective (by simpa using h1)
    have h3 : (0 : ℝ) < (vV T.V (algebraMap T.V T.Fr t) : ℝ) := by exact_mod_cast vV_pos T hu ht0
    have := div_pos h3 hvl'
    linarith
  · rw [hY.F i]
    have e : (a3B C3).G.F i = MvPowerSeries.map (algebraMap T.V T.Fr) (C3.FT i) := C3.gen.1.1 i
    rw [e]
    ext mu
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]
  · rw [hY.act a i]
    have e : (a3B C3).A.act a i = MvPowerSeries.map (algebraMap T.V T.Fr) (C3.actT a i) := C3.gen.1.2.1 a i
    rw [e]
    ext mu
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]

variable {Xo c} in

theorem upChar_at_chartL {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
    {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C} (hPlace : Pl.PlaceCriterionOfIdempotent)
    (hL : UpFLaw V.l T.V (𝓞 E) (chD C3.ch) C3.FT C3.actT)
    (hie : EmbOK T V ie) (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))))
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y)
    {Orb : Type} {d : ℕ} [NeZero d] {lab : Lab E Orb d} (ha : LabArith V io ie lab) (hg : LabGeo C3 ie Y lab)
    (hr : lab.RankOK Dw) (o : Orb) (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g) :
    UPCharSt Y (pairOfLab ha hg o) Hc := by
  obtain ⟨h1, h2, h3, h4⟩ := chart_ties hie hY
  exact upChar_of_upFLaw_RR hPlace Y (pairOfLab ha hg o) (rankHyp_ofLab ha hg hr o) Hc T.V C3.FT C3.actT hL
    (ie.comp (algebraMap T.V T.Fr)) h1 h2 h3 h4 hd

variable {Xo c} in

theorem upFLaw_at_chart {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
    {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C} (hUp : UpFSt V.l) (hl2 : V.l ≠ 2)
    (hGeoJ : GeoJ T.V C3.I.G.G (𝓞 E) (fun a => C3.I.G.act.act a) (chD C3.ch) C3.FT C3.actT)
    (hie : EmbOK T V ie) (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E)))) :
    UpFLaw V.l T.V (𝓞 E) (chD C3.ch) C3.FT C3.actT :=
  upFLaw_of_geoJ hUp hl2 T.V
    (not_isUnit_l (ie.comp (algebraMap T.V T.Fr)) fun t => embIntSt_holds T C V ie hie t)
    C3.I.G.G (fun a => C3.I.G.act.act a) C3.FT C3.actT hGeoJ hd

variable {Xo c} in

theorem upChar_at_chart {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
    {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C} (hUp : UpFSt V.l) (hPlace : Pl.PlaceCriterionOfIdempotent)
    (hGeoJ : GeoJ T.V C3.I.G.G (𝓞 E) (fun a => C3.I.G.act.act a) (chD C3.ch) C3.FT C3.actT)
    (hie : EmbOK T V ie) (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))))
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y)
    {Orb : Type} {d : ℕ} [NeZero d] {lab : Lab E Orb d} (ha : LabArith V io ie lab) (hg : LabGeo C3 ie Y lab)
    (hr : lab.RankOK Dw) (o : Orb) (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g) :
    UPCharSt Y (pairOfLab ha hg o) Hc :=
  upChar_at_chartL hPlace (upFLaw_at_chart hUp Y.l_odd hGeoJ hie hd) hie hd hY ha hg hr o Hc

theorem upper_character_unramified_of_forms (hUp : ∀ (p : ℕ) [Fact p.Prime], UpFSt p) (hPlace : Pl.PlaceCriterionOfIdempotent) (hGeo : GeoJA3St Xo c) :
    UpperCharacterUnramified Xo c :=
  fun hstar T io y C3 _ _ _ V _ hie hd _ _ hY _ _ _ _ ha hg hr o Hc =>
    upChar_at_chart (hUp V.l) hPlace (hGeo hstar T io y C3) hie hd hY ha hg hr o Hc

theorem chart_hypothesis_unramified_of_forms (hUp : ∀ (p : ℕ) [Fact p.Prime], UpFSt p) (hPlace : Pl.PlaceCriterionOfIdempotent) (hGeo : GeoJA3St Xo c) : CharacterHypothesisUnramified Xo c :=
  chart_hypothesis_unramified_of_upper Xo c (upper_character_unramified_of_forms Xo c hUp hPlace hGeo)

end Chart

end UpFBr

end Formalism.L2.FormalSeriesBounds
