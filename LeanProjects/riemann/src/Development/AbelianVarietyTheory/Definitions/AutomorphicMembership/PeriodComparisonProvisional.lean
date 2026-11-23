import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam

variable {D : D7}

section Same

theorem samePt_of_heq {r j p r' j' : ℕ} {Λ : ModuliIntegralCharts.Loc D r j p} {Λ' : ModuliIntegralCharts.Loc D r' j' p} (hr : r = r') (hj : j = j')
    (hΛ : HEq Λ Λ') {y : Λ.Pt Λ.YY} {y' : Λ'.Pt Λ'.YY} (hy : HEq y y') :
    Λ.fld y = Λ'.fld y' ∧
      (∃ e : Λ.Ylat y ≃ₗ[𝓞 D.host.E] Λ'.Ylat y', ∀ a b, Λ'.be y' (e a) (e b) = Λ.be y a b) ∧
      (Λ.good y ↔ Λ'.good y') ∧ Λ.phiCy y = Λ'.phiCy y' ∧ Λ.dP y = Λ'.dP y' := by
  subst hr hj; cases hΛ; cases hy
  exact ⟨rfl, ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩, Iff.rfl, rfl, rfl⟩

theorem lat_of_heq {r j p r' j' : ℕ} {Λ : ModuliIntegralCharts.Loc D r j p} {Λ' : ModuliIntegralCharts.Loc D r' j' p} (hr : r = r') (hj : j = j')
    (hΛ : HEq Λ Λ') {y : Λ.Pt Λ.YY} {y' : Λ'.Pt Λ'.YY} (hy : HEq y y') {Y : Type} [AddCommGroup Y]
    [Module (𝓞 D.host.E) Y] (β : Y → Y → ℝ)
    (hY : ∃ e : Λ.Ylat y ≃ₗ[𝓞 D.host.E] Y, ∀ a b, β (e a) (e b) = Λ.be y a b) :
    ∃ e : Λ'.Ylat y' ≃ₗ[𝓞 D.host.E] Y, ∀ a b, β (e a) (e b) = Λ'.be y' a b := by
  subst hr hj; cases hΛ; cases hy; exact hY

theorem pt_eq_of_heq {r j p r' j' : ℕ} {Λ : ModuliIntegralCharts.Loc D r j p} {Λ' : ModuliIntegralCharts.Loc D r' j' p} (hr : r = r') (hj : j = j')
    (hΛ : HEq Λ Λ') : Λ.Pt Λ.YY = Λ'.Pt Λ'.YY := by
  subst hr hj; cases hΛ; rfl

theorem loc_heq_of_eq {P P' : ModuliIntegralCharts.Prov D} (hP : P = P') {d : P.Dat} {d' : P'.Dat} (hd : HEq d d') (p : ℕ) :
    HEq (P.loc d p) (P'.loc d' p) := by
  subst hP; cases hd; rfl

end Same

section Comparison₂

variable {T : Top D} (h : LawsP T) {F : SrcFam (ambOf T.Q h.pins.1)} (t : ParTie T.Q h.pins.1 F) {L : CmList (ambOf T.Q h.pins.1)}
  {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C) {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (k : Kits F L C jC ng)

def LocTie : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ p,
  HEq (T.G.P.loc (T.G.dat j) p) ((k.at (datW D F.κg j)).pad.loc p)

variable {h t K R k}

theorem rk_dat_eq (h : LawsP T) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) :
    T.G.P.rk (T.G.dat j) = (datW D κ j).N :=
  (h.datum_condition j h1 hm).1.trans (datW_N D κ j).symm

theorem jj_dat_eq (h : LawsP T) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) :
    T.G.P.jj (T.G.dat j) = (datW D κ j).j :=
  (h.datum_condition j h1 hm).2.trans (datW_j D κ h1 hm.le).symm

theorem LocTie.pts (H : LocTie h k) : PtsTie h k := fun j h1 hm p =>
  pt_eq_of_heq (rk_dat_eq h F.κg h1 hm) (jj_dat_eq h F.κg h1 hm) (H j h1 hm p)

theorem LocTie.samePt (H : LocTie h k) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {p : ℕ} {η : T.G.PY j p}
    {η' : ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY} (he : HEq η η') :
    (T.G.P.loc (T.G.dat j) p).fld η = ((k.at (datW D F.κg j)).pad.loc p).fld η' ∧
      (∃ e : (T.G.P.loc (T.G.dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] ((k.at (datW D F.κg j)).pad.loc p).Ylat η',
        ∀ a b, ((k.at (datW D F.κg j)).pad.loc p).be η' (e a) (e b) = (T.G.P.loc (T.G.dat j) p).be η a b) ∧
      ((T.G.P.loc (T.G.dat j) p).good η ↔ ((k.at (datW D F.κg j)).pad.loc p).good η') ∧
      (T.G.P.loc (T.G.dat j) p).phiCy η = ((k.at (datW D F.κg j)).pad.loc p).phiCy η' ∧
      (T.G.P.loc (T.G.dat j) p).dP η = ((k.at (datW D F.κg j)).pad.loc p).dP η' :=
  samePt_of_heq (rk_dat_eq h F.κg h1 hm) (jj_dat_eq h F.κg h1 hm) (H j h1 hm p) he

theorem LocTie.lat (H : LocTie h k) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {la : HeightOneSpectrum (𝓞 T.Q.c.F)}
    {z : PointsOfFlagModel.Pt (T.G.Tw j (WeightAlgebra.resCh la)) .yy} (hz : T.G.IsAlgPt j la z) {η : T.G.PY j (WeightAlgebra.resCh la)}
    (hr : T.G.rel j _ η z)
    {η' : ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).Pt ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).YY}
    (he : HEq η η') (A : DatAt ((T.G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1) :
    ∃ e : ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).Ylat η' ≃ₗ[𝓞 D.host.E] A.Ylat,
      ∀ a b, A.beta (e a) (e b) = ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).be η' a b :=
  lat_of_heq (rk_dat_eq h F.κg h1 hm) (jj_dat_eq h F.κg h1 hm) (H j h1 hm _) he (fun a b => A.beta a b)
    (h.lattice_condition j h1 hm la z hz η hr A)

theorem LocTie.localTie_of_provisional (K : CutSt C) (R : ResSt C) {I : Type} {dat : I → Dat D (Lv (ambOf T.Q h.pins.1))}
    {hI : ∀ i, (dat i).Indef} {iW : ℕ → I} (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j)
    (hP : T.G.P = indefiniteDataFamily (shimOf K R k) I dat hI) (hd : ∀ j, 1 ≤ j → j < D.R.m → HEq (T.G.dat j) (iW j)) :
    LocTie h k := fun j h1 hm p => by
  refine (loc_heq_of_eq hP (hd j h1 hm) p).trans ?_
  show HEq ((k.at (dat (iW j))).pad.loc p) _
  rw [hiW j h1 hm]

example {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {p : ℕ} {η : T.G.PY j p}
    {η' : ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY} (he : HEq η η')
    (hη : (T.G.P.loc (T.G.dat j) p).good η) (hη' : ¬ ((k.at (datW D F.κg j)).pad.loc p).good η') : ¬ LocTie h k :=
  fun H => hη' ((H.samePt h1 hm he).2.2.1.1 hη)

example {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {p : ℕ} {η : T.G.PY j p}
    {η' : ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY} (he : HEq η η')
    (hne : (T.G.P.loc (T.G.dat j) p).phiCy η ≠ ((k.at (datW D F.κg j)).pad.loc p).phiCy η') : ¬ LocTie h k :=
  fun H => hne (H.samePt h1 hm he).2.2.2.1

section Phi

variable {P : FormsOver K R k} (hg : F.κg.primes = Finset.univ.image D.host.g)
  {I : Type} {dat : I → Dat D (Lv (ambOf T.Q h.pins.1))} (hI : ∀ i, (dat i).Indef) {iW : ℕ → I}
  (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D (famOf K R k hg P).κg j)

end Phi

end Comparison₂

end GlobalTheory.ShFam
