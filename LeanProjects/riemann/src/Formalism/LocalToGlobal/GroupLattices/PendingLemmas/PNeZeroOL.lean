import Formalism.LocalToGlobal.GroupLattices.CloudFilling.CloudBound
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainK
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ConditionIffAdditiveMaps
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SysC

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem
open scoped TensorProduct

namespace Formalism.L2.G.Pend

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem std_of {p : ℕ} (G : GAtP p) (Fl : Fills G) (hr1 : 1 ≤ G.P.r) (hr2 : 2 * G.P.r ≤ G.P.m + 1) (hm : 1 ≤ Fl.mm)
    (v : Fin G.P.nV) :
    Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v) where
  prime := (G.P.setting v).prime
  five_le := (G.P.setting v).five_le
  two_le := (G.P.setting v).two_le
  even := (G.P.setting v).even
  r_pos := hr1
  two_r := hr2
  m_pos := hm
  base := Fl.base v
  dom := G.P.dom v
  w_low := fun s => ⟨le_trans (le_max_left _ _) (Fl.w_ge v s), le_trans (le_max_right _ _) (Fl.w_ge v s)⟩
  w_mono := fun s l hl _ => Fl.w_mono v s l hl

section Chain

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) {LL : Type} [Field LL] (e : LL →+* G.Kf) (m : ℕ)
  (V : ℕ → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module LL (V j)] (ix : ℕ → Type) (b : ∀ j, Module.Basis (ix j) LL (V j))
  (cmp : ∀ j, V j →ₛₗ[e] Lv.Fm j) (li : ∀ j, j ≤ m → LinearIndependent G.Kf fun a => cmp j (b j a))
  (KL : ∀ j, V j →ₗ[LL] V (j + 1))

open Classical in

def chainG : Chain Lv where
  Kz j := if hj : j < m then Cmp.extK (cmp j) (cmp (j + 1)) (b j) (li j hj.le) (KL j) else 0

end Chain

section Ring

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (L : IntermediateField (KO p n) (Om p n)) [FiniteDimensional (KO p n) L]

instance fracOL : IsFractionRing (OL p n L) L := IntCl.frac (OO p n) (KO p n) L

instance charZeroL : CharZero L := charZero_of_injective_algebraMap (algebraMap (KO p n) L).injective

theorem p_ne_zero_OL : (p : OL p n L) ≠ 0 := by
  intro h0
  have h1 := congrArg (algebraMap (OL p n L) L) h0
  rw [map_natCast, map_zero] at h1
  exact (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : L) ≠ 0) h1

end Ring

section Record

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)

abbrev gatL : GAtP p := gatRecP D u h (settingOL p (orderOf (zPsi D.R.toFrame h)) L h5 h2 he) r Lc I ψ e

def cembL : CEmb (gatL D u h L h5 h2 he r Lc I ψ e) := ⟨embLC (k0ToC p) L, embLC_int' L⟩

theorem compat_L : Compat (gatL D u h L h5 h2 he r Lc I ψ e) (cembL D u h L h5 h2 he r Lc I ψ e)
    (fun _ => rdW p (orderOf (zPsi D.R.toFrame h))) :=
  fun _ s x => compat_conc L s x

end Record

section Record2

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)

abbrev fillsL : Fills (gatL D u h L h5 h2 he r Lc I ψ e) :=
  fillsRec D u h (settingOL p (orderOf (zPsi D.R.toFrame h)) L h5 h2 he) r Lc I ψ (repP Lc p) e c hc

theorem std_L (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (v : Fin (gatL D u h L h5 h2 he r Lc I ψ e).P.nV) :
    Std p ((gatL D u h L h5 h2 he r Lc I ψ e).P.n' v) (gatL D u h L h5 h2 he r Lc I ψ e).P.m
      (fillsL D u h L h5 h2 he r Lc I ψ e c hc).t (fillsL D u h L h5 h2 he r Lc I ψ e c hc).mm
      (fillsL D u h L h5 h2 he r Lc I ψ e c hc).c (gatL D u h L h5 h2 he r Lc I ψ e).P.r
      ((fillsL D u h L h5 h2 he r Lc I ψ e c hc).TT v) ((fillsL D u h L h5 h2 he r Lc I ψ e c hc).a v)
      ((fillsL D u h L h5 h2 he r Lc I ψ e c hc).b v) ((gatL D u h L h5 h2 he r Lc I ψ e).P.lam0 v)
      ((fillsL D u h L h5 h2 he r Lc I ψ e c hc).w v) :=
  std_of _ _ hr1 (by
    show 2 * r ≤ D.R.k - 1 + 1
    rw [k_pred]
    exact hr2) (by
    show 1 ≤ D.R.m
    exact le_trans (by norm_num) D.R.two_le_m) v

variable (Lv : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc)) (Ch : Chain Lv)
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (hfin : ∀ j c', (Lv.lev j c').FinClasses)

abbrev sysL : Sys p :=
  sysC (gatL D u h L h5 h2 he r Lc I ψ e) (fillsL D u h L h5 h2 he r Lc I ψ e c hc) Lv Ch
    (std_L D u h L h5 h2 he r Lc I ψ e c hc hr1 hr2) hfin (p_ne_zero_OL L)

end Record2

section Record3

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (Lv : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc)) (Ch : Chain Lv)
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (hfin : ∀ j c', (Lv.lev j c').FinClasses) (hst : FinStab Lv)
  {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g)

abbrev posL : (Σ v : (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Pl,
    Fin ((sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).G.P.n' v)) ≃ D.what₂.Tau :=
  gatRec_pos D u h (settingOL p (orderOf (zPsi D.R.toFrame h)) L h5 h2 he) r Lc I ψ (repP Lc p) e

abbrev pendL
    (F : ∀ j, (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Lt j →
      (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin (((sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) ×
        Fin (((sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Pj j).m + 1)) ℂ_[p]) :
    Pend (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin) :=
  @pendC p hp (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin) (fracOL L)
    (cembL D u h L h5 h2 he r Lc I ψ e) hfin hst (beLT hLT)
    (thFOf (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin)
      (posL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin) F)

end Record3

section ChainF

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) {D : D7} (Tw : TwForms D) (u : D.what₂.Word)
  (w : D.what₂.places.Pl) (eL : D.what₂.LL →+* G.Kf)
  (cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[eL] Lv.Fm j)
  (li : ∀ j, j ≤ D.R.m → LinearIndependent G.Kf fun a => cmp j (((Tw.fm u (D.what₂.muAt w)).lat j).b a))

abbrev chainF : Chain Lv :=
  chainG Lv eL D.R.m (fun j => ((Tw.fm u (D.what₂.muAt w)).lat j).V) (fun j => ((Tw.fm u (D.what₂.muAt w)).lat j).ι)
    (fun j => ((Tw.fm u (D.what₂.muAt w)).lat j).b) cmp li (fun j => Cmp.KLx Tw u w j)

end ChainF

abbrev LW (D : D7) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime] (h : D.R.MA) :
    IntermediateField (KO (D.what₂.places.resChar w) (orderOf (zPsi D.R.toFrame h)))
      (Om (D.what₂.places.resChar w) (orderOf (zPsi D.R.toFrame h))) :=
  Lt (tauRec D w (orderOf (zPsi D.R.toFrame h)))

end Formalism.L2.G.Pend
