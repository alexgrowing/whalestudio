import Formalism.LocalToGlobal.GroupLattices.CloudFilling.TauTopPlacesIff
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie
import Formalism.LocalRingCardinality.DataExtra
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure LocPack (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (p : ℕ) where
  W : Type
  Qq : Type
  O : Type
  Kf : Type
  [cW : CommRing W]
  [dW : IsDomain W]
  [vW : IsDiscreteValuationRing W]
  [fQ : Field Qq]
  [aW : Algebra W Qq]
  [cO : CommRing O]
  [dO : IsDomain O]
  [vO : IsDiscreteValuationRing O]
  [fK : Field Kf]
  [aO : Algebra O Kf]
  ι : Qq →+* Kf
  σ : Qq ≃+* Qq
  j : W →+* O
  w : O
  hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w
  I : LocId Lc p (nOrb (zH D.R.toFrame (hP D p))) W Qq
  ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* Oˣ

attribute [instance] LocPack.cW LocPack.dW LocPack.vW LocPack.fQ LocPack.aW LocPack.cO LocPack.dO LocPack.vO LocPack.fK
  LocPack.aO

def rSc (sc : Scale) (k p : ℕ) : ℕ := if (p : ℝ) < sc.p0 k then rG sc else 1

theorem rRec_eq {D : D7} (L : SizeData₂ D) (p : ℕ) : rRec L p = rSc L.sc D.R.k p := rfl

def epSc (R : Ranks) (sc : Scale) (Ce : ℝ) (p : ℕ) : ℕ := ⌈Ce * (R.f : ℝ) * (R.k : ℝ) ^ 2 * Real.logb p sc.a⌉₊

abbrev LocPack.gat {D : D7} {u : D.what₂.Word}
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {p : ℕ} (X : LocPack D u Lc p)
    (r e : ℕ) : GAtP p :=
  gatRec D u (D.R.iota (hP D p)) X.hS r Lc X.I X.ψ (repP Lc p) e

def LocPack.posOK {D : D7} {u : D.what₂.Word}
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {p : ℕ} [Fact p.Prime]
    (X : LocPack D u Lc p) (iK : X.Kf →+* ℂ_[p])
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) : Prop :=
  PosCompat D.host (D.R.iota (hP D p)) X.ι X.σ X.I.iw iK lam

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (X : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocPack D u (Lc u) (D.what₂.places.resChar w))
  (hd : ∀ u w h, ((X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))).d =
    Module.finrank ℂ (D.mem u).A.Mu0)

def recG : D7 :=
  { D with
    gat := fun u w h => (X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))
    gat_d := hd }

def gatTiesG : GatTies (recG D sc Ce Lc X hd) where
  gat_k := fun _ _ _ => k_pred D.R
  gat_n := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) v (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
      (hL : P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})) τ hτ =>
    haveI := hP
    haveI := hL
    gatRec_n_frob D u h (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _) _ v P τ hτ
  gat_pos := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) =>
    gatRec_pos D u _ (X u w h).hS (rSc sc D.R.k (D.what₂.places.resChar w)) (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _)
      (epSc D.R sc Ce (D.what₂.places.resChar w))
  gat_step := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) v s (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
      (hL : P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})) τ hτ =>
    haveI := hP
    haveI := hL
    gatRec_step_frob D u h (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _) _ v s P τ hτ
  gat_lam := fun _ _ _ _ _ _ => rfl

variable (L : SizeData₂ (recG D sc Ce Lc X hd)) (P : ParameterChoice' (recG D sc Ce Lc X hd) L)

def fillsG (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Fills ((recG D sc Ce Lc X hd).gat u w h) :=
  fillsRec D u _ (X u w h).hS (rSc sc D.R.k (D.what₂.places.resChar w)) (Lc u) (X u w h).I (X u w h).ψ
    (repP (Lc u) _) (epSc D.R sc Ce (D.what₂.places.resChar w)) (cRec L) ⟨(cloudBound L P u).top, (cloudBound L P u).off, (cloudBound L P u).fill⟩

def latInstG (Lv : ∀ u w h, Levels (fillsG D sc Ce Lc X hd L P u w h)) (Ch : ∀ u w h, Chain (Lv u w h))
    (Vram : ∀ u w h, Submodule ((recG D sc Ce Lc X hd).gat u w h).O ((recG D sc Ce Lc X hd).gat u w h).Fn) :
    LatInst (recG D sc Ce Lc X hd) where
  vOf := fun _ w _ => vOfH D.R.toFrame (hP D (D.what₂.places.resChar w))
  Fl := fillsG D sc Ce Lc X hd L P
  Lv := Lv
  Ch := Ch
  Vram := Vram

set_option maxHeartbeats 4000000 in

theorem latTiedG (hsc : L.sc = sc) (K : Consts) (Lv : ∀ u w h, Levels (fillsG D sc Ce Lc X hd L P u w h))
    (Ch : ∀ u w h, Chain (Lv u w h))
    (Vram : ∀ u w h, Submodule ((recG D sc Ce Lc X hd).gat u w h).O ((recG D sc Ce Lc X hd).gat u w h).Fn) :
    LatTied (gatTiesG D sc Ce Lc X hd) (instRec L K Ce) (latInstG D sc Ce Lc X hd L P Lv Ch Vram) := by
  rw [latTied_iff]
  intro (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  exact latTiedAt_rec L P K Ce u h.2.2.1 (X u w h).hS _ (by rw [rRec_eq, hsc]; rfl) (Lc u) (X u w h).I (X u w h).ψ
    (repP (Lc u) _) _

theorem fill_instRec_eq_wj (K : Consts) :
    ∀ j ∈ SizeData₂.lifts (recG D sc Ce Lc X hd), ∀ (τ : D.what₂.Tau) (z : Bool × HH D),
      (D.eTau τ : D.R.GG) = plGG D z → fill (instRec L K Ce) (bL L) j z = wj D j τ :=
  instRec_fill L K Ce

def levTieG (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Formalism.L2.Herm.GLevTie (Lc u) ((recG D sc Ce Lc X hd).gat u w h) :=
  gatRecP_lev D u _ (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ _

theorem epTieG (hsc : L.sc = sc) (K : Consts) : EpTie (instRec L K Ce) := by
  intro u w h
  show epSc D.R sc Ce (D.what₂.places.resChar w) =
    ⌈Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a⌉₊
  rw [hsc]
  rfl

theorem fillsAllG (Lv : ∀ u w h, Levels (fillsG D sc Ce Lc X hd L P u w h)) (Ch : ∀ u w h, Chain (Lv u w h))
    (Vram : ∀ u w h, Submodule ((recG D sc Ce Lc X hd).gat u w h).O ((recG D sc Ce Lc X hd).gat u w h).Fn) :
    FillsAll (gatTiesG D sc Ce Lc X hd) (latInstG D sc Ce Lc X hd L P Lv Ch Vram) :=
  fun u _ _ _ _ j hj => wRec_eq D u _ j hj

theorem std_of_fills {p : ℕ} (G : GAtP p) (Fl : Fills G) (v : Fin G.P.nV) (hr : 1 ≤ G.P.r) (h2r : 2 * G.P.r ≤ G.P.m + 1)
    (hm : 1 ≤ Fl.mm) :
    Formalism.MainNotions.FormalGroupSystem.Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v) where
  prime := (G.P.setting v).prime
  five_le := (G.P.setting v).five_le
  two_le := (G.P.setting v).two_le
  even := (G.P.setting v).even
  r_pos := hr
  two_r := h2r
  m_pos := hm
  base := Fl.base v
  dom := G.P.dom v
  w_low := fun s => ⟨le_trans (le_max_left _ _) (Fl.w_ge v s), le_trans (le_max_right _ _) (Fl.w_ge v s)⟩
  w_mono := fun s l h1 _ => Fl.w_mono v s l h1

theorem one_le_rSc (k p : ℕ) : 1 ≤ rSc sc k p := by
  unfold rSc rG
  split_ifs <;> omega

theorem two_rSc_le (k p : ℕ) (h : 2 * rG sc ≤ k) : 2 * rSc sc k p ≤ k := by
  unfold rSc
  split_ifs
  · exact h
  · unfold rG at h
    omega

theorem stdG (h2r : 2 * rG sc ≤ D.R.k) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin ((recG D sc Ce Lc X hd).gat u w h).P.nV) :
    Formalism.MainNotions.FormalGroupSystem.Std (D.what₂.places.resChar w) (((recG D sc Ce Lc X hd).gat u w h).P.n' v) ((recG D sc Ce Lc X hd).gat u w h).P.m
      (fillsG D sc Ce Lc X hd L P u w h).t (fillsG D sc Ce Lc X hd L P u w h).mm (fillsG D sc Ce Lc X hd L P u w h).c
      ((recG D sc Ce Lc X hd).gat u w h).P.r ((fillsG D sc Ce Lc X hd L P u w h).TT v) ((fillsG D sc Ce Lc X hd L P u w h).a v)
      ((fillsG D sc Ce Lc X hd L P u w h).b v) (((recG D sc Ce Lc X hd).gat u w h).P.lam0 v)
      ((fillsG D sc Ce Lc X hd L P u w h).w v) := by
  refine std_of_fills _ _ v ?_ ?_ ?_
  · exact one_le_rSc sc _ _
  · have h1 := two_rSc_le sc D.R.k (D.what₂.places.resChar w) h2r
    have h2 := D.R.m_add_three_le_k
    show 2 * rSc sc D.R.k (D.what₂.places.resChar w) ≤ D.R.k - 1 + 1
    omega
  · have := D.R.two_le_m
    show 1 ≤ D.R.m
    omega

end Formalism.L2.G
