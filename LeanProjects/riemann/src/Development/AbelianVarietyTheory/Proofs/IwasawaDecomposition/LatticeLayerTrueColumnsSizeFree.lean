import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GyLat

open Formalism.L2.G Formalism.MainNotions.G Formalism.UG Formalism.FrobeniusOrbits
open scoped TensorProduct

open Classical in

theorem arith_bsH_eq {φ : Formalism.HC.Frame} (h t : φ.A) : Formalism.L2.GlobalTheoryTheory.Arith.bsH h t = Formalism.L2.G.bsH φ h t := by
  rw [bsH_eq_bsA]
  have hex : ∃ v : ℕ, ∃ i : ℕ, φ.ofNat v + i • h = t := ⟨t.val, 0, by simp⟩
  unfold Formalism.L2.GlobalTheoryTheory.Arith.bsH
  rw [dif_pos hex]
  unfold Formalism.MainNotions.Inhab.bsA
  congr 1
  apply le_antisymm
  · apply Nat.find_min'
    obtain ⟨i, hi⟩ := Formalism.MainNotions.Inhab.bsA_orb h t
    exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := Nat.find_spec hex
    set v := Nat.find hex
    have hN : 1 ≤ φ.ord := φ.ord_pos
    have hv : φ.ofNat v = t + (i * (φ.ord - 1)) • h := by
      have h1 : (i * (φ.ord - 1)) • h + i • h = 0 := by
        rw [← add_nsmul]
        have : i * (φ.ord - 1) + i = i * φ.ord := by
          calc i * (φ.ord - 1) + i = i * (φ.ord - 1 + 1) := by ring
            _ = i * φ.ord := by rw [Nat.sub_add_cancel hN]
        rw [this, mul_nsmul', Formalism.MainNotions.Inhab.ord_nsmul_A, nsmul_zero]
      calc φ.ofNat v = φ.ofNat v + i • h + (i * (φ.ord - 1)) • h := by
            rw [add_assoc, add_comm (i • h), h1, add_zero]
        _ = t + (i * (φ.ord - 1)) • h := by rw [hi]
    have hle := Formalism.MainNotions.Inhab.bsA_val_le h t (i * (φ.ord - 1))
    rw [Formalism.MainNotions.Inhab.bsA_val, ← hv, Formalism.HC.Frame.val_ofNat] at hle
    exact hle.trans (Nat.mod_le _ _)

end GlobalTheory.GyLat

namespace GlobalTheory.GyLat

open Formalism.L2.G Formalism.MainNotions.G Formalism.UG Formalism.FrobeniusOrbits
open scoped TensorProduct

theorem reps_canon {D : D7} {L : SizeData₂ D} (X : Inst D L) (hb : ∀ h t, X.bs h t = Formalism.L2.GlobalTheoryTheory.Arith.bsH h t) {p : ℕ}
    (hc : IsResidueClassZero D p) : ((reps X p : Finset (HH D)) : Set (HH D)) = Set.range (Formalism.L2.G.bsH D.R.toFrame (hP D p)) := by
  have hs : stepP D p = hP D p := by
    unfold stepP
    rw [if_neg (fun h : D.host.cls p = PrimeClass.signal => by
      have hc' : D.host.cls p = PrimeClass.inertClass := hc
      rw [hc'] at h; exact PrimeClass.noConfusion h)]
  unfold reps
  rw [hs]
  ext x
  simp [hb, arith_bsH_eq]

theorem orbitFill_eq_sizeMinusWeight_firstPlace {D : D7} {L : SizeData₂ D} (X : Inst D L)
    (hfill : ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × HH D), (D.eTau τ : D.R.GG) = plGG D z →
      fill X (bL L) j z = wj D j τ) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t : HH D) :
    fillG X (bL L) j (false, t) = wj D j (D.eTau.symm (tau1P D.R.toFrame t)) - kaJ D j := by
  unfold fillG
  rw [hfill j hj (D.eTau.symm (tau1P D.R.toFrame t)) (false, t)
    (by rw [Equiv.apply_symm_apply, Formalism.MainNotions.Inhab.plGG_false]; rfl)]

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem latTiedAt_canon {D : D7} (L : SizeData₂ D) (X : Inst D L) (hb : ∀ h t, X.bs h t = Formalism.L2.GlobalTheoryTheory.Arith.bsH h t)
    (hfill : ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × HH D), (D.eTau τ : D.R.GG) = plGG D z →
      fill X (bL L) j z = wj D j τ) (u : D.what₂.Word)
    (hc : IsResidueClassZero D p) (hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w) (r : ℕ) (hr : r = rRec L p)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId Lc p (nOrb (zH D.R.toFrame (hP D p))) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* Oˣ)
    (y : compL Lc p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) (c : ℕ) (hcl : CloudBound D u c)
    (hcc : (c : ℝ) ≤ cG L) :
    LatticeCompatibleAt X (gatRec D u (D.R.iota (hP D p)) hS r Lc I ψ y e)
      (gatRec_pos D u (D.R.iota (hP D p)) hS r Lc I ψ y e) (vOfH D.R.toFrame (hP D p))
      (fillsRec D u (D.R.iota (hP D p)) hS r Lc I ψ y e c hcl) := by
  subst hr
  refine ⟨rfl, rfl, hcc, rfl, ?_, ?_, ?_⟩
  · rw [reps_canon X hb hc]
    exact vOfH_injOn _ _
  · intro v s t ht
    have ht' : ((posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩ : D.R.Psi) : D.R.GG) = D.R.tau2 t := by
      have h0 : ((D.eTau (D.eTau.symm (posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩)) : D.R.Psi) : D.R.GG) = D.R.tau2 t := ht
      rwa [Equiv.apply_symm_apply] at h0
    refine ⟨fun hs => ?_, fun jj hj => ?_⟩
    · have h1 : ((posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces := (Finset.mem_filter.1 hs).2
      rw [ht', ← Formalism.MainNotions.Inhab.plGG_true, Formalism.MainNotions.Inhab.plGG_top_iff] at h1
      exact Bool.noConfusion h1.1
    · show ((wRec D u (posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩) jj : ℤ) : ℝ) = _
      rw [wRec_eq D u _ jj hj]
      unfold fillG
      rw [hfill jj hj (D.eTau.symm (posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩)) (true, t)
        (by rw [Equiv.apply_symm_apply, ht', Formalism.MainNotions.Inhab.plGG_true])]
  · intro t0 ht0
    have ht0' : t0 ∈ Set.range (Formalism.L2.G.bsH D.R.toFrame (hP D p)) := by
      rw [← reps_canon X hb hc]; exact ht0
    obtain ⟨x, rfl⟩ := ht0'
    refine ⟨orderOf_zH _ _, fun s => ?_⟩
    have hpos : posG (zH D.R.toFrame (hP D p)) ⟨vOfH D.R.toFrame (hP D p) (Formalism.L2.G.bsH D.R.toFrame (hP D p) x), s⟩ =
        tau1P D.R.toFrame (Formalism.L2.G.bsH D.R.toFrame (hP D p) x + s.val • hP D p) := by
      rw [posG_vOfH, bsH_idem]
    have hmem : (s ∈ (fillsRec D u (D.R.iota (hP D p)) hS (rRec L p) Lc I ψ y e c hcl).TT
        (vOfH D.R.toFrame (hP D p) (Formalism.L2.G.bsH D.R.toFrame (hP D p) x))) ↔
        Formalism.L2.G.bsH D.R.toFrame (hP D p) x + s.val • hP D p ∈ D.host.TT := by
      rw [← tau_top_places_iff]
      show s ∈ Finset.univ.filter _ ↔ _
      rw [Finset.mem_filter, hpos]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    have ha : (fillsRec D u (D.R.iota (hP D p)) hS (rRec L p) Lc I ψ y e c hcl).a
        (vOfH D.R.toFrame (hP D p) (Formalism.L2.G.bsH D.R.toFrame (hP D p) x)) s =
        aL L (Formalism.L2.G.bsH D.R.toFrame (hP D p) x + s.val • hP D p) := by
      show (if ((posG (zH D.R.toFrame (hP D p)) _ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces then
        lamRec D u (posG (zH D.R.toFrame (hP D p)) _) 0 else 0) = _
      rw [hpos, tau_coe_val]
      unfold aL
      by_cases ht : Formalism.L2.G.bsH D.R.toFrame (hP D p) x + s.val • hP D p ∈ D.host.TT
      · rw [if_pos ((tau_top_places_iff D _).2 ht), dif_pos ht]
        exact (lamRec_top L u _ ⟨_, ht⟩ rfl).1
      · rw [if_neg (fun h => ht ((tau_top_places_iff D _).1 h)), dif_neg ht]
    have hb' : (fillsRec D u (D.R.iota (hP D p)) hS (rRec L p) Lc I ψ y e c hcl).b
        (vOfH D.R.toFrame (hP D p) (Formalism.L2.G.bsH D.R.toFrame (hP D p) x)) s =
        bL L (Formalism.L2.G.bsH D.R.toFrame (hP D p) x + s.val • hP D p) := by
      show (if ((posG (zH D.R.toFrame (hP D p)) _ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces then
        -lamRec D u (posG (zH D.R.toFrame (hP D p)) _) (Fin.last _) else 0) = _
      rw [hpos, tau_coe_val]
      unfold bL
      by_cases ht : Formalism.L2.G.bsH D.R.toFrame (hP D p) x + s.val • hP D p ∈ D.host.TT
      · rw [if_pos ((tau_top_places_iff D _).2 ht), dif_pos ht, (lamRec_top L u _ ⟨_, ht⟩ rfl).2, neg_neg]
      · rw [if_neg (fun h => ht ((tau_top_places_iff D _).1 h)), dif_neg ht]
    refine ⟨?_, hmem, fun _ => ⟨ha, hb'⟩, fun jj hj => ?_⟩
    · show ((D.eTau (D.eTau.symm (posG (zH D.R.toFrame (hP D p)) _)) : D.R.Psi) : D.R.GG) = _
      rw [Equiv.apply_symm_apply, hpos]
      rfl
    · show ((wRec D u (posG (zH D.R.toFrame (hP D p)) _) jj : ℤ) : ℝ) = _
      rw [hpos, wRec_eq D u _ jj hj, orbitFill_eq_sizeMinusWeight_firstPlace X hfill jj hj]

end GlobalTheory.GyLat

namespace GlobalTheory.GyLat

open Formalism.L2.G Formalism.MainNotions.G Formalism.UG Formalism.FrobeniusOrbits

attribute [local instance] Formalism.BasicNotions.factResChar

section RecG

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (X : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocPack D u (Lc u) (D.what₂.places.resChar w))
  (hd : ∀ u w h, ((X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))).d =
    Module.finrank ℂ (D.mem u).A.Mu0)

noncomputable def fillsC (c : ℕ) (hcl : ∀ u, CloudBound (recG D sc Ce Lc X hd) u c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Fills ((recG D sc Ce Lc X hd).gat u w h) :=
  fillsRec D u _ (X u w h).hS (rSc sc D.R.k (D.what₂.places.resChar w)) (Lc u) (X u w h).I (X u w h).ψ
    (repP (Lc u) _) (epSc D.R sc Ce (D.what₂.places.resChar w)) c ⟨(hcl u).top, (hcl u).off, (hcl u).fill⟩

set_option maxHeartbeats 4000000 in

theorem latTied_fillsC (c : ℕ) (hcl : ∀ u, CloudBound (recG D sc Ce Lc X hd) u c)
    (Lv : ∀ u w h, Levels (fillsC D sc Ce Lc X hd c hcl u w h)) (Ch : ∀ u w h, Chain (Lv u w h))
    (Vram : ∀ u w h, Submodule ((recG D sc Ce Lc X hd).gat u w h).O ((recG D sc Ce Lc X hd).gat u w h).Fn)
    (L : SizeData₂ (recG D sc Ce Lc X hd)) (hsc : L.sc = sc) (hcc : (c : ℝ) ≤ cG L) (Xi : Inst (recG D sc Ce Lc X hd) L)
    (hb : ∀ h t, Xi.bs h t = Formalism.L2.GlobalTheoryTheory.Arith.bsH h t)
    (hfill : D.what₂.places.Pl → ∀ j ∈ SizeData₂.lifts (recG D sc Ce Lc X hd), ∀ (τ : D.what₂.Tau) (z : Bool × HH D),
      (D.eTau τ : D.R.GG) = plGG D z → fill Xi (bL L) j z = wj (recG D sc Ce Lc X hd) j τ) :
    LatTied (gatTiesG D sc Ce Lc X hd) Xi
      ⟨fun _ w _ => vOfH D.R.toFrame (hP D (D.what₂.places.resChar w)), fillsC D sc Ce Lc X hd c hcl, Lv, Ch, Vram⟩ := by
  rw [latTied_iff]
  intro (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  exact latTiedAt_canon (D := recG D sc Ce Lc X hd) L Xi hb (hfill w) u h.2.2.1 (X u w h).hS
    (rSc sc D.R.k (D.what₂.places.resChar w)) (by rw [rRec_eq, hsc]; rfl) (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _)
    (epSc D.R sc Ce (D.what₂.places.resChar w)) c (hcl u) hcc

theorem fillsC_w (c : ℕ) (hcl : ∀ u, CloudBound (recG D sc Ce Lc X hd) u c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (x : Fin ((recG D sc Ce Lc X hd).gat u w h).P.nV)
    (s : Fin (((recG D sc Ce Lc X hd).gat u w h).P.n' x)) :
    ∀ j ∈ SizeData₂.lifts (recG D sc Ce Lc X hd), ((fillsC D sc Ce Lc X hd c hcl u w h).w x j s : ℝ) =
      wj (recG D sc Ce Lc X hd) j ((gatTiesG D sc Ce Lc X hd).gat_pos u w h ⟨x, s⟩) - kaJ (recG D sc Ce Lc X hd) j :=
  fun j hj => wRec_eq D u _ j hj

end RecG

end GlobalTheory.GyLat

namespace GlobalTheory.GyLat

open Formalism.L2.G Formalism.MainNotions.G Formalism.UG Formalism.FrobeniusOrbits

attribute [local instance] Formalism.BasicNotions.factResChar

set_option maxHeartbeats 4000000 in

theorem latLayer_of_eq (sc : Scale) (D : D7) (Gt : GatTies D) (D0 : D7) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D0.R D0.host.F D0.host.E D0.sp D0.host.g (D0.mem u).C (D0.mem u).A (D0.clsLat u))
    (X : ∀ u (w : D0.what₂.places.Pl), GIdx D0.host (D0.mem u).A.T (D0.what₂.places.resChar w) →
      LocPack D0 u (Lc u) (D0.what₂.places.resChar w))
    (hd : ∀ u w h, ((X u w h).gat (rSc sc D0.R.k (D0.what₂.places.resChar w)) (epSc D0.R sc Ce (D0.what₂.places.resChar w))).d =
      Module.finrank ℂ (D0.mem u).A.Mu0)
    (hR : (⟨D, Gt⟩ : Σ D : D7, GatTies D) = ⟨recG D0 sc Ce Lc X hd, gatTiesG D0 sc Ce Lc X hd⟩)
    (c : ℕ) (hcl : ∀ u, CloudBound D u c) :
    ∃ (vOf : ∀ u (v : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)),
        HH D → Fin (D.gat u v hg).P.nV)
      (Fl : ∀ u (v : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)), Fills (D.gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = D.R.t ∧ (Fl u v hg).mm = D.R.m) ∧
      (∀ u v hg (x : Fin (D.gat u v hg).P.nV) (s : Fin ((D.gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts D,
        ((Fl u v hg).w x j s : ℝ) = wj D j (Gt.gat_pos u v hg ⟨x, s⟩) - kaJ D j) ∧
      ∀ (Lv : ∀ u v hg, Levels (Fl u v hg)) (Ch : ∀ u v hg, Chain (Lv u v hg))
        (Vram : ∀ u v hg, Submodule (D.gat u v hg).O (D.gat u v hg).Fn) (L : SizeData₂ D), L.sc = sc → (c : ℝ) ≤ cG L →
        ∀ Xi : Inst D L, (∀ h t, Xi.bs h t = Formalism.L2.GlobalTheoryTheory.Arith.bsH h t) →
        (D.what₂.places.Pl → ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × HH D),
          (D.eTau τ : D.R.GG) = plGG D z → fill Xi (bL L) j z = wj D j τ) →
        LatTied Gt Xi ⟨vOf, Fl, Lv, Ch, Vram⟩ := by
  cases hR
  refine ⟨fun _ w _ => vOfH D0.R.toFrame (hP D0 (D0.what₂.places.resChar w)), fillsC D0 sc Ce Lc X hd c hcl,
    fun _ _ _ => ⟨rfl, rfl⟩, fun u v hg x s => fillsC_w D0 sc Ce Lc X hd c hcl u v hg x s, ?_⟩
  intro Lv Ch Vram L hsc hcc Xi hb hfill
  exact latTied_fillsC D0 sc Ce Lc X hd c hcl Lv Ch Vram L hsc hcc Xi hb hfill

end GlobalTheory.GyLat

namespace GlobalTheory.Mem.Top.Bl

open GlobalTheory.GyLat

set_option maxHeartbeats 4000000 in

theorem latLayer_free : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    (∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧
      ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L) →
    ∃ (vOf : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.HH (w.D Z) → Fin ((w.D Z).gat u v hg).P.nV)
      (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) ∧
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) ∧
      ∀ (Lv : ∀ u v hg, G.Levels (Fl u v hg)) (Ch : ∀ u v hg, G.Chain (Lv u v hg))
        (Vram : ∀ u v hg, Submodule ((w.D Z).gat u v hg).O ((w.D Z).gat u v hg).Fn)
        (L : SizeData₂ (w.D Z)), L.sc = K.s → WtEq L K.a K.b → Val K.C K.cD K.ch L → ∀ X : G.Inst (w.D Z) L, CanonInst X →
        G.EpDef X K.C.cX.Ce → G.KapIDef X K.C.GK → (∀ v, G.ParametersFill X K.C.GK v) →
        G.LatTied t.Gt X ⟨vOf, Fl, Lv, Ch, Vram⟩ := by
  intro K B f T w _ _ _ Z t Wt nch _ Y _ _ hcl
  obtain ⟨c, hcl, hcG⟩ := hcl
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, Tf, Bm, hBs, hB, iK, lam, hK, hPos, CH, eq⟩ := t.isRec
  have hR : (⟨w.D Z, t.Gt⟩ : Σ D : D7, GatTies D) =
      ⟨Formalism.L2.G.recC D0 K.s 1 Lc I ψ hd, Formalism.L2.G.gatTiesC D0 K.s 1 Lc I ψ hd⟩ :=
    congrArg (fun x => (⟨x.1, x.2.1⟩ : Σ D : D7, GatTies D)) eq
  obtain ⟨vOf, Fl, h1, h2, h3⟩ := latLayer_of_eq K.s (w.D Z) t.Gt D0 1 Lc (Formalism.L2.G.packC D0 Lc I ψ) hd hR c hcl
  refine ⟨vOf, Fl, h1, h2, ?_⟩
  intro Lv Ch Vram L hsc _ hV X hX _ _ hLF
  exact h3 Lv Ch Vram L hsc (hcG L hsc hV) X hX.1 (fun v => (hLF v).1)

end GlobalTheory.Mem.Top.Bl
