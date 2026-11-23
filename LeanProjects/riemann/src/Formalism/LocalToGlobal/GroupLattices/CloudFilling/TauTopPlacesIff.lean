import Formalism.LocalToGlobal.GroupLattices.CloudFilling.WLeWjOne
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.InstRecFillG
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.GatRecStepFrob

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LatticeCompatibleAt {D : D7} {L : SizeData₂ D} (X : Inst D L) {p : ℕ} (G : GAtP p)
    (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau) (vOf : HH D → Fin G.P.nV) (Fl : Fills G) : Prop :=
  Fl.mm = D.R.m ∧ Fl.t = D.R.t ∧
  (Fl.c : ℝ) ≤ cG L ∧
  G.P.r = (if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1) ∧
  Set.InjOn vOf (reps X p) ∧
  (∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (t : HH D),
    ((D.eTau (pos ⟨v, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau2 t →
      s ∉ Fl.TT v ∧ ∀ j ∈ SizeData₂.lifts D, (Fl.w v j s : ℝ) = fillG X (bL L) j (true, t)) ∧
  ∀ t0 ∈ reps X p,
    G.P.n' (vOf t0) = addOrderOf (hP D p) ∧
    ∀ s : Fin (G.P.n' (vOf t0)),
      ((D.eTau (pos ⟨vOf t0, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau1 (t0 + s.val • hP D p) ∧
      (s ∈ Fl.TT (vOf t0) ↔ t0 + s.val • hP D p ∈ D.host.TT) ∧
      (s ∈ Fl.TT (vOf t0) →
        Fl.a (vOf t0) s = aL L (t0 + s.val • hP D p) ∧
        Fl.b (vOf t0) s = bL L (t0 + s.val • hP D p)) ∧
      ∀ j ∈ SizeData₂.lifts D,
        (Fl.w (vOf t0) j s : ℝ) = fillG X (bL L) j (false, t0 + s.val • hP D p)

theorem latTied_iff {D : D7} {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) :
    LatTied hT X Y ↔ ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      LatticeCompatibleAt X (D.gat u w hg) (hT.gat_pos u w hg) (Y.vOf u w hg) (Y.Fl u w hg) := Iff.rfl

def rRec {D : D7} (L : SizeData₂ D) (p : ℕ) : ℕ := if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1

theorem tau_top_places_iff (D : D7) (t : HH D) : D.R.tau1 t ∈ D.host.topPlaces ↔ t ∈ D.host.TT := by
  rw [← Formalism.MainNotions.Inhab.plGG_false, Formalism.MainNotions.Inhab.plGG_top_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem tau_coe_val (φ : Formalism.HC.Frame) (t : φ.A) : ((tau1P φ t : φ.Psi) : φ.GG) = φ.tau1 t := rfl

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem latTiedAt_rec {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (K : Consts) (Ce : ℝ) (u : D.what₂.Word)
    (hc : IsResidueClassZero D p) (hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w) (r : ℕ) (hr : r = rRec L p)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId Lc p (nOrb (zH D.R.toFrame (hP D p))) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* Oˣ)
    (y : compL Lc p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) :
    LatticeCompatibleAt (instRec L K Ce) (gatRec D u (D.R.iota (hP D p)) hS r Lc I ψ y e)
      (gatRec_pos D u (D.R.iota (hP D p)) hS r Lc I ψ y e) (vOfH D.R.toFrame (hP D p))
      (fillsRec D u (D.R.iota (hP D p)) hS r Lc I ψ y e (cRec L) (cloudBound L P u)) := by
  subst hr
  refine ⟨rfl, rfl, cRec_le L, rfl, ?_, ?_, ?_⟩
  · rw [reps_instRec L K Ce hc]
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
      rw [instRec_fill L K Ce jj hj (D.eTau.symm (posG (zH D.R.toFrame (hP D p)) ⟨v, s⟩)) (true, t)
        (by rw [Equiv.apply_symm_apply, ht', Formalism.MainNotions.Inhab.plGG_true])]
  · intro t0 ht0
    have ht0' : t0 ∈ Set.range (bsH D.R.toFrame (hP D p)) := by
      rw [← reps_instRec L K Ce hc]; exact ht0
    obtain ⟨x, rfl⟩ := ht0'
    refine ⟨orderOf_zH _ _, fun s => ?_⟩
    have hpos : posG (zH D.R.toFrame (hP D p)) ⟨vOfH D.R.toFrame (hP D p) (bsH D.R.toFrame (hP D p) x), s⟩ =
        tau1P D.R.toFrame (bsH D.R.toFrame (hP D p) x + s.val • hP D p) := by
      rw [posG_vOfH, bsH_idem]
    have hmem : (s ∈ (fillsRec D u (D.R.iota (hP D p)) hS (rRec L p) Lc I ψ y e (cRec L)
        (cloudBound L P u)).TT (vOfH D.R.toFrame (hP D p) (bsH D.R.toFrame (hP D p) x))) ↔
        bsH D.R.toFrame (hP D p) x + s.val • hP D p ∈ D.host.TT := by
      rw [← tau_top_places_iff]
      show s ∈ Finset.univ.filter _ ↔ _
      rw [Finset.mem_filter, hpos]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    have ha : (fillsRec D u (D.R.iota (hP D p)) hS (rRec L p) Lc I ψ y e (cRec L)
        (cloudBound L P u)).a (vOfH D.R.toFrame (hP D p) (bsH D.R.toFrame (hP D p) x)) s =
        aL L (bsH D.R.toFrame (hP D p) x + s.val • hP D p) := by
      show (if ((posG (zH D.R.toFrame (hP D p)) _ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces then
        lamRec D u (posG (zH D.R.toFrame (hP D p)) _) 0 else 0) = _
      rw [hpos, tau_coe_val]
      unfold aL
      by_cases ht : bsH D.R.toFrame (hP D p) x + s.val • hP D p ∈ D.host.TT
      · rw [if_pos ((tau_top_places_iff D _).2 ht), dif_pos ht]
        exact (lamRec_top L u _ ⟨_, ht⟩ rfl).1
      · rw [if_neg (fun h => ht ((tau_top_places_iff D _).1 h)), dif_neg ht]
    have hb : (fillsRec D u (D.R.iota (hP D p)) hS (rRec L p) Lc I ψ y e (cRec L)
        (cloudBound L P u)).b (vOfH D.R.toFrame (hP D p) (bsH D.R.toFrame (hP D p) x)) s =
        bL L (bsH D.R.toFrame (hP D p) x + s.val • hP D p) := by
      show (if ((posG (zH D.R.toFrame (hP D p)) _ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces then
        -lamRec D u (posG (zH D.R.toFrame (hP D p)) _) (Fin.last _) else 0) = _
      rw [hpos, tau_coe_val]
      unfold bL
      by_cases ht : bsH D.R.toFrame (hP D p) x + s.val • hP D p ∈ D.host.TT
      · rw [if_pos ((tau_top_places_iff D _).2 ht), dif_pos ht, (lamRec_top L u _ ⟨_, ht⟩ rfl).2, neg_neg]
      · rw [if_neg (fun h => ht ((tau_top_places_iff D _).1 h)), dif_neg ht]
    refine ⟨?_, hmem, fun _ => ⟨ha, hb⟩, fun jj hj => ?_⟩
    · show ((D.eTau (D.eTau.symm (posG (zH D.R.toFrame (hP D p)) _)) : D.R.Psi) : D.R.GG) = _
      rw [Equiv.apply_symm_apply, hpos]
      rfl
    · show ((wRec D u (posG (zH D.R.toFrame (hP D p)) _) jj : ℤ) : ℝ) = _
      rw [hpos, wRec_eq D u _ jj hj, instRec_fillG L K Ce jj hj]

end Formalism.L2.G
