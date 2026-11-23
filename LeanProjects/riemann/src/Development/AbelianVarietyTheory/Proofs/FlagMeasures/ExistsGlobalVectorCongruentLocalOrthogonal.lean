import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocApprox

theorem iota_gS_typed {D : D7} (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w := by
  obtain ⟨sg, hsg, hq, -⟩ := Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.typed_data Z p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]

end GlobalTheory.LocApprox

namespace GlobalTheory.LocApprox

set_option maxHeartbeats 1000000 in

theorem approx : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O, c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → ∀ {T : D.host.E} (F : LFlag (VS D) D.R.rS T), ∀ x ∈ lattice₂ D Z.M p Λ, x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) → ∃ l ∈ Lrep Λ F, x - baseChange₂ D p l ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))) (lattice₂ D Z.M p Λ) := by
  intro D Z p hc Λ hΛ T F x hx hxp
  have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
  rcases hs : (Z.M p).split with _ | g
  · refine ⟨0, zero_mem _, ?_⟩
    have ht : Formalism.MainNotions.S.LocNG.theta (Z.M p) = 1 := by simp [Formalism.MainNotions.S.LocNG.theta, hs]
    rw [ht, map_one, map_zero, sub_zero]
    exact Submodule.subset_span ⟨x, hx, one_smul _ _⟩
  · have ht : Formalism.MainNotions.S.LocNG.theta (Z.M p) = (g.q : (D.s.atP p).Fp) := by simp [Formalism.MainNotions.S.LocNG.theta, hs]
    obtain ⟨w, hw, he⟩ := iota_gS_typed Z p g hs
    rw [ht]
    have hspan := GlobalTheory.LocExt.perp_le Z p F hxp
    have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (orth (VS D) (Xsp F)) hΛ.fg
    have hxL : x ∈ lattice₂ D Z.M p (Lrep Λ F) := by
      have : x ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) (Xsp F))) : Set (Vp D p)) := by
        rw [hsat]; exact ⟨hx, hspan⟩
      exact this
    clear hx hxp hspan hsat
    induction hxL using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact ⟨l, hl, by rw [sub_self]; exact zero_mem _⟩
    | zero => exact ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
    | add u v _ _ ihu ihv =>
      obtain ⟨l, hl, h⟩ := ihu
      obtain ⟨l', hl', h'⟩ := ihv
      refine ⟨l + l', add_mem hl hl', ?_⟩
      rw [map_add, show u + v - (baseChange₂ D p l + baseChange₂ D p l') = (u - baseChange₂ D p l) + (v - baseChange₂ D p l') by abel]
      exact add_mem h h'
    | smul o v _ ih =>
      obtain ⟨l, hl, h⟩ := ih
      have ho : (o : (D.s.atP p).Ep) ∈ (D.s.atP p).O := hO ▸ o.2
      obtain ⟨a, o', ho', hco⟩ := hc _ ho
      refine ⟨a • l, Submodule.smul_mem _ a hl, ?_⟩
      have hbl : baseChange₂ D p l ∈ lattice₂ D Z.M p Λ := Submodule.subset_span ⟨l, hl.1, rfl⟩
      have e1 : baseChange₂ D p (a • l) = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l := by
        rw [← baseChange_smul₂]; congr 1; exact (algebraMap_smul D.host.E a l).symm
      have key : ∀ (oo ia ig th : (D.s.atP p).Ep) (vv b : Vp D p), oo = ia + ig * o' → ig = th * w →
          oo • vv - ia • b = oo • (vv - b) + th • ((w * o') • b) := by
        intro oo ia ig th vv b h1 h2
        subst h1 h2
        simp only [smul_sub, add_smul, smul_smul, ← mul_assoc]
        abel
      have hov : o • v = (o : (D.s.atP p).Ep) • v := rfl
      have hob : (o : (D.s.atP p).Ep) • (v - baseChange₂ D p l) ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) :=
        Submodule.smul_mem _ o h
      have hwo : w * o' ∈ (Z.M p).L.O := hO ▸ mul_mem hw ho'
      have k1 := key (o : (D.s.atP p).Ep) _ _ _ v (baseChange₂ D p l) hco he
      have h3 : (w * o') • baseChange₂ D p l ∈ lattice₂ D Z.M p Λ := (lattice₂ D Z.M p Λ).smul_mem ⟨_, hwo⟩ hbl
      have h4 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • ((w * o') • baseChange₂ D p l) ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) :=
        Submodule.subset_span ⟨_, h3, rfl⟩
      have h5 : (o : (D.s.atP p).Ep) • v - (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) := by
        rw [k1]; exact add_mem hob h4
      have h6 : o • v - baseChange₂ D p (a • l) = (o : (D.s.atP p).Ep) • v - (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l := by
        rw [hov, e1]
      rw [h6]
      exact h5

end GlobalTheory.LocApprox
