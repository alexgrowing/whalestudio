import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.IotaGlob

theorem mem_localLattice_inf_of_mem_span : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) (Λ : LV D),
    Submodule.IsLattice D.host.E Λ → ∀ y ∈ lattice₂ D Z.M p Λ,
    y ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → y ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) U) := by
  intro D Z p U Λ h y hy hs
  have e := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ U h.fg
  exact (Set.ext_iff.1 e y).2 ⟨hy, hs⟩

theorem O_eq {D : D7} (Z : LocDat D) (p : PlF D) : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1

theorem gS_unit : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (Z.M p).split = none →
    ∃ u ∈ (Z.M p).L.O, u * ((gS D : ℕ) : (D.s.atP p).Ep) = 1 := by
  intro D Z p hs
  refine ⟨(D.s.atP p).ιE (uP p : D.host.E), ?_, ?_⟩
  · rw [O_eq Z p]; exact Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p
  · rw [mul_comm, ← map_natCast (D.s.atP p).ιE]
    exact Formalism.L2.SG.Pf.StabIntSh.gS_mul_uP Z.δ Z.M Z.agree p hs

theorem gS_split : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g →
    ∃ u ∈ (Z.M p).L.O, ∃ v ∈ (Z.M p).L.O,
      ((gS D : ℕ) : (D.s.atP p).Ep) = u * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) ∧ u * v = 1 := by
  intro D Z p g hs
  have hagree := (Z.agree p).2.2.2.2.2
  rcases hs' : (D.s.atP p).split with _ | sg
  · rw [hs, hs'] at hagree; exact hagree.elim
  rw [hs, hs'] at hagree
  have hq : g.q = sg.q := hagree.2
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, (D.s.atP p).ιE (uP p : D.host.E), ?_, ?_, ?_⟩
  · rw [O_eq Z p, map_natCast]; exact natCast_mem _ _
  · rw [O_eq Z p]; exact Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hs']
    simp only [Nat.cast_mul, map_natCast]
    rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), mul_comm]
  · rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [mul_inv_cancel₀ h0, map_one]

end GlobalTheory.Unfold.IotaGlob

namespace GlobalTheory.Unfold.IotaGlob

variable {D : D7}

theorem mem_iff_loc (Z : LocDat D) (N : LV D) (hN : Submodule.IsLattice D.host.E N) (x : (VS D).V) :
    x ∈ N ↔ ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p N := by
  have h := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL N) (LatLoc.isLattice_map _ _ hN)).1 (LatLoc.cE D x)
  simp only [← LatLoc.localLattice_eq, ← LatLoc.baseChange_eq] at h
  refine Iff.trans ⟨fun hx => Submodule.mem_map_of_mem hx, fun hx => ?_⟩ h
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := (LatLoc.cE D).injective hyx
  exact this ▸ hy

theorem smul_mem_latP (Z : LocDat D) (p : PlF D) (Λ : LV D) {u : (D.s.atP p).Ep} (hu : u ∈ (Z.M p).L.O)
    {w : Vp D p} (hw : w ∈ lattice₂ D Z.M p Λ) : u • w ∈ lattice₂ D Z.M p Λ := by
  have := (lattice₂ D Z.M p Λ).smul_mem (⟨u, hu⟩ : (Z.M p).L.O) hw
  rwa [Subring.smul_def] at this

theorem baseChange_natCast_smul (p : PlF D) (n : ℕ) (x : (VS D).V) :
    baseChange₂ D p ((n : 𝓞 D.host.E) • x) = ((n : (D.s.atP p).Ep)) • baseChange₂ D p x := by
  rw [← algebraMap_smul D.host.E (n : 𝓞 D.host.E) x, map_natCast, baseChange_smul₂, map_natCast]

theorem gsmul_mem (Z : LocDat D) (p : PlF D) (Λ : LV D) {w : Vp D p} (hw : w ∈ lattice₂ D Z.M p Λ) :
    ((gS D : ℕ) : (D.s.atP p).Ep) • w ∈ lattice₂ D Z.M p (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  unfold lattice₂ at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    rw [← baseChange_natCast_smul]
    exact Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, smul_comm]
    exact smul_mem_latP Z p _ a.2 hx

theorem bcP_mem_X (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
    {f : Fin (D.R.rS + 1) → Vp D p} (hf : f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))
    {ξ : (VS D).V} (hξ : ξ ∈ Xsp G) : baseChange₂ D p ξ ∈ (locH Z p).X f := by
  subst hf
  have hξ' : ξ ∈ Submodule.span D.host.E (Set.range G.fl.e) := hξ
  clear hξ
  induction hξ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨u, hu⟩ := Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z p a.castSucc
    have e : baseChange₂ D p (G.fl.e a) =
        (↑u⁻¹ : (D.s.atP p).Ep) • (frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)) := by
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
      simp [frame, FlagG.fvec]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem X_le_span (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
    {f : Fin (D.R.rS + 1) → Vp D p} (hf : f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) :
    (locH Z p).X f ≤ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp G : Set (VS D).V)) := by
  subst hf
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨G.fl.e a, Submodule.subset_span ⟨a, rfl⟩, ?_⟩)
  simp [frame, FlagG.fvec]

theorem baseChange_mem_perp (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
    {f : Fin (D.R.rS + 1) → Vp D p} (hf : f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))
    {l : (VS D).V} (hl : l ∈ orth (VS D) (Xsp G)) : baseChange₂ D p l ∈ (locH Z p).perp ((locH Z p).X f) := by
  intro x hx
  have hx' := X_le_span Z p G hf hx
  clear hx
  have key : (locH Z p).h x (baseChange₂ D p l) = 0 := by
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ξ, hξ, rfl⟩ := hy
      rw [(locH Z p).h_herm]
      have h0 : (locH Z p).h (baseChange₂ D p l) (baseChange₂ D p ξ) = 0 := by
        show LocFacts₂ Z.M p (baseChange₂ D p l) (baseChange₂ D p ξ) = 0
        rw [baseChangeAt_form Z.M p (Z.hcj p)]
        have : (VS D).hT ξ l = 0 := (GlobalTheory.FrameProj.mem_orth_iff _ _).1 hl ξ hξ
        simp [brS, this]
      rw [h0, map_zero]
    | zero => exact (locH Z p).h_zero_left _
    | add x y _ _ hx hy => rw [(locH Z p).h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [(locH Z p).h_smul_left, hx, mul_zero]
  rw [(locH Z p).h_herm, key, map_zero]

theorem X_le_orth {T : D.host.E} (G : LFlag (VS D) D.R.rS T) : Xsp G ≤ orth (VS D) (Xsp G) := by
  intro y hy
  rw [GlobalTheory.FrameProj.mem_orth_iff]
  intro u hu
  have hu' : u ∈ Submodule.span D.host.E (Set.range G.fl.e) := hu
  have hy' : y ∈ Submodule.span D.host.E (Set.range G.fl.e) := hy
  clear hu hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    induction hu' using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact G.fl.e_iso a b
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul c x _ hx => simp [hx]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [hx]

theorem gS_ne : ((gS D : ℕ) : D.host.E) ≠ 0 := by
  have h0 := (D.host.g_prime 0).pos
  have h1 := (D.host.g_prime 1).pos
  have : 0 < gS D := Nat.mul_pos h0 h1
  exact_mod_cast this.ne'

theorem ngx_lattice {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D)
    (h : Submodule.IsLattice D.host.E Λ) : Submodule.IsLattice D.host.E (NgX Λ (gS D) F F') := by
  have hle : NgX Λ (gS D) F F' ≤ Λ := sup_le (sup_le Submodule.smul_le_right inf_le_left) inf_le_left
  refine ⟨h.fg.of_le hle, ?_⟩
  rw [eq_top_iff, ← h.span_eq_top]
  refine Submodule.span_le.2 fun v hv => ?_
  have hm : ((gS D : ℕ) : 𝓞 D.host.E) • v ∈ NgX Λ (gS D) F F' :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv))
  have e : v = ((gS D : ℕ) : D.host.E)⁻¹ • (((gS D : ℕ) : 𝓞 D.host.E) • v) := by
    rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) v, map_natCast, smul_smul, inv_mul_cancel₀ gS_ne, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem lrep_mem_lsub {T : D.host.E} {Λ : LV D} {G : LFlag (VS D) D.R.rS T} {l : (VS D).V}
    (hl : l ∈ Lrep Λ G) : l ∈ Lsub Λ G :=
  Submodule.mem_inf.2 ⟨Submodule.mem_sup_left hl, (Submodule.mem_inf.1 hl).2⟩

end GlobalTheory.Unfold.IotaGlob

namespace GlobalTheory.Unfold.IotaGlob
variable {D : D7}
theorem smulLat_mem (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (L : Submodule (Z.M p).L.O (Vp D p)) (w : Vp D p)
    (hw : w ∈ L) : c • w ∈ (locH Z p).smulLat c L := by
  unfold Loc.HermSp.smulLat; exact Submodule.subset_span ⟨w, hw, rfl⟩

theorem mem_iota (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (L : Submodule (Z.M p).L.O (Vp D p))
    (f f' : Fin (D.R.rS + 1) → Vp D p) (T T' : (D.s.atP p).Fp)
    (x' : (locH Z p).perp ((locH Z p).X f')) (x : (locH Z p).perp ((locH Z p).X f))
    (hx' : (x' : Vp D p) ∈ L) (hx : (x : Vp D p) ∈ L)
    (hxx : (x : Vp D p) - x' ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) L) :
    ((locH Z p).mkW f' x', (locH Z p).mkW f x) ∈ (locH Z p).iotaGraph g ⟨L, f, f', T, T'⟩ :=
  ⟨x', x, hx', hx, hxx, rfl⟩

theorem of_mem_iota (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (L : Submodule (Z.M p).L.O (Vp D p))
    (f f' : Fin (D.R.rS + 1) → Vp D p) (T T' : (D.s.atP p).Fp)
    (x' : (locH Z p).perp ((locH Z p).X f')) (x : (locH Z p).perp ((locH Z p).X f))
    (h : ((locH Z p).mkW f' x', (locH Z p).mkW f x) ∈ (locH Z p).iotaGraph g ⟨L, f, f', T, T'⟩) :
    ∃ y' : (locH Z p).perp ((locH Z p).X f'), ∃ y : (locH Z p).perp ((locH Z p).X f),
      (y' : Vp D p) ∈ L ∧ (y : Vp D p) ∈ L ∧
      (y : Vp D p) - y' ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) L ∧
      (x' : Vp D p) - y' ∈ (locH Z p).X f' ∧ (x : Vp D p) - y ∈ (locH Z p).X f := by
  obtain ⟨y', y, hy', hy, hyy, heq⟩ := h
  obtain ⟨e1, e2⟩ := Prod.mk.inj heq
  refine ⟨y', y, hy', hy, hyy, ?_, ?_⟩
  · have := (Submodule.Quotient.eq _).1 e1
    simpa using this
  · have := (Submodule.Quotient.eq _).1 e2
    simpa using this

theorem of_mem_iota2 (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (L₁ L₂ : Submodule (Z.M p).L.O (Vp D p))
    (f f' : Fin (D.R.rS + 1) → Vp D p) (T T' : (D.s.atP p).Fp) (x' x : Vp D p)
    (hx' : x' ∈ (locH Z p).perp ((locH Z p).X f')) (hx : x ∈ (locH Z p).perp ((locH Z p).X f))
    (hI : (locH Z p).iotaGraph g ⟨L₁, f, f', T, T'⟩ = (locH Z p).iotaGraph g ⟨L₂, f, f', T, T'⟩)
    (h1 : x' ∈ L₁) (h2 : x ∈ L₁)
    (h3 : x - x' ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) L₁) :
    ∃ y' y : Vp D p, y' ∈ L₂ ∧ y ∈ L₂ ∧
      y - y' ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) L₂ ∧
      x' - y' ∈ (locH Z p).X f' ∧ x - y ∈ (locH Z p).X f := by
  have h := mem_iota Z p g L₁ f f' T T' ⟨x', hx'⟩ ⟨x, hx⟩ h1 h2 h3
  rw [hI] at h
  obtain ⟨y', y, h1, h2, h3, h4, h5⟩ := of_mem_iota Z p g L₂ f f' T T' ⟨x', hx'⟩ ⟨x, hx⟩ h
  exact ⟨y', y, h1, h2, h3, h4, h5⟩

theorem bc1 (p : PlF D) (a c d : (VS D).V) (y : Vp D p) :
    baseChange₂ D p a - y = baseChange₂ D p (d - c) + (baseChange₂ D p (a + c - d) - y) := by
  simp only [map_sub, map_add]; abel

theorem bc2 (p : PlF D) (a c d : (VS D).V) (y : Vp D p) :
    baseChange₂ D p a - y = baseChange₂ D p (-(d + c)) + (baseChange₂ D p (a + c + d) - y) := by
  simp only [map_neg, map_add]; abel

theorem bc3 (p : PlF D) (a a' : (VS D).V) (y y' : Vp D p) :
    baseChange₂ D p (a - a') = (baseChange₂ D p a - y) - (baseChange₂ D p a' - y') + (y - y') := by
  rw [map_sub]; abel

theorem mem_of_baseChangeAtPlace_split_difference_mem (p : PlF D) (a c d : (VS D).V) (y : Vp D p) (S : Submodule (D.s.atP p).Ep (Vp D p))
    (h : baseChange₂ D p (d - c) + (baseChange₂ D p (a + c - d) - y) ∈ S) : baseChange₂ D p a - y ∈ S := by
  rw [bc1 p a c d y]; exact h

theorem mem_of_baseChangeAtPlace_split_negSum_mem (p : PlF D) (a c d : (VS D).V) (y : Vp D p) (S : Submodule (D.s.atP p).Ep (Vp D p))
    (h : baseChange₂ D p (-(d + c)) + (baseChange₂ D p (a + c + d) - y) ∈ S) : baseChange₂ D p a - y ∈ S := by
  rw [bc2 p a c d y]; exact h

theorem smulLat_le_g (Z : LocDat D) (p : PlF D) (c u v : (D.s.atP p).Ep) (hv : v ∈ (Z.M p).L.O)
    (hg : ((gS D : ℕ) : (D.s.atP p).Ep) = u * c) (huv : u * v = 1) (Λ : LV D) (w : Vp D p)
    (hw : w ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ)) :
    w ∈ lattice₂ D Z.M p (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  unfold Loc.HermSp.smulLat at hw
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨z, hz, rfl⟩
  have e : c • z = v • (((gS D : ℕ) : (D.s.atP p).Ep) • z) := by
    rw [hg, smul_smul, ← mul_assoc, mul_comm v u, huv, one_mul]
  show c • z ∈ _
  rw [e]
  exact smul_mem_latP Z p _ hv (gsmul_mem Z p Λ hz)

theorem baseChangeAtPlace_sub_mem_of_three_mem (Z : LocDat D) (p : PlF D) (a a' : (VS D).V) (y y' : Vp D p) (S : Submodule (Z.M p).L.O (Vp D p))
    (h1 : baseChange₂ D p a - y ∈ S) (h2 : baseChange₂ D p a' - y' ∈ S) (h3 : y - y' ∈ S) : baseChange₂ D p (a - a') ∈ S := by
  rw [bc3 p a a' y y']; exact add_mem (sub_mem h1 h2) h3
end GlobalTheory.Unfold.IotaGlob

namespace GlobalTheory.Unfold.IotaGlob

variable {D : D7}

set_option maxHeartbeats 1000000 in
theorem graph_sub (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (Λ₁ Λ₂ : LV D)
    (h₂ : Submodule.IsLattice D.host.E Λ₂) (hL : Lsub Λ₁ F = Lsub Λ₂ F) (hL' : Lsub Λ₁ F' = Lsub Λ₂ F')
    (hI : ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g →
      (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ =
      (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) :
    (gdat F F' Λ₁).2.2 ⊆ (gdat F F' Λ₂).2.2 := by
  rintro ⟨p₁, p₂⟩ ⟨l', hl', l, hl, hp₁, hp₂, hll⟩
  obtain ⟨l₂, hl₂, t, ht, rfl⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 (hL ▸ lrep_mem_lsub hl)).1
  obtain ⟨l'₂, hl'₂, t', ht', rfl⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 (hL' ▸ lrep_mem_lsub hl')).1
  refine ⟨l'₂, hl'₂, l₂, hl₂, ?_, ?_, ?_⟩
  · have e : p₁ - l'₂ = (p₁ - (l'₂ + t')) + t' := by abel
    rw [e]; exact add_mem hp₁ ht'
  · have e : p₂ - l₂ = (p₂ - (l₂ + t)) + t := by abel
    rw [e]; exact add_mem hp₂ ht
  · rw [mem_iff_loc Z _ (ngx_lattice F F' Λ₂ h₂)]
    intro p
    have hΛl₂ : l₂ ∈ Λ₂ := (Submodule.mem_inf.1 hl₂).1
    have hΛl'₂ : l'₂ ∈ Λ₂ := (Submodule.mem_inf.1 hl'₂).1
    have hw : baseChange₂ D p (l₂ - l'₂) ∈ lattice₂ D Z.M p Λ₂ := Submodule.subset_span ⟨_, sub_mem hΛl₂ hΛl'₂, rfl⟩
    have hgle : lattice₂ D Z.M p (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ₂) ≤
        lattice₂ D Z.M p (NgX Λ₂ (gS D) F F') :=
      GlobalTheory.FrameProj.localLattice_mono Z p (le_sup_left.trans le_sup_left)
    cases hs : (Z.M p).split with
    | none =>
      obtain ⟨u, hu, hug⟩ := gS_unit D Z p hs
      have e : baseChange₂ D p (l₂ - l'₂) = ((gS D : ℕ) : (D.s.atP p).Ep) • (u • baseChange₂ D p (l₂ - l'₂)) := by
        rw [smul_smul, mul_comm, hug, one_smul]
      rw [e]
      exact hgle (gsmul_mem Z p Λ₂ (smul_mem_latP Z p Λ₂ hu hw))
    | some g =>
      obtain ⟨u, hu, v, hv, hg, huv⟩ := gS_split D Z p g hs
      obtain ⟨ab, hab, ξ', hξ', habξ⟩ := Submodule.mem_sup.1 hll
      obtain ⟨a, ha, ξ, hξ, haξ⟩ := Submodule.mem_sup.1 hab
      rw [Submodule.ideal_span_singleton_smul] at ha
      obtain ⟨lam, hlam, hlamE⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
      have hA := (hB p).1
      have hBf := (hB p).2.1
      have hlΛ : l₂ + t ∈ Λ₁ := (Submodule.mem_inf.1 hl).1
      have hl'Λ : l'₂ + t' ∈ Λ₁ := (Submodule.mem_inf.1 hl').1
      have hξΛ : ξ ∈ Λ₁ := (Submodule.mem_inf.1 hξ).1
      have hξ'Λ : ξ' ∈ Λ₁ := (Submodule.mem_inf.1 hξ').1
      have hξX : ξ ∈ Xsp F := (Submodule.mem_inf.1 hξ).2
      have hξ'X : ξ' ∈ Xsp F' := (Submodule.mem_inf.1 hξ').2
      have hxO : l₂ + t - ξ ∈ orth (VS D) (Xsp F) := sub_mem (Submodule.mem_inf.1 hl).2 (X_le_orth F hξX)
      have hx'O : l'₂ + t' + ξ' ∈ orth (VS D) (Xsp F') := add_mem (Submodule.mem_inf.1 hl').2 (X_le_orth F' hξ'X)
      have hxP := baseChange_mem_perp Z p F hA hxO
      have hx'P := baseChange_mem_perp Z p F' hBf hx'O
      have hxΛ : baseChange₂ D p (l₂ + t - ξ) ∈ lattice₂ D Z.M p Λ₁ := Submodule.subset_span ⟨_, sub_mem hlΛ hξΛ, rfl⟩
      have hx'Λ : baseChange₂ D p (l'₂ + t' + ξ') ∈ lattice₂ D Z.M p Λ₁ := Submodule.subset_span ⟨_, add_mem hl'Λ hξ'Λ, rfl⟩
      have hxx : baseChange₂ D p (l₂ + t - ξ) - baseChange₂ D p (l'₂ + t' + ξ') ∈ (locH Z p).smulLat
          (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ₁) := by
        have e1 : l₂ + t - ξ - (l'₂ + t' + ξ') = a := by
          have : l₂ + t - ξ - (l'₂ + t' + ξ') = (l₂ + t - (l'₂ + t')) - ξ - ξ' := by abel
          rw [this, ← habξ, ← haξ]; abel
        rw [← map_sub, e1, ← hlamE, baseChange_natCast_smul, hg, mul_comm, mul_smul]
        exact smulLat_mem Z p _ _ _ (smul_mem_latP Z p Λ₁ hu (Submodule.subset_span ⟨lam, hlam, rfl⟩))
      have hm1 := of_mem_iota2 Z p g (lattice₂ D Z.M p Λ₁) (lattice₂ D Z.M p Λ₂)
        (FP p).A.f (FP p).B.f (FP p).A.T (FP p).B.T _ _ hx'P hxP (hI p g hs) hx'Λ hxΛ hxx
      clear hI
      obtain ⟨y', y, hy'Λ, hyΛ, hyy, hx'y', hxy⟩ := hm1
      have hd1 : baseChange₂ D p l₂ - y ∈ lattice₂ D Z.M p Λ₂ := sub_mem (Submodule.subset_span ⟨l₂, hΛl₂, rfl⟩) hyΛ
      have hd2 := X_le_span Z p F hA (add_mem (bcP_mem_X Z p F hA (sub_mem hξX ht)) hxy)
      have hd : baseChange₂ D p l₂ - y ∈ lattice₂ D Z.M p (XLam Λ₂ F) :=
        mem_localLattice_inf_of_mem_span D Z p (Xsp F) Λ₂ h₂ _ hd1 (mem_of_baseChangeAtPlace_split_difference_mem p l₂ t ξ y _ hd2)
      have hd1' : baseChange₂ D p l'₂ - y' ∈ lattice₂ D Z.M p Λ₂ := sub_mem (Submodule.subset_span ⟨l'₂, hΛl'₂, rfl⟩) hy'Λ
      have hd2' := X_le_span Z p F' hBf (add_mem (bcP_mem_X Z p F' hBf (neg_mem (add_mem hξ'X ht'))) hx'y')
      have hd' : baseChange₂ D p l'₂ - y' ∈ lattice₂ D Z.M p (XLam Λ₂ F') :=
        mem_localLattice_inf_of_mem_span D Z p (Xsp F') Λ₂ h₂ _ hd1' (mem_of_baseChangeAtPlace_split_negSum_mem p l'₂ t' ξ' y' _ hd2')
      exact baseChangeAtPlace_sub_mem_of_three_mem Z p l₂ l'₂ y y' _ (GlobalTheory.FrameProj.localLattice_mono Z p (le_sup_right.trans le_sup_left) hd)
        (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_right hd') (hgle (smulLat_le_g Z p _ u v hv hg huv Λ₂ _ hyy))

theorem graph_eq_of_local_iota : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 := by
  intro D Z FP Tn T'n F F' hB Λ₁ Λ₂ h₁ h₂ hL hL' hI
  exact Set.Subset.antisymm (graph_sub Z FP Tn T'n F F' hB Λ₁ Λ₂ h₂ hL hL' hI)
    (graph_sub Z FP Tn T'n F F' hB Λ₂ Λ₁ h₁ hL.symm hL'.symm fun p g hs => (hI p g hs).symm)

end GlobalTheory.Unfold.IotaGlob
