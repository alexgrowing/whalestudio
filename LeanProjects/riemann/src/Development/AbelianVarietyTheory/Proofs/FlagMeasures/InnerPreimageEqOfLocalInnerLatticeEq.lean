import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.LsubG

variable {D : D7}

theorem exists_proj (X : Submodule D.host.E (VS D).V) :
    ∃ Q : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ X, Q x = 0) ∧ (∀ v, v - Q v ∈ X) ∧ ∀ v, Q (Q v) = Q v := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl X
  have hC' : IsCompl C X := hC.symm
  refine ⟨C.projection X hC', fun x hx => (Submodule.projection_apply_eq_zero_iff hC').2 hx, fun v => ?_, fun v => ?_⟩
  · rw [← Submodule.projection_eq_self_sub_projection hC']
    exact Submodule.projection_apply_mem _ _
  · exact Submodule.projection_apply_of_mem_left hC' (Submodule.projection_apply_mem _ _)

def endP (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
  Fintype.linearCombination (D.s.atP p).Ep (fun i => baseChange₂ D p (Q ((VS D).frame i)))

theorem bcP_endP (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    endP p Q (baseChange₂ D p x) = baseChange₂ D p (Q x) := by
  rw [endP, Fintype.linearCombination_apply]
  conv_rhs => rw [← (VS D).frame.sum_repr x]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, baseChange_smul₂]
  rfl

theorem endP_latP (Z : LocDat D) (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) (Λ : LV D) {y : Vp D p}
    (hy : y ∈ lattice₂ D Z.M p Λ) : endP p Q y ∈ lattice₂ D Z.M p (Λ.map (Q.restrictScalars (𝓞 D.host.E))) := by
  refine Submodule.span_induction (p := fun y _ => endP p Q y ∈ lattice₂ D Z.M p (Λ.map (Q.restrictScalars (𝓞 D.host.E))))
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨x, hx, rfl⟩
    rw [bcP_endP]
    exact Submodule.subset_span ⟨Q x, Submodule.mem_map_of_mem hx, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have e : endP p Q (c • a) = c • endP p Q a := by
      rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ c ha

theorem localLattice_mono' (Z : LocDat D) (p : PlF D) {Λ Λ' : LV D} (h : Λ ≤ Λ') : lattice₂ D Z.M p Λ ≤ lattice₂ D Z.M p Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_of_local (Z : LocDat D) (Γ : LV D) (hΓ : Submodule.IsLattice D.host.E Γ) (x : (VS D).V)
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Γ) : x ∈ Γ := by
  have r := ((GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Γ) (LatLoc.isLattice_map _ _ hΓ)).1
    (LatLoc.cE D x)).2 (fun p => by rw [← LatLoc.baseChange_eq, ← LatLoc.localLattice_eq]; exact h p)
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.1 r
  have : y = x := (LatLoc.cE D).injective hxy
  exact this ▸ hy

theorem herm_smul_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (c : E) (u w : V) : H.h u (c • w) = M.L.cj c * H.h u w := by
  rw [H.h_herm (c • w) u, H.h_smul_left, map_mul, ← H.h_herm w u]

theorem herm_span_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (u : V) (S : Set V) (hS : ∀ s ∈ S, H.h u s = 0) :
    ∀ w ∈ Submodule.span E S, H.h u w = 0 := by
  intro w hw
  refine Submodule.span_induction (p := fun w _ => H.h u w = 0) hS ?_ ?_ ?_ hw
  · rw [H.h_herm 0 u, H.h_zero_left, map_zero]
  · intro a b _ _ ha hb
    rw [H.h_herm (a + b) u, H.h_add_left, map_add, ← H.h_herm a u, ← H.h_herm b u, ha, hb, add_zero]
  · intro c a _ ha
    rw [herm_smul_right, ha, mul_zero]

theorem X_iso {T : D.host.E} (G : LFlag (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ Xsp G) :
    x ∈ orth (VS D) (Xsp G) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y hy
  have hgen : ∀ b, (VS D).hT y (G.fl.e b) = 0 := by
    intro b
    refine Submodule.span_induction (p := fun y _ => (VS D).hT y (G.fl.e b) = 0) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨a, rfl⟩; exact G.fl.e_iso a b
    · simp
    · intro a c _ _ ha hc; simp [ha, hc]
    · intro c a _ ha; simp [ha]
  refine Submodule.span_induction (p := fun x _ => (VS D).hT y x = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩; exact hgen b
  · simp
  · intro a c _ _ ha hc; simp [ha, hc]
  · intro c a _ ha; simp [ha]

example (Λ : LV D) (h : Submodule.IsLattice D.host.E Λ) : Λ.FG ∧ Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ :=
  ⟨h.fg, h.span_eq_top⟩

set_option maxHeartbeats 1000000 in
theorem lsub_le (Z : LocDat D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
    (f : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p)
    (hf : ∀ p, f p = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) (Λ₁ Λ₂ : LV D)
    (h₂ : Submodule.IsLattice D.host.E Λ₂)
    (hL : ∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (f p) ⊆ (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (f p)) :
    Lsub Λ₁ G ≤ Lsub Λ₂ G := by
  obtain ⟨Q, hQX, hQv, hQQ⟩ := exists_proj (Xsp G)
  set Γ : LV D := Λ₂ ⊔ Λ₂.map (Q.restrictScalars (𝓞 D.host.E)) with hΓdef
  have hΓ : Submodule.IsLattice D.host.E Γ :=
    ⟨h₂.fg.sup (h₂.fg.map _), eq_top_iff.2 (h₂.span_eq_top.symm.le.trans (Submodule.span_mono (show (Λ₂ : Set (VS D).V) ⊆ Γ from fun z hz => Submodule.mem_sup_left hz)))⟩
  intro v hv
  have hvo : v ∈ orth (VS D) (Xsp G) := hv.2
  obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 hv.1
  have hlo : l ∈ orth (VS D) (Xsp G) := hl.2
  have hloc : ∀ p, baseChange₂ D p (Q (l + x)) ∈ lattice₂ D Z.M p Γ := by
    intro p
    have hXQ : ∀ w ∈ (locH Z p).X (f p), endP p Q w = 0 := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => endP p Q w = 0) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨a, rfl⟩
        rw [hf p]
        simp only
        rw [map_smul, bcP_endP, hQX _ (Submodule.subset_span ⟨a, by simp [frame, FlagG.fvec]⟩), map_zero, smul_zero]
      · exact map_zero _
      · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
      · intro c a _ ha; rw [map_smul, ha, smul_zero]
    have hperp : baseChange₂ D p l ∈ (locH Z p).perp ((locH Z p).X (f p)) := by
      intro w hw
      refine herm_span_right (locH Z p) (baseChange₂ D p l) _ ?_ w hw
      rintro _ ⟨a, rfl⟩
      rw [hf p]
      simp only
      rw [herm_smul_right]
      have e0 : (locH Z p).h (baseChange₂ D p l) (baseChange₂ D p (frame G a.castSucc)) = 0 := by
        show LocFacts₂ Z.M p (baseChange₂ D p l) (baseChange₂ D p (frame G a.castSucc)) = 0
        rw [baseChangeAt_form Z.M p (Z.hcj p), brS]
        have hmem : frame G a.castSucc ∈ Xsp G := Submodule.subset_span ⟨a, by simp [frame, FlagG.fvec]⟩
        have := hlo
        simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this
        rw [this _ hmem, map_zero]
      rw [e0, mul_zero]
    obtain ⟨y, hy, hyw⟩ := hL p ⟨⟨baseChange₂ D p l, hperp⟩, Submodule.subset_span ⟨l, hl.1, rfl⟩, rfl⟩
    have hdiff : ((y : Vp D p) - baseChange₂ D p l) ∈ (locH Z p).X (f p) := by
      have := (Submodule.Quotient.eq _).1 hyw
      simpa using this
    have e : endP p Q (baseChange₂ D p l) = endP p Q y := by
      have := hXQ _ hdiff
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    rw [← bcP_endP, map_add, map_add, e, bcP_endP p Q x, hQX x hx, map_zero, add_zero]
    exact localLattice_mono' Z p (le_sup_right : Λ₂.map (Q.restrictScalars (𝓞 D.host.E)) ≤ Γ) (endP_latP Z p Q Λ₂ hy)
  have hmem : Q (l + x) ∈ Γ := mem_of_local Z Γ hΓ _ hloc
  obtain ⟨a, ha, b', hb', hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hb'
  have hQab : Q a + Q b = Q (l + x) := by
    have := congrArg Q hab
    simp only [LinearMap.restrictScalars_apply, map_add, hQQ] at this
    rw [map_add Q l x]
    exact this
  have h2 : Q (l + x - (a + b)) = 0 := by
    rw [map_sub Q, map_add Q a b, hQab, sub_self]
  have hc : l + x - (a + b) ∈ Xsp G := by
    have h1 := hQv (l + x - (a + b))
    rw [h2, sub_zero] at h1
    exact h1
  have hco : a + b ∈ orth (VS D) (Xsp G) := by
    have : a + b = (l + x) - (l + x - (a + b)) := by abel
    rw [this]
    exact Submodule.sub_mem _ hvo (X_iso G hc)
  refine ⟨Submodule.mem_sup.2 ⟨a + b, ⟨Submodule.add_mem _ ha hb, hco⟩, l + x - (a + b), hc, by abel⟩, hvo⟩

theorem lsub_eq_of_local : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := by
  intro D Z T G Fr hFr Λ₁ Λ₂ h₁ h₂ hL
  exact le_antisymm
    (lsub_le Z G (fun p => (Fr p).f) hFr Λ₁ Λ₂ h₂ fun p => (hL p).le)
    (lsub_le Z G (fun p => (Fr p).f) hFr Λ₂ Λ₁ h₁ fun p => (hL p).ge)

end GlobalTheory.Unfold.LsubG
