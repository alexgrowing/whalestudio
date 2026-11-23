import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameSpanLat

variable {D : D7}

theorem localComplementUnitary_fixes_both_frames {Z : LocDat D} {p : PlF D} (P : LocNG.FPair (locH Z p) D.R.rS)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ P.UW0) :
    ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact fun _ => ⟨rfl, rfl⟩
  | mul x y _ _ hx hy =>
    intro b
    change x (y _) = _ ∧ x (y _) = _
    rw [(hy b).1, (hy b).2]; exact hx b
  | inv x _ hx =>
    intro b
    refine ⟨?_, ?_⟩
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq, (hx b).1]
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq, (hx b).2]

theorem h_zero_left {Z : LocDat D} {p : PlF D} (y : Vp D p) : (locH Z p).h 0 y = 0 := by
  show LocFacts₂ Z.M p 0 y = 0
  simp [LocFacts₂]

theorem frame_ne_zero {Z : LocDat D} {p : PlF D} (Fr : LocNG.FrameD (locH Z p) D.R.rS) (hT : Fr.T ≠ 0)
    (a : Fin (D.R.rS + 1)) : Fr.f a ≠ 0 := by
  intro h0
  induction a using Fin.lastCases with
  | last =>
    have h1 := Fr.h_zz
    rw [h0, h_zero_left] at h1
    have h2 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep Fr.T = 0 := neg_eq_zero.mp h1.symm
    exact hT ((map_eq_zero_iff _ (RingHom.injective _)).mp h2)
  | cast i =>
    have h1 := Fr.h_es i i
    rw [h0, h_zero_left, if_pos rfl] at h1
    exact zero_ne_one h1

theorem frFac_unit {p : PlF D} (δ : ∀ p, (D.s.atP p).Fp) (a : Fin (D.R.rS + 1)) (v : Vp D p)
    (hv : frFac δ p a • v ≠ 0) : IsUnit (frFac δ p a) := by
  unfold frFac at hv ⊢
  by_cases hu : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (D.R.rS - a.val))
  · exact isUnit_ringInverse.mpr hu
  · rw [Ring.inverse_non_unit _ hu, zero_smul] at hv
    exact absurd rfl hv

def fixSub (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Submodule D.host.E (VS D).V where
  carrier := {u | g (baseChange₂ D p u) = baseChange₂ D p u}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    rw [ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [baseChange_smul₂, map_smul, ha]

theorem xplus_le {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (S : Submodule D.host.E (VS D).V)
    (h : ∀ a, frame F a ∈ S) : Xplus F ≤ S := by
  show F.fl.X ⊔ Submodule.span _ {F.fl.z} ≤ S
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    have := h i.castSucc
    simpa [frame, FlagG.fvec] using this
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have := h (Fin.last _)
    simpa [frame, FlagG.fvec] using this

theorem le_of_loc (Z : LocDat D) (Λ₂ : LV D) (h2 : Submodule.IsLattice D.host.E Λ₂) (N : LV D)
    (hN : ∀ z ∈ N, ∀ p, baseChange₂ D p z ∈ lattice₂ D Z.M p Λ₂) : N ≤ Λ₂ := by
  intro x hx
  have hlat : Submodule.IsLattice D.host.E (Λ₂ ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
    refine ⟨h2.fg.sup (Submodule.fg_span_singleton x), ?_⟩
    rw [eq_top_iff, ← h2.span_eq_top]
    exact Submodule.span_mono (by intro y hy; exact Submodule.mem_sup_left hy)
  have heq : ∀ p, lattice₂ D Z.M p (Λ₂ ⊔ Submodule.span (𝓞 D.host.E) {x}) = lattice₂ D Z.M p Λ₂ := by
    intro p
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [map_add]
      exact add_mem (Submodule.subset_span ⟨y, hy, rfl⟩) (hN _ (N.smul_mem c hx) p)
    · exact Submodule.span_mono (Set.image_mono (by intro y hy; exact Submodule.mem_sup_left hy))
  have := ((GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).1 _ Λ₂ hlat h2).2 heq
  rw [← this]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

theorem fix_span {u u' : D.what₂.Word}
    (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)
    (hB : Based Z FP (Tu D u) (Tu D u') F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p))) (p : PlF D)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ (FP p).UW0) :
    Xplus F ⊔ Xplus F' ≤ fixSub p g := by
  have hN := (hR p).2.2.2.2.2.2
  refine sup_le (xplus_le F _ fun a => ?_) (xplus_le F' _ fun a => ?_)
  · have hfa := (localComplementUnitary_fixes_both_frames (FP p) hg a).1
    have hne := frame_ne_zero (FP p).A hN.2.1 a
    rw [(hB p).1] at hfa hne
    have hu := frFac_unit Z.δ a _ hne
    show g (baseChange₂ D p (frame F a)) = baseChange₂ D p (frame F a)
    rw [map_smul] at hfa
    exact hu.smul_left_cancel.mp hfa
  · have hfa := (localComplementUnitary_fixes_both_frames (FP p) hg a).2
    have hne := frame_ne_zero (FP p).B hN.2.2.2.1 a
    rw [(hB p).2.1] at hfa hne
    have hu := frFac_unit Z.δ a _ hne
    show g (baseChange₂ D p (frame F' a)) = baseChange₂ D p (frame F' a)
    rw [map_smul] at hfa
    exact hu.smul_left_cancel.mp hfa

theorem inf_span_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') := by
  intro D X Y u u' F F' w _ _ Z FP hB hR Λ₀ h0 Λ h1 hloc
  apply le_antisymm
  · refine le_inf (le_of_loc Z Λ₀ h0 _ fun z hz p => ?_) inf_le_right
    obtain ⟨g, hg, himg⟩ := hloc p
    have hfix : g (baseChange₂ D p z) = baseChange₂ D p z := fix_span F F' Z FP hB hR p hg hz.2
    have hm : baseChange₂ D p z ∈ lattice₂ D Z.M p Λ := Submodule.subset_span ⟨z, hz.1, rfl⟩
    rw [← himg] at hm
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.1 hm
    have : g y = g (baseChange₂ D p z) := by rw [hfix]; exact hyz
    rw [g.injective this] at hy
    exact hy
  · refine le_inf (le_of_loc Z Λ h1 _ fun z hz p => ?_) inf_le_right
    obtain ⟨g, hg, himg⟩ := hloc p
    have hfix : g (baseChange₂ D p z) = baseChange₂ D p z := fix_span F F' Z FP hB hR p hg hz.2
    have hm : baseChange₂ D p z ∈ lattice₂ D Z.M p Λ₀ := Submodule.subset_span ⟨z, hz.1, rfl⟩
    rw [← himg, ← hfix]
    exact Submodule.mem_map_of_mem hm

end GlobalTheory.FrameSpanLat
