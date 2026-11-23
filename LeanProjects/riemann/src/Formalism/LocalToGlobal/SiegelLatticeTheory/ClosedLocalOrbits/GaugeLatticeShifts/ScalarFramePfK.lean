import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfJ

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth fvec_castSucc fvec_last mem_orth_Xplus hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ScalOm

variable {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}

theorem hT_om_X (u v : Fin (D.R.rS + 1) → (VS D).V) {w : (VS D).V} (hw : w ∈ Xs (S := VS D) v) :
    (VS D).hT (Gom u v) w = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hw
  rw [map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [map_smul, om_pair, if_neg (Fin.castSucc_ne_last b), smul_zero]

theorem scal_om (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z) (hT0' : T' ≠ 0)
    (hiso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y)
    (hXm' : ∀ x ∈ Xsp F'', β.symm x ∈ Xsp F') (hβz : β F'.fl.z = F''.fl.z)
    (hU1 : UUE Λ F F' = Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)))
    (htrβ : ∀ y ∈ UUE Λ F F', y ∈ orth (VS D) (Xsp F') → β y ∈ UUE Λ F F'')
    (hsc : ∀ y', y' ∈ Ylift' Λ F F' → β y' ∈ Ylift' Λ F F'' → ∀ α α',
      SgRel F F' 0 y' α α' → SgRel F F'' 0 (β y') α α')
    (hD2 : GDl F.fl.fvec F''.fl.fvec (D.R.rS + 1) ≠ 0) :
    star (GDl F.fl.fvec F''.fl.fvec (D.R.rS + 1)) • β (Gom F.fl.fvec F'.fl.fvec) -
      star (GDl F.fl.fvec F'.fl.fvec (D.R.rS + 1)) • Gom F.fl.fvec F''.fl.fvec ∈ Xsp F'' := by
  set f := F.fl.fvec with hf
  set f' := F'.fl.fvec with hf'
  set f'' := F''.fl.fvec with hf''
  set D1 := GDl f f' (D.R.rS + 1) with hD1def
  set D2 := GDl f f'' (D.R.rS + 1) with hD2def
  set R1 := GDl f f' D.R.rS with hR1def
  set om1 := Gom f f' with hom1
  set om2 := Gom f f'' with hom2
  have hfl' : f' (Fin.last _) = F'.fl.z := fvec_last _
  have hfl'' : f'' (Fin.last _) = F''.fl.z := fvec_last _
  have hfc' : ∀ b : Fin D.R.rS, f' b.castSucc = F'.fl.e b := fun b => fvec_castSucc _ b
  have hfc'' : ∀ b : Fin D.R.rS, f'' b.castSucc = F''.fl.e b := fun b => fvec_castSucc _ b
  have q1 : ∀ b, (VS D).hT om1 (f' b) = if b = Fin.last _ then D1 else 0 := om_pair f f'
  have q2 : ∀ b, (VS D).hT om2 (f'' b) = if b = Fin.last _ then D2 else 0 := om_pair f f''
  have hom1X : ∀ w ∈ Xsp F', (VS D).hT om1 w = 0 := fun w hw => hT_om_X f f' (by rw [← Xsp_eq_Xs]; exact hw)
  have hz'z' : (VS D).hT F'.fl.z F'.fl.z = -T' := F'.fl.z_norm
  set u' := om1 + (star D1 / T') • F'.fl.z with hu'
  have hu'U : u' ∈ UUE Λ F F' := by
    rw [hU1]
    exact Submodule.add_mem _ (span_left_le F F' (Gom_mem f f'))
      (Submodule.smul_mem _ _ (span_right_le F F' (z_mem_span F')))
  have hu'o : u' ∈ orth (VS D) (Xplus F') := by
    rw [Xplus, mem_orth_Xplus]
    refine ⟨fun b => ?_, ?_⟩
    · rw [hu', map_add, map_smul, F'.fl.z_orth b, smul_zero, add_zero, hT_swap,
        hom1X _ (Submodule.subset_span ⟨b, rfl⟩), star_zero]
    · have h1 := q1 (Fin.last _)
      rw [if_pos rfl, hfl'] at h1
      rw [hu', map_add, map_smul, hz'z', hT_swap, h1, smul_eq_mul]
      field_simp
      ring
  have hu'oX : u' ∈ orth (VS D) (Xsp F') := by
    rw [mem_orth]
    intro x hx
    exact (mem_orth (VS D)).1 hu'o x (Submodule.mem_sup_left hx)
  have hβU : β u' ∈ UUE Λ F F'' := htrβ u' hu'U hu'oX
  have hβo : β u' ∈ orth (VS D) (Xplus F'') := by
    rw [Xplus, mem_orth_Xplus]
    refine ⟨fun b => ?_, ?_⟩
    · have hb : β.symm (F''.fl.e b) ∈ Xsp F' := hXm' _ (Submodule.subset_span ⟨b, rfl⟩)
      rw [show F''.fl.e b = β (β.symm (F''.fl.e b)) from (β.apply_symm_apply _).symm, hiso]
      exact (mem_orth (VS D)).1 hu'o _ (Submodule.mem_sup_left hb)
    · rw [← hβz, hiso]
      exact (mem_orth (VS D)).1 hu'o _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hx0 : -(om1 - star R1 • F.fl.z) ∈ Xsp F := by
    rw [Xsp_eq_Xs, ← fvec_last F.fl]
    exact Submodule.neg_mem _ (om_decomp f f')
  have hsg : SgRel F F' 0 u' (-star R1) (-(star D1 / T')) :=
    ⟨-(om1 - star R1 • F.fl.z), hx0, 0, Submodule.zero_mem _, by rw [hz, hz', hu']; module⟩
  obtain ⟨x, hx, x'', hx'', heq⟩ := hsc u' (Submodule.mem_inf.2 ⟨hu'U, hu'o⟩)
    (Submodule.mem_inf.2 ⟨hβU, hβo⟩) _ _ hsg
  rw [hz, hz'', hu', map_add, map_smul, hβz] at heq
  have hp : β om1 + x'' = star R1 • F.fl.z - x := by
    have e1 : β om1 + x'' = -(0 - (β om1 + (star D1 / T') • F''.fl.z)) - (star D1 / T') • F''.fl.z + x'' := by
      abel
    rw [e1, heq]
    module
  have hxX : x ∈ F.fl.X := hx
  have hx''X : x'' ∈ F''.fl.X := hx''
  have hpspan : β om1 + x'' ∈ Submodule.span D.host.E (Set.range f) := by
    rw [hp]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (z_mem_span F)) (Xsp_le_span F hx)
  have hq0 : star D2 • (β om1 + x'') - star D1 • om2 = 0 := by
    refine eq_zero_of_orth_of_det_ne_zero f f'' hD2 (Submodule.sub_mem _ (Submodule.smul_mem _ _ hpspan)
      (Submodule.smul_mem _ _ (Gom_mem f f''))) fun b => ?_
    rw [PI.ScalarPairDr.W.hT_sub_left, hT_smul_left, hT_smul_left, star_star, star_star,
      PI.ScalarPairDr.W.hT_add_left, q2]
    induction b using Fin.lastCases with
    | last =>
      rw [if_pos rfl, hfl'', hT_X_alt F''.fl hx''X, ← hβz, hiso, ← hfl', q1, if_pos rfl]
      ring
    | cast b =>
      rw [if_neg (Fin.castSucc_ne_last b), hfc'', hT_X_X F''.fl hx''X (Submodule.subset_span ⟨b, rfl⟩),
        show F''.fl.e b = β (β.symm (F''.fl.e b)) from (β.apply_symm_apply _).symm, hiso,
        hom1X _ (hXm' _ (Submodule.subset_span ⟨b, rfl⟩))]
      ring
  have e : star D2 • β om1 - star D1 • om2 = -(star D2 • x'') + (star D2 • (β om1 + x'') - star D1 • om2) := by
    module
  rw [e, hq0, add_zero]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hx'')

end ScalOm

end Formalism.L2.SG.Pf.ScalarFramePf
