import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfK

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth finrank_orth fvec_castSucc fvec_last mem_orth_span
  mem_ThPairs)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GF

variable {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}

theorem span_sum_elim_frameAct (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec (frameAct F'.fl.fvec ξ⁻¹))) =
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) := by
  rw [Set.Sum.elim_range, Set.Sum.elim_range, Submodule.span_union, Submodule.span_union,
    span_frameAct_inv _ ξ h1 h2]

theorem Dl_eq_GDl_top (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Dl F.fl F'.fl (D.R.rS + 1) = GDl F.fl.fvec F'.fl.fvec (D.R.rS + 1) := by
  rw [PI.PairCorankPos.W.Dl_top, GDl_top']
  rfl

theorem Dl_eq_GDl_r (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Dl F.fl F'.fl D.R.rS = GDl F.fl.fvec F'.fl.fvec D.R.rS := by
  rw [PI.PairCorankPos.W.Dl_r, GDl_r']
  rfl

theorem Gval_eq (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Gval F F' = GDl F.fl.fvec F'.fl.fvec (D.R.rS + 1) * star (GDl F.fl.fvec F'.fl.fvec (D.R.rS + 1)) -
      T * T' * (GDl F.fl.fvec F'.fl.fvec D.R.rS * star (GDl F.fl.fvec F'.fl.fvec D.R.rS)) := by
  show Gflag F.fl F'.fl = _
  rw [Gflag, Dl_eq_GDl_top, Dl_eq_GDl_r]

theorem gfacts_of (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T')
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hF : FixedHyp D Λ F) (hl' : IsLift Λ F') (hl'' : IsLift Λ F'') (hc' : IsFixedConv Λ (gS D) F')
    (hc'' : IsFixedConv Λ (gS D) F'') (hP : IsPair Λ F F' F'' β (gS D))
    (hs : Lat.s0 Λ F F' F'' β D.R.k = 1) (hsc : IsScalar Λ F F' F'' β)
    (hG' : Gval F F' ≠ 0) (hG'' : Gval F F'' ≠ 0) (hT0 : T ≠ 0) (hT0' : T' ≠ 0) :
    GFacts Λ (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹) (frameAct (frame F'') (admXi D Λ F F'')⁻¹) β := by
  obtain ⟨hlat, -, hlF, hcF⟩ := hF
  have hξ1 := admissibility_witness_unitriangular Λ F F'
  have hξ2 := admissibility_witness_unitriangular Λ F F''
  have hη1 := inv_unitri _ hξ1.1 hξ1.2
  have hη2 := inv_unitri _ hξ2.1 hξ2.2
  have hXF := X_le_spanE_of_conv Λ F _ hcF
  have hXF' := X_le_spanE_of_conv Λ F' _ hc'
  have hXF'' := X_le_spanE_of_conv Λ F'' _ hc''
  have hU1 := PI.ScalarPairDr.W.UUE_eq Λ F F' hlF.2 hl'.2 hXF hXF'
  have hU2 := PI.ScalarPairDr.W.UUE_eq Λ F F'' hlF.2 hl''.2 hXF hXF''
  have hGN1 := PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate (VS D) Λ F F' hlat hlF hl' hG'
  have hGN2 := PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate (VS D) Λ F F'' hlat hlF hl'' hG''
  have hn := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_hS D
  obtain ⟨hTh, hTh''⟩ := theta_eq Λ D.R.k F F' F'' β hn hGN1.1 hGN2.1 hU1 hG' hs
  have hXg1 : Xs (S := VS D) (frameAct (frame F') (admXi D Λ F F')⁻¹) = Xsp F' :=
    (Xs_frameAct_inv _ _ hξ1.1 hξ1.2).trans (Xs_fvec F'.fl)
  have hXg2 : Xs (S := VS D) (frameAct (frame F'') (admXi D Λ F F'')⁻¹) = Xsp F'' :=
    (Xs_frameAct_inv _ _ hξ2.1 hξ2.2).trans (Xs_fvec F''.fl)
  have hsp1 : Submodule.span D.host.E (Set.range (Sum.elim (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹))) =
      UUE Λ F F' := (span_sum_elim_frameAct F F' _ hξ1.1 hξ1.2).trans hU1.symm
  have hsp2 : Submodule.span D.host.E (Set.range (Sum.elim (frame F) (frameAct (frame F'') (admXi D Λ F F'')⁻¹))) =
      UUE Λ F F'' := (span_sum_elim_frameAct F F'' _ hξ2.1 hξ2.2).trans hU2.symm
  have hPX : (Xsp F').map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F'' := by
    rw [← Xflag_top, ← Xflag_top]
    exact hP.2.1 D.R.rS
  have hβX : ∀ x ∈ Xsp F', β x ∈ Xsp F'' := fun x hx => hPX ▸ Submodule.mem_map_of_mem hx
  have hβX' : ∀ x ∈ Xsp F'', β.symm x ∈ Xsp F' := by
    intro x hx
    rw [← hPX] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hy
  have hiso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y := fun x y => hP.1.1 x y
  have hβz : β F'.fl.z = F''.fl.z := hP.2.2.1

  rw [show (frame F) = F.fl.fvec from rfl]
  have rT1 := GDl_frameAct_top F.fl.fvec F'.fl.fvec _ hη1.1 hη1.2
  have rT2 := GDl_frameAct_top F.fl.fvec F''.fl.fvec _ hη2.1 hη2.2
  have rR1 := GDl_frameAct_r F.fl.fvec F'.fl.fvec _ hη1.1 hη1.2
  have rR2 := GDl_frameAct_r F.fl.fvec F''.fl.fvec _ hη2.1 hη2.2
  have rO'1 := Gom'_frameAct F.fl.fvec F'.fl.fvec _ hη1.1 hη1.2
  have rO'2 := Gom'_frameAct F.fl.fvec F''.fl.fvec _ hη2.1 hη2.2
  have rO1 := Gom_frameAct F.fl.fvec F'.fl.fvec _ hη1.1 hη1.2
  have rO2 := Gom_frameAct F.fl.fvec F''.fl.fvec _ hη2.1 hη2.2
  have hind' : LinearIndependent D.host.E F'.fl.fvec := by
    have := (PI.PairCorankPos.W.linIndep F.fl F'.fl hG').comp Sum.inr Sum.inr_injective
    rwa [Sum.elim_comp_inr] at this
  have hind'' : LinearIndependent D.host.E F''.fl.fvec := by
    have := (PI.PairCorankPos.W.linIndep F.fl F''.fl hG'').comp Sum.inr Sum.inr_injective
    rwa [Sum.elim_comp_inr] at this
  have key1 := fun h => scal_dir Λ F F' F'' hlF.2 hl'.2 hl''.2 hT0 hU2
    (fun y hy hyo => ylift_tr Λ F F' F'' β hTh hy hyo)
    (fun y hy1 hy2 α α' h => (hsc y hy1 y hy2 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
      (by rw [sub_self]; exact Submodule.zero_mem _) (by rw [map_zero, sub_zero]; exact Submodule.zero_mem _)
      α α').2 h) hind' h
  have key2 := fun h => scal_dir Λ F F'' F' hlF.2 hl''.2 hl'.2 hT0 hU1
    (fun y hy hyo => ylift_tr' Λ F F' F'' β hTh'' hy hyo)
    (fun y hy1 hy2 α α' h => (hsc y hy2 y hy1 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
      (by rw [sub_self]; exact Submodule.zero_mem _) (by rw [map_zero, sub_zero]; exact Submodule.zero_mem _)
      α α').1 h) hind'' h
  have keyom := fun h => scal_om Λ F F' F'' β hlF.2 hl'.2 hl''.2 hT0' hiso hβX' hβz hU1
    (fun y hy hyo => ylift_beta Λ F F' F'' β hiso hβX' hTh'' hy hyo)
    (fun y' hy1 hy2 α α' h => (hsc 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) y' hy1 (β y') hy2
      (by rw [sub_self]; exact Submodule.zero_mem _) (by rw [sub_self]; exact Submodule.zero_mem _)
      α α').1 h) h
  have hG'e := Gval_eq F F'
  have hG''e := Gval_eq F F''
  set D1 := GDl F.fl.fvec F'.fl.fvec (D.R.rS + 1) with hD1
  set D2 := GDl F.fl.fvec F''.fl.fvec (D.R.rS + 1) with hD2
  set R1 := GDl F.fl.fvec F'.fl.fvec D.R.rS with hR1
  set R2 := GDl F.fl.fvec F''.fl.fvec D.R.rS with hR2

  have hrel : R1 * D2 = R2 * D1 ∧
      D2 • Gom' F.fl.fvec F'.fl.fvec - D1 • Gom' F.fl.fvec F''.fl.fvec ∈ Xsp F ∧
      star D2 • β (Gom F.fl.fvec F'.fl.fvec) - star D1 • Gom F.fl.fvec F''.fl.fvec ∈ Xsp F'' := by
    by_cases h1 : D1 = 0
    · by_cases h2 : D2 = 0
      · rw [h1, h2]
        simp
      · exfalso
        have k := (key2 h2).2
        rw [h1, zero_mul, mul_eq_zero] at k
        rcases k with k | k
        · exact h2 k
        · apply hG'
          rw [hG'e, h1, k]
          simp
    · obtain ⟨⟨x, hx, hxe⟩, k⟩ := key1 h1
      have h2 : D2 ≠ 0 := by
        intro h2
        rw [h2, zero_mul, mul_eq_zero] at k
        rcases k with k | k
        · exact h1 k
        · apply hG''
          rw [hG''e, h2, k]
          simp
      refine ⟨by linear_combination (-1 : D.host.E) * k, ?_, keyom h2⟩
      have e : D2 • Gom' F.fl.fvec F'.fl.fvec - D1 • Gom' F.fl.fvec F''.fl.fvec = -(D1 • x) := by
        rw [hxe, smul_sub]
        abel
      rw [e]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hx)
  refine ⟨hiso, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [← hP.1.2]
    exact ⟨v, hv, rfl⟩
  · intro v hv
    rw [← hP.1.2] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    show β.symm (β w) ∈ Λ
    rw [LinearEquiv.symm_apply_apply]
    exact hw
  · intro a
    show _ ∈ Xs (S := VS D) (frameAct (frame F'') (admXi D Λ F F'')⁻¹)
    rw [hXg2]
    exact hβX _ (hXg1 ▸ Submodule.subset_span ⟨a, rfl⟩)
  · intro a
    show _ ∈ Xs (S := VS D) (frameAct (frame F') (admXi D Λ F F')⁻¹)
    rw [hXg1]
    exact hβX' _ (hXg2 ▸ Submodule.subset_span ⟨a, rfl⟩)
  · have h1 := frameAct_last_sub (frame F') _ (hη1.2 (Fin.last _))
    have h2 := frameAct_last_sub (frame F'') _ (hη2.2 (Fin.last _))
    rw [Xs_fvec] at h1 h2
    show _ ∈ Xs (S := VS D) (frameAct (frame F'') (admXi D Λ F F'')⁻¹)
    rw [hXg2]
    have e : β (frameAct (frame F') (admXi D Λ F F')⁻¹ (Fin.last _)) -
        frameAct (frame F'') (admXi D Λ F F'')⁻¹ (Fin.last _) =
        β (frameAct (frame F') (admXi D Λ F F')⁻¹ (Fin.last _) - frame F' (Fin.last _)) -
        (frameAct (frame F'') (admXi D Λ F F'')⁻¹ (Fin.last _) - frame F'' (Fin.last _)) := by
      rw [map_sub, show frame F' (Fin.last _) = F'.fl.z from fvec_last _,
        show frame F'' (Fin.last _) = F''.fl.z from fvec_last _, hβz]
      abel
    rw [e]
    exact Submodule.sub_mem _ (hβX _ h1) h2
  · intro a b
    show (VS D).hT (F.fl.fvec a.castSucc) (F.fl.fvec b.castSucc) = 0
    rw [fvec_castSucc, fvec_castSucc]
    exact F.fl.e_iso a b
  · intro a b
    have ha : frameAct (frame F'') (admXi D Λ F F'')⁻¹ a.castSucc ∈ F''.fl.X := by
      have h : frameAct (frame F'') (admXi D Λ F F'')⁻¹ a.castSucc ∈
          Xs (S := VS D) (frameAct (frame F'') (admXi D Λ F F'')⁻¹) := Submodule.subset_span ⟨a, rfl⟩
      rw [hXg2] at h
      exact h
    have hb : frameAct (frame F'') (admXi D Λ F F'')⁻¹ b.castSucc ∈ F''.fl.X := by
      have h : frameAct (frame F'') (admXi D Λ F F'')⁻¹ b.castSucc ∈
          Xs (S := VS D) (frameAct (frame F'') (admXi D Λ F F'')⁻¹) := Submodule.subset_span ⟨b, rfl⟩
      rw [hXg2] at h
      exact h
    exact hT_X_X F''.fl ha hb
  · intro y
    have hsup : UUE Λ F F' ⊔ orth (VS D) (UUE Λ F F') = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (UUE Λ F F') (orth (VS D) (UUE Λ F F'))
      rw [hGN1.2, finrank_bot] at h1
      have h2 := finrank_orth (VS D) (UUE Λ F F')
      omega
    have hy : y ∈ UUE Λ F F' ⊔ orth (VS D) (UUE Λ F F') := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hy
    refine ⟨u, hsp1 ▸ hu, fun i => ?_⟩
    have e : y - u = w := by rw [← huw]; abel
    rw [e]
    exact (mem_orth (VS D)).1 hw _ (hsp1 ▸ Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    set v := Sum.elim F.fl.fvec (frameAct (frame F') (admXi D Λ F F')⁻¹) with hv
    set u := ∑ k, star (c k) • v k with hu
    have hpair : ∀ i, (VS D).hT u (v i) = 0 := by
      intro i
      have := congrFun hc i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, brS, Pi.zero_apply] at this
      rw [hu, map_sum, LinearMap.sum_apply]
      simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have huU : u ∈ UUE Λ F F' := by
      rw [← hsp1]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have huO : u ∈ orth (VS D) (UUE Λ F F') := by
      rw [← hsp1, mem_orth_span]
      rintro _ ⟨i, rfl⟩
      rw [hT_swap, hpair i, star_zero]
    have hu0 : u = 0 := by
      have := Submodule.mem_inf.2 ⟨huU, huO⟩
      rw [hGN1.2] at this
      exact (Submodule.mem_bot _).1 this
    have hind : LinearIndependent D.host.E v := by
      rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hsp1, hGN1.1, Fintype.card_sum,
        Fintype.card_fin]
      ring
    apply hc0
    funext k
    have := Fintype.linearIndependent_iff.1 hind (fun k => star (c k)) (by rw [← hu]; exact hu0) k
    simpa using this
  · intro x1 hx1
    have hx1H : x1 ∈ Hp Λ F F' := by
      rw [Hp, ← hsp1, mem_orth_span]
      rintro _ ⟨i, rfl⟩
      exact hx1 i
    rw [← hTh] at hx1H
    obtain ⟨p, hp, rfl⟩ := hx1H
    have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
    refine ⟨p.2, fun i => ?_, ?_, ?_⟩
    · have h := hm.2.1
      rw [Hp, ← hsp2, mem_orth_span] at h
      exact h _ ⟨i, rfl⟩
    · show p.1 - p.2 ∈ Xs (S := VS D) F.fl.fvec
      rw [Xs_fvec]
      exact hm.2.2.1
    · show _ ∈ Xs (S := VS D) (frameAct (frame F'') (admXi D Λ F F'')⁻¹)
      rw [hXg2]
      exact hm.2.2.2
  · rw [rR1, rR2, rT1, rT2]
    exact hrel.1
  · rw [rT1, rT2, rO'1, rO'2]
    show _ ∈ Xs (S := VS D) F.fl.fvec
    rw [Xs_fvec]
    exact hrel.2.1
  · show _ ∈ Xs (S := VS D) (frameAct (frame F'') (admXi D Λ F F'')⁻¹)
    rw [rT1, rT2, rO1, rO2, hXg2]
    exact hrel.2.2

end GF

end Formalism.L2.SG.Pf.ScalarFramePf
