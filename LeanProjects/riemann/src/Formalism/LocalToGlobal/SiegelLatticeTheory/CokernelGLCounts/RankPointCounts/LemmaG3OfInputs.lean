import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Th21

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false
set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem Hp_eq_Hsp (t : TauC Y u u') (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ)
    (hL : IsLift Λ (lf D (X.Fu u))) (hL' : IsLift Λ t.frame) :
    Hp Λ (lf D (X.Fu u)) t.frame = Hsp (X.Fu u) t.frame.fl := by
  unfold Hp Hsp
  rw [UUE_eq_Asp Λ hΛ _ _ hL hL']

theorem lemmaG3_of_inputs (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0)
    (h2 : Gt t2 ≠ 0) (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) (hG1 : t1.G = t0.G) (hG2 : t2.G = t0.G)
    (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u')))
    (he : t2.lin = σ * t1.lin * s') (ha : coefA Y u u' t0 t1 = coefA Y u u' t0 t2)
    (ha' : coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2) :
    σ (omp (X.Fu u) t1.frame.fl) - omp (X.Fu u) t1.frame.fl ∈ (X.Fu u).X ∧
    (t1.lin * s'⁻¹ * t1.lin⁻¹) (omp t1.frame.fl (X.Fu u)) - omp t1.frame.fl (X.Fu u) ∈ t1.frame.fl.X ∧
    ∀ w ∈ Hsp (X.Fu u) t1.frame.fl, ∃ w0 ∈ Hsp (X.Fu u) t1.frame.fl,
      σ w - w0 ∈ (X.Fu u).X ∧ (t1.lin * s'⁻¹ * t1.lin⁻¹) w - w0 ∈ t1.frame.fl.X := by
  obtain ⟨⟨l1, -⟩, ⟨l1', -⟩⟩ := line_occ Y t0 t1 h0 h1 hR1 hG1 hT hT'
  obtain ⟨⟨l2, -⟩, ⟨l2', -⟩⟩ := line_occ Y t0 t2 h0 h2 hR2 hG2 hT hT'
  have hy : yT Y u u' t2 - yT Y u u' t1 ∈ (X.Fu u).X := by
    have := Submodule.sub_mem _ l2 l1
    rw [← ha] at this
    convert this using 1
    abel
  have hy' : yT' Y u u' t2 - yT' Y u u' t1 ∈ (X.Fu u').X := by
    have := Submodule.sub_mem _ l2' l1'
    rw [← ha'] at this
    convert this using 1
    abel
  obtain ⟨o1, o2, o3, o4⟩ := omp_terms Y t1 t2 σ s' hσ hs' he
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs'i := SRat_inv (lf D (X.Fu u')) hs'
  have hσm := hσ
  obtain ⟨hσi, hσf, hσz⟩ := hσm
  obtain ⟨hsi', hsf', hsz'⟩ := hs'i
  have hsymm : ∀ v, t2.lin.symm (σ v) = s'.symm (t1.lin.symm v) := by
    intro v
    apply t2.lin.injective
    rw [LinearEquiv.apply_symm_apply, he]
    show σ v = σ (t1.lin (s' (s'.symm (t1.lin.symm v))))
    simp
  refine ⟨?_, ?_, ?_⟩
  · have e : yT Y u u' t2 - yT Y u u' t1 =
        ((Tu D u : ℕ) : D.host.E) • (σ (omp (X.Fu u) t1.frame.fl) - omp (X.Fu u) t1.frame.fl) := by
      simp only [yT, yv, o1, o2, smul_sub]
      abel
    rw [e] at hy
    exact (Submodule.smul_mem_iff _ hTE).1 hy
  · set ω := omp t1.frame.fl (X.Fu u) with hω
    have e : yT' Y u u' t2 - yT' Y u u' t1 =
        ((Tu D u' : ℕ) : D.host.E) • (s'.symm (t1.lin.symm ω) - t1.lin.symm ω) := by
      simp only [yT', yv, o3, o4, frame_z_eq_lin_zu, map_add, map_smul, LinearEquiv.symm_apply_apply, hsymm, smul_sub]
      abel
    rw [e] at hy'
    have hv := (Submodule.smul_mem_iff _ hTE').1 hy'
    refine (mem_frameX Y t1 _).2 ?_
    convert hv using 1
    rw [map_sub]
    show t1.lin.symm (t1.lin (s'.symm (t1.lin.symm ω))) - t1.lin.symm ω = _
    rw [LinearEquiv.symm_apply_apply]
  · obtain ⟨hl1, hl2, hTh⟩ := th21 Y t0 t1 t2 h0 h1 h2 hR1 hR2
    have hlat : Submodule.IsLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.1
    have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
    have hL1 : IsLift t0.lam t1.frame := by rw [← hl1]; exact t1.rep.2.2.2.2.1
    have hL2 : IsLift t0.lam t2.frame := by rw [← hl2]; exact t2.rep.2.2.2.2.1
    have hH1 := Hp_eq_Hsp Y t1 t0.lam hlat hLF hL1
    have hH2 := Hp_eq_Hsp Y t2 t0.lam hlat hLF hL2

    have hX1A : t1.frame.fl.X ≤ Asp (X.Fu u) t1.frame.fl := by
      rw [← Asp_symm]; exact X_le_Asp _ _
    have hz1A : t1.frame.fl.z ∈ Asp (X.Fu u) t1.frame.fl := by
      rw [← Asp_symm]; exact z_mem_Asp _ _
    have hAsp : Asp (X.Fu u) t2.frame.fl ≤ (Asp (X.Fu u) t1.frame.fl).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [Asp, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl a =>
        refine ⟨σ.symm ((X.Fu u).fvec a), ?_, by simp⟩
        induction a using Fin.lastCases with
        | last =>
          have e : σ.symm ((X.Fu u).fvec (Fin.last _)) =
              (X.Fu u).z + (σ.symm (X.Fu u).z - (X.Fu u).z) := by
            simp [FlagG.fvec, Fin.snoc_last]
          rw [e]
          exact Submodule.add_mem _ (z_mem_Asp _ _) (X_le_Asp _ _ (SRat_inv (lf D (X.Fu u)) hσ).2.2)
        | cast a =>
          simp only [FlagG.fvec, Fin.snoc_castSucc]
          refine X_le_Asp _ _ (X_pres (lf D (X.Fu u)) (SRat_inv (lf D (X.Fu u)) hσ).2.1 _ ?_)
          exact Submodule.subset_span ⟨a, rfl⟩
      | inr b =>
        refine ⟨t1.lin (s' ((X.Fu u').fvec b)), ?_, ?_⟩
        · induction b using Fin.lastCases with
          | last =>
            have e : t1.lin (s' ((X.Fu u').fvec (Fin.last _))) =
                t1.frame.fl.z + t1.lin (s' (X.Fu u').z - (X.Fu u').z) := by
              rw [frame_z_eq_lin_zu, map_sub]; simp [FlagG.fvec, Fin.snoc_last]
            rw [e]
            refine Submodule.add_mem _ hz1A (hX1A ((mem_frameX Y t1 _).2 ?_))
            rw [LinearEquiv.symm_apply_apply]
            exact hs'.2.2
          | cast b =>
            refine hX1A ((mem_frameX Y t1 _).2 ?_)
            rw [LinearEquiv.symm_apply_apply]
            simp only [FlagG.fvec, Fin.snoc_castSucc]
            exact X_pres (lf D (X.Fu u')) hs'.2.1 _ (Submodule.subset_span ⟨b, rfl⟩)
        · show σ (t1.lin (s' ((X.Fu u').fvec b))) = t2.frame.fl.fvec b
          rw [frame_fvec, he]
          rfl
    intro w hw
    have hσw : σ w ∈ Hp t0.lam (lf D (X.Fu u)) t2.frame := by
      rw [hH2]
      refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun y hy => ?_
      obtain ⟨a, ha, rfl⟩ := hAsp hy
      rw [LinearEquiv.coe_coe, hσi]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).1 hw a ha
    rw [← hTh] at hσw
    obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hσw
    obtain ⟨-, hp2, hp12, hpβ⟩ := (CorankRelation.mem_ThPairs t0.lam _ t2.frame t1.frame _ p).1 hp
    simp only [LinearMap.fst_apply] at hp1
    refine ⟨p.2, by rw [← hH1]; exact hp2, ?_, ?_⟩
    · rw [← hp1]; exact hp12
    · have e : (t1.lin * t2.lin⁻¹) p.1 = (t1.lin * s'⁻¹ * t1.lin⁻¹) w := by
        rw [hp1]
        show t1.lin (t2.lin.symm (σ w)) = t1.lin (s'.symm (t1.lin.symm w))
        rw [hsymm]
      rw [← e]
      exact hpβ

end Formalism.L2.SG.NGCut.NormalVectorPairings
