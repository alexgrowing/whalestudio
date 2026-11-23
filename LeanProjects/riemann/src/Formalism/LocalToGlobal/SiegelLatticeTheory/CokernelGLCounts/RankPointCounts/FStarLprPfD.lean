import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGenLoc

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.S.Loc.HermSp.LprU

namespace LprND

variable {D : Formalism.BasicNotions.D7}

def gramW {ι : Type} (w : ι → (VS D).V) : Matrix ι ι D.host.E := Matrix.of fun i j => brS (VS D) (w j) (w i)

theorem gramW_det_ne {r : ℕ} {U : Submodule D.host.E (VS D).V} (hdim : Module.finrank D.host.E U = 2 * r + 2)
    (hnd : U ⊓ orth (VS D) U = ⊥) (w : Fin (r + 1) ⊕ Fin (r + 1) → (VS D).V)
    (hw : Submodule.span D.host.E (Set.range w) = U) : (gramW w).det ≠ 0 := by
  have hli : LinearIndependent D.host.E w := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show _ = Module.finrank D.host.E (Submodule.span D.host.E (Set.range w))
    rw [hw, hdim, Fintype.card_sum, Fintype.card_fin]
    ring
  intro h0
  obtain ⟨c, hc0, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set x := ∑ k, c k • w k with hx
  have hx2 : ∀ i, (VS D).hT (w i) x = 0 := by
    intro i
    have h := congrFun hMc i
    simp only [Matrix.mulVec, dotProduct, gramW, Matrix.of_apply, brS, Pi.zero_apply] at h
    rw [hx, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hx1 : x ∈ U := by
    rw [← hw, hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hx3 : x ∈ orth (VS D) U := by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro y hy
    rw [← hw] at hy
    have hk : Submodule.span D.host.E (Set.range w) ≤ LinearMap.ker ((VS D).hT.flip x) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show (VS D).hT.flip x (w i) = 0
      rw [LinearMap.flip_apply]
      exact hx2 i
    have h := hk hy
    rw [LinearMap.mem_ker, LinearMap.flip_apply] at h
    exact h
  have hx0 : x = 0 := by
    have h : x ∈ U ⊓ orth (VS D) U := ⟨hx1, hx3⟩
    rw [hnd] at h
    exact (Submodule.mem_bot _).1 h
  apply hc0
  funext k
  exact Fintype.linearIndependent_iff.1 hli c (hx ▸ hx0) k

theorem gram_pair_ne {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ)
    (F : LFlag (VS D) D.R.rS T) (F'' : LFlag (VS D) D.R.rS T') (hzF : F.zt = F.fl.z) (hG : Gflag F.fl F''.fl ≠ 0)
    (w : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V)
    (hw : Submodule.span D.host.E (Set.range w) =
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F''.fl.fvec))) : (gramW w).det ≠ 0 := by
  set v := Sum.elim F.fl.fvec F''.fl.fvec with hv
  set Λ' : Submodule (𝓞 D.host.E) (VS D).V := Λ ⊔ Submodule.span (𝓞 D.host.E) (Set.range v) with hΛ'
  have hfg : Λ'.FG := hΛ.fg.sup (Submodule.fg_span (Set.finite_range _))
  have := hΛ
  have hL' : Submodule.IsLattice D.host.E Λ' :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg (A := D.host.E) le_sup_left hfg
  have hmem : ∀ k, v k ∈ Λ' := fun k => Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)
  let F1 : LFlag (VS D) D.R.rS T := ⟨F.fl, F.fl.z⟩
  let F2 : LFlag (VS D) D.R.rS T' := ⟨F''.fl, F''.fl.z⟩
  have hz1 : F1.fl.z ∈ Λ' := by
    have h := hmem (Sum.inl (Fin.last D.R.rS))
    simpa [hv, PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last] using h
  have hz2 : F2.fl.z ∈ Λ' := by
    have h := hmem (Sum.inr (Fin.last D.R.rS))
    simpa [hv, PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last] using h
  have hX1 : Xsp F1 ≤ spanE (VS D) (XLam Λ' F1) := by
    show Submodule.span D.host.E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨?_, Submodule.subset_span ⟨a, rfl⟩⟩
    have h := hmem (Sum.inl a.castSucc)
    simpa [hv, PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc] using h
  have hX2 : Xsp F2 ≤ spanE (VS D) (XLam Λ' F2) := by
    show Submodule.span D.host.E (Set.range F''.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨?_, Submodule.subset_span ⟨a, rfl⟩⟩
    have h := hmem (Sum.inr a.castSucc)
    simpa [hv, PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc] using h
  have n := PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate (VS D) Λ' F1 F2 hL' ⟨hz1, rfl⟩ ⟨hz2, rfl⟩ hG
  have hU : UUE Λ' F1 F2 = Submodule.span D.host.E (Set.range v) :=
    PI.ScalarPairDr.W.UUE_eq Λ' F1 F2 rfl rfl hX1 hX2
  exact gramW_det_ne n.1 n.2 w (hw.trans hU.symm)

theorem span_frameAct {r : ℕ} (u v : Fin (r + 1) → (VS D).V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    Submodule.span D.host.E (Set.range (Sum.elim u (frameAct v ξ⁻¹))) =
      Submodule.span D.host.E (Set.range (Sum.elim u v)) := by
  have hdet : IsUnit ξ.det := by
    have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [h2]
  have hinv : ξ⁻¹ * ξ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hv : v = frameAct (frameAct v ξ⁻¹) ξ := by
    funext b
    simp only [frameAct, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have e : ∀ a, ∑ c, ((ξ⁻¹ a c : 𝓞 D.host.E) : D.host.E) * ((ξ c b : 𝓞 D.host.E) : D.host.E) =
        (((ξ⁻¹ * ξ) a b : 𝓞 D.host.E) : D.host.E) := by
      intro a; rw [Matrix.mul_apply]; push_cast; rfl
    simp_rw [← Finset.sum_smul]
    have e2 : ∀ a, (∑ c, ((ξ c b : 𝓞 D.host.E) : D.host.E) * ((ξ⁻¹ a c : 𝓞 D.host.E) : D.host.E)) =
        (((ξ⁻¹ * ξ) a b : 𝓞 D.host.E) : D.host.E) := by
      intro a; rw [← e a]; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    simp only [e2, hinv, Matrix.one_apply]
    simp
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    cases k with
    | inl a => exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    | inr b =>
      show frameAct v ξ⁻¹ b ∈ _
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    cases k with
    | inl a => exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    | inr b =>
      show v b ∈ _
      have hb : v b = frameAct (frameAct v ξ⁻¹) ξ b := congrFun hv b
      rw [hb]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩)

variable (Zd : LocDat D) (p : PlF D)

theorem gram_loc {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → (VS D).V) (s : ι → (D.s.atP p).Ep) :
    (locH Zd p).gram (fun k => s k • baseChange₂ D p (w k)) =
      Matrix.diagonal (fun k => (Zd.M p).L.cj (s k)) * (gramW w).map (D.s.atP p).ιE * Matrix.diagonal s := by
  ext i j
  simp only [Formalism.MainNotions.S.Loc.HermSp.gram, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply,
    gramW]
  rw [Formalism.L2.SG.Pf.ScalarFramePf.h_bcP]
  ring

theorem gramInvE_loc {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → (VS D).V) (s : ι → (D.s.atP p).Ep)
    (hs : ∀ k, IsUnit (s k)) (hdet : (gramW w).det ≠ 0) :
    GramInvE (locH Zd p) (fun k => s k • baseChange₂ D p (w k)) := by
  set M := gramW w with hMdef
  set ι' := (D.s.atP p).ιE with hι
  set si : ι → (D.s.atP p).Ep := fun k => (((hs k).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) with hsi
  refine ⟨Matrix.diagonal si * M⁻¹.map ι' * Matrix.diagonal (fun k => (Zd.M p).L.cj (si k)), ?_⟩
  rw [gram_loc]
  have hM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  have hmap : M⁻¹.map ι' * M.map ι' = 1 := by
    rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero ι') (map_one ι')]
  have hs1 : (fun k => si k * s k) = fun _ => 1 := funext fun k => (hs k).val_inv_mul
  have hc1 : (fun k => (Zd.M p).L.cj (si k) * (Zd.M p).L.cj (s k)) = fun _ => 1 := by
    funext k; rw [← map_mul, (hs k).val_inv_mul, map_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal fun k => (Zd.M p).L.cj (si k)), Matrix.diagonal_mul_diagonal, hc1,
    Matrix.diagonal_one, Matrix.one_mul, ← Matrix.mul_assoc (M⁻¹.map ι'), hmap, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal, hs1, Matrix.diagonal_one]

end LprND

open LprND

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem genLoc_rows (hrows : IsRowReps D F0 what₂) (γ : TermDef.Term D u u' F0 what₂)
    (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w) (p : PlF D) : (locH Zd p).IsGeneric (tLoc Zd p γ) := by
  have hR : IsRowLat D F0 γ.lam := hrows.1 γ.lam γ.mem
  obtain ⟨hgen, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
  have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
    (h1e.trans h2e.symm)
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) :=
    (PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have hGv : Gval (lf D F0) (repF γ) ≠ 0 := by
    rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2]; exact hG
  exact (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 γ.lam (repF γ) hR h2
    (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hGv).1 hgenR p

theorem gval_repF (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w) :
    Gval (lf D F0) (repF γ) ≠ 0 := by
  obtain ⟨-, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2]; exact hG

theorem iso_locF' (p : PlF D) {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') :
    Iso' (locH Zd p) (locF' Zd p F') := by
  intro a b hab
  show (locH Zd p).h ((TermLoc.sgnP' D p a * frFac Zd.δ p a) • baseChange₂ D p (frame F' a))
    ((TermLoc.sgnP' D p b * frFac Zd.δ p b) • baseChange₂ D p (frame F' b)) = 0
  rw [Formalism.L2.SG.Pf.ScalarFramePf.h_bcP]
  have h0 : brS (VS D) (frame F' a) (frame F' b) = 0 := by
    unfold brS
    rcases hab with ha | hb
    · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 ha
      rw [PI.ScalarPairDr.W.hT_swap]
      have e : (VS D).hT (frame F' i.castSucc) (frame F' b) = 0 := by
        show (VS D).hT (F'.fl.fvec i.castSucc) (F'.fl.fvec b) = 0
        rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc]
        refine Fin.lastCases ?_ (fun j => ?_) b
        · rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last]; exact F'.fl.z_orth i
        · rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc]; exact F'.fl.e_iso i j
      rw [e, star_zero]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hb
      show (VS D).hT (F'.fl.fvec j.castSucc) (F'.fl.fvec a) = 0
      rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc]
      refine Fin.lastCases ?_ (fun i => ?_) a
      · rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last]; exact F'.fl.z_orth j
      · rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc]; exact F'.fl.e_iso j i
  rw [h0, map_zero, mul_zero]

theorem lprNondeg_holds : LprNondeg Zd u u' F0 what₂ := by
  intro hrows γ Z hC F' hP p
  obtain ⟨w, hγ, -, -, -, -⟩ := id hC
  have hΛ : Submodule.IsLattice D.host.E γ.lam := (hrows.1 γ.lam γ.mem).1.1
  have hgen := genLoc_rows Zd hrows γ w hγ p
  have hZ : ZhatL (lf D F0) F' = Z := hP.1.2.2.2.2
  have hdet : Z.det ≠ 0 := (starMinors_holds u u' F0 what₂ γ Z hC).1
  have hsK : ∀ k, IsUnit (Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a)
      (fun b => sgnP' D p b * frFac Zd.δ p b) k) := by
    intro k
    cases k with
    | inl a => exact Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p a
    | inr b => exact Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p b

  have n1 : GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (tLoc Zd p γ).f') := by
    have e : Sum.elim (tLoc Zd p γ).f (tLoc Zd p γ).f' = fun k => Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a)
        (fun b => sgnP' D p b * frFac Zd.δ p b) k • baseChange₂ D p (Sum.elim (frame (lf D F0)) (starFrame γ) k) := by
      funext k; cases k <;> rfl
    rw [e]
    refine gramInvE_loc Zd p _ _ hsK (gram_pair_ne γ.lam hΛ (lf D F0) (repF γ) rfl (gval_repF γ w hγ) _ ?_)
    have hu := admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)
    exact span_frameAct _ _ _ hu.1 hu.2
  have n2 : GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (locF' Zd p F')) := by
    have e : Sum.elim (tLoc Zd p γ).f (locF' Zd p F') = fun k => Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a)
        (fun b => sgnP' D p b * frFac Zd.δ p b) k • baseChange₂ D p (Sum.elim (frame (lf D F0)) (frame F') k) := by
      funext k; cases k <;> rfl
    rw [e]
    exact gramInvE_loc Zd p _ _ hsK (gram_pair_ne γ.lam hΛ (lf D F0) F' rfl hP.1.1.2.2 _ rfl)
  refine ⟨n1, n2, ?_, ?_, hgen.1.2.2.1.2.1, iso_locF' Zd p F'⟩
  · rw [← dl_full]; exact hgen.1.2.2.2.1
  · rw [← dl_full]; exact local_discriminant_unit_of_det Zd p γ Z F' hZ hdet

theorem lprPart_of' (hE : LprExist Zd u u' F0 what₂) : LprPart Zd u u' F0 what₂ :=
  lprPart_of Zd hE (lprNondeg_holds Zd)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
