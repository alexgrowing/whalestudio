import Formalism.LocalToGlobal.Columns.ChainLawExt
import Formalism.LocalToGlobal.Columns.ReducedMatrixExtensionEntry
import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Bridge

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem clL_base (hok : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hs : cst.sharp = true) :
    OcbBase Ch sel mu cst m2 where
  hX := hX
  hPr := hPr
  hCh := hCh
  hm := hok.hm
  cst_ok := hok.cst_ok
  sharp := hs
  psi0 := hok.psi0
  depthG := hok.depthG

theorem clL_bridge (hok : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hs : cst.sharp = true)
    {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j) (hb : ∀ P, L.h j b P = 1) (w : {w // w ∈ Pr.vGs}) (g : ↥(L.levG j b w).H)
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w.1)
    (hred : ∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (κ x) = g.1.1.mulVec (redV w.1 x)) :
    clL_ext (cOf R j) κ ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) ∧
      LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t j (R.N j) (cOf R j) (clL_ext (cOf R j) κ).toLinearMap =
        (((L.levG j b w).lam g : X.Kˣ) : X.K) := by
  classical
  have hB := clL_base hok hX hPr hCh hs

  have hpat : ocbXPat R.k R.rS j R.t g.1 := by
    obtain ⟨g', hg', hred'⟩ := (hok.grpG j b w g.1).1 g.2
    rw [hb] at hg'
    exact (ocbGrpGLoc_holds Ch sel mu cst m2 hB j hj w g.1).1 ⟨g', hg', hred'⟩
  obtain ⟨hk, hr, hrN, -⟩ := ranks_frame_inequalities R hB.hm hj
  have hq := ciQ_mem w.1
  have hu := ciQ_notMem_sq hB.hX hB.hPr w.2
  have hq0 := ciQ_ne_zero hu
  have hmS : R.m = 2 * R.rS + 2 := by
    unfold Ranks.rS
    obtain ⟨a, ha⟩ := R.m_even
    have := R.two_le_m
    omega
  have hrr : R.r = R.k + 2 * R.rS + 1 := by
    unfold Ranks.r
    omega
  have hcj : cOf R j + j = 2 * R.rS + 1 := by
    have := hB.hm
    unfold cOf
    omega
  have hJat : Jat (Pr := Pr) cst.sharp j w.1 = LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    unfold Jat
    rw [if_pos w.2, hB.sharp, if_pos rfl]

  set Gm := LinearMap.toMatrix' κ.toLinearMap with hGm
  have hκi : κ.symm ∈ GLint X.E (R.N j) w.1 := (GLint X.E (R.N j) w.1).inv_mem hκ
  have hGi : ∀ i i', IntAt w.1 (Gm i i') := by
    intro i i'
    rw [hGm, LinearMap.toMatrix'_apply]
    exact (ciMem_stdAt w.1 _).1 ((hκ _).2 (ciSingle_mem i')) i
  have hGii : ∀ i i', IntAt w.1 (LinearMap.toMatrix' κ.symm.toLinearMap i i') := by
    intro i i'
    rw [LinearMap.toMatrix'_apply]
    exact (ciMem_stdAt w.1 _).1 ((hκi _).2 (ciSingle_mem i')) i
  have hGred : ∀ i i', redP w.1 (Gm i i') = g.1.1 i i' := by
    intro i i'
    rw [ciEntry hred i i', hGm, LinearMap.toMatrix'_apply]
    rfl
  have hE1 := clL_extM_mul (cOf R j) κ
  have hE2 := clL_extM_mul' (cOf R j) κ
  have hap : ∀ v, clL_ext (cOf R j) κ v = (ciExtM (cOf R j) Gm).mulVec v := fun v => clL_ext_apply _ κ v
  have he : ∀ (A : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E), (∀ i i', IntAt w.1 (A i i')) → ∀ l l' : Fin (R.N j),
      IntAt w.1 (A l l' * ((qOf w.1 : ℕ) : X.E) ^ (LocE.scE (R.N j) (fun i => i + 1) l'.1 - LocE.scE (R.N j) (fun i => i + 1) l.1)) := by
    intro A hA l l'
    rw [ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one]
    exact hA _ _
  have hS : clL_ext (cOf R j) κ ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) :=
    ciEquiv_stab (fun v hv => ciExtM_maps hq0 Gm _ (he Gm hGi) v hv)
      (fun v hv => ciExtM_maps hq0 _ _ (he _ hGii) v hv)
  have hM := reducedMatrix_blockExtension (P := w.1) (q := qOf w.1) Gm _ hap
  have hJ : clL_ext (cOf R j) κ ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    refine mem_parahoric_of_blockTriangular hq hu hk hr (by omega) hS ?_ ?_ ?_
    · intro y y' hlt
      rw [hM]
      split_ifs with h1 h2
      · rw [hGred]
        by_contra hnz
        have hne : y.1 ≠ y'.1 := fun he' => by
          have hlt' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y'.1) <
              betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y.1) := hlt
          rw [he'] at hlt'
          exact lt_irrefl _ hlt'
        have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)
        refine not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inl ?_) hall
        rw [← hrr]
        exact hlt
      · subst h2
        exact absurd hlt (lt_irrefl _)
      · rfl
    · intro y hy
      rw [hM]
      split_ifs with h1 h2
      · rw [hGred]
        have hyk : y.1 < R.k + j := by
          rw [framePos_of_lt_dim h1.1, hrr] at hy
          split_ifs at hy <;> omega
        have h3 := hpat.1 y.1 hyk
        unfold ocbM at h3
        rw [dif_pos ⟨h1.1, h1.1⟩] at h3
        exact h3
      · rfl
      · exact absurd rfl h2
    · intro y y' hy hy'
      rw [hM]
      split_ifs with h1 h2
      · rw [hGred]
        by_contra hnz
        have hne : y.1 ≠ y'.1 := by
          intro he'
          rw [he'] at hy
          omega
        have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)
        exact not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inr ⟨hy, hy'⟩) hall
      · subst h2
        omega
      · rfl
  refine ⟨hJ, ?_⟩

  have hr1 : clL_ext (cOf R j) κ ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩) := by
    rw [hb]
    refine Subgroup.mem_inf.2 ⟨extended_matrix_in_reduction _ _ hE1 hE2, Subgroup.mem_comap.2 ?_⟩
    simpa [MulAut.conj_apply, hJat] using hJ
  have hlam := hok.chrG j b w g κ (clL_ext (cOf R j) κ) hr1 (fun x => clL_ext_inX _ κ x) hred
  rw [hlam]
  unfold chiInv
  rw [hb]
  have hn1 : Loc.n1Arg (clL_ext (cOf R j) κ) = 0 := by
    unfold Loc.n1Arg
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < cOf R j - 1 := Finset.mem_range.1 hi
    unfold Loc.atN
    rw [dif_pos (by omega)]
    have e1 : (⟨R.N j + i, by omega⟩ : Fin (R.N j + cOf R j)) = Fin.natAdd (R.N j) ⟨i, by omega⟩ := rfl
    rw [e1, clL_ext_natAdd]
    unfold Loc.eN
    simp
  rw [hn1, hok.cst_ok.psi_int _ 0 (ChainCounts.intAt_zero _), inv_one, one_mul]
  unfold lamRow
  rw [if_pos w.2, hs, if_pos rfl]
  simp

end Bridge

end Formalism.L2.Col
