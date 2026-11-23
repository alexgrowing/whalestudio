import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ContinuousCw

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem gv_eq : GX X u u' D.host.rdE (gamW X u u' w) v =
    Gv (Tw u) (Tw u') (Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v)) := rfl

theorem sub_one_mulVec (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (x : Fin X.B.I.n → ℂ) :
    (M - 1) *ᵥ x = M *ᵥ x - x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

theorem frame_diff {m : ℕ} {N : ℕ} (V : Fin (m + 1) → Fin N → ℂ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (a' : Fin (m + 1)) : ∑ a'', A a'' a' • V a'' - V a' = ∑ a'', (A - 1) a'' a' • V a'' := by
  simp [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.one_apply]

section Main

variable (hw : OkPt X u u' w)

include hw in
theorem hgap_w : 1 - ((Tw u : ℝ) : ℂ) * (Tw u' : ℝ) *
    ((Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v))⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) *
      starRingEnd ℂ ((Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v))⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS))) ≠ 0 := by
  set Z := Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) with hZd
  have hG : 0 < Gv (Tw u) (Tw u') Z := by
    rw [← gv_eq X u u' w v]
    exact hw.2 v
  have hdet : IsUnit Z.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hD : Dl Z (D.R.rS + 1) = Z.det := by
      unfold Formalism.L2.SG.RealObj.Dl
      rw [dif_pos le_rfl]
      congr 1
    have hnn : (0 : ℝ) ≤ (Tw u : ℝ) * (Tw u' : ℝ) * ‖Dl Z D.R.rS‖ ^ 2 :=
      mul_nonneg (mul_nonneg (Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u).le
        (Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u').le) (sq_nonneg _)
    unfold Gv at hG
    rw [hD, h0, norm_zero, zero_pow two_ne_zero, zero_sub] at hG
    linarith
  exact gap_of_G Z hdet _ _ hG

include hw in
theorem yM_unit (c : FreeE w → ℂ) :
    (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
      Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) = Formalism.REAL.Jm (X.B.I.ε v) :=
  by
  have hC : IsUB (blkW w) (Cw w c) := by
      refine ⟨fun i => by simp [Cw], fun i j h => ?_⟩
      simp only [Cw, Matrix.of_apply] at h
      split_ifs at h with h1 h2
      · exact ⟨le_of_eq h1, by rw [h1]⟩
      · exact ⟨le_of_lt h2.1, h2.2⟩
      · exact absurd rfl h
  exact Yc_unitary (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Tw u : ℝ) (Tw u' : ℝ) (piW w) (blkW w) (fun a b => gram_frm (X := X) v u D.host.rdE a b)
    (fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
    (fun a => piW_invol (w := w) a)
    (fun a => piW_blk (w := w) a) (fun a b h hab => piW_anti (w := w) a b h hab)
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (hgap_w X u u' w v hw) hC

include hw in
theorem yM_F (c : FreeE w → ℂ) (a : Fin (D.R.rS + 1)) :
    Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Fw X u v a =
      ∑ a', Am (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) a' a • Fw X u v a' :=
  Yc_F (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Tw u : ℝ) (Tw u' : ℝ) (piW w) (fun a b => gram_frm (X := X) v u D.host.rdE a b)
    (fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
    (fun a => piW_invol (w := w) a)
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (hgap_w X u u' w v hw) a

include hw in
theorem yM_G (c : FreeE w → ℂ) (b : Fin (D.R.rS + 1)) :
    Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Gw X u u' w v b =
      ∑ b', Cw w c b' b • Gw X u u' w v b' :=
  Yc_G (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Tw u : ℝ) (Tw u' : ℝ) (piW w) (fun a b => gram_frm (X := X) v u D.host.rdE a b)
    (fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
    (fun a => piW_invol (w := w) a)
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (hgap_w X u u' w v hw) b

include hw in
theorem yM_isUB_A (c : FreeE w → ℂ) : IsUB (blkW w) (Am (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) := by
  unfold Am
  exact isUB_A (piW w) (fun a => piW_invol (w := w) a) (fun a => piW_blk (w := w) a)
    (fun a b h hab => piW_anti (w := w) a b h hab) (Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v))
    (fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b) (isUB_Cw w c)

theorem lt_last_set : {a : Fin (D.R.rS + 1) | a ≠ Fin.last D.R.rS} = {a | a.1 < D.R.rS} := by
  ext a
  simp only [Set.mem_setOf_eq]
  rw [← Fin.lt_last_iff_ne_last]
  exact Iff.rfl

theorem e_eq (b : Fin D.R.rS) : rv X.B.I v (X.eR b) =
    ((D.host.rdE : ℂ) ^ (D.R.rS - b.1)) • frm X u D.host.rdE v b.castSucc := by
  have hr : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D).ne'
  simp only [frm, famSc, fam, Fin.coe_castSucc, Fin.snoc_castSucc, smul_smul]
  rw [mul_inv_cancel₀ (pow_ne_zero _ hr), one_smul]

include hw in
theorem inN_u (c : FreeE w → ℂ) :
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))
      (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) := by
  have hr : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D).ne'
  have hF : ∀ b : Fin D.R.rS, Fw X u v b.castSucc =
      ((D.host.rdE : ℂ) ^ (D.R.rS - b.1))⁻¹ • rv X.B.I v (X.eR b) := by
    intro b
    show frm X u D.host.rdE v b.castSucc = _
    rw [e_eq X u v b, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hr), one_smul]
  have hspan : ∀ k, k ≤ D.R.rS → Submodule.span ℂ (Fw X u v '' {a | a.1 < k}) ≤
      spanLt (fun a => rv X.B.I v (X.eR a)) k := by
    intro k hk
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a.1 < k := ha
    obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc := ⟨⟨a.1, by omega⟩, Fin.ext rfl⟩
    rw [hF b]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ha', rfl⟩)
  have hA := yM_isUB_A X u u' w v hw c
  have hcol : ∀ a' : Fin (D.R.rS + 1),
      Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Fw X u v a' - Fw X u v a' ∈
        spanLt (fun a => rv X.B.I v (X.eR a)) a'.1 := by
    intro a'
    rw [yM_F X u u' w v hw c a', frame_diff]
    exact hspan a'.1 (Nat.lt_succ_iff.mp a'.2) (comb_mem X u v hA a')
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · show (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) - 1) *ᵥ rv X.B.I v (X.eR a) ∈ _
    have he : rv X.B.I v (X.eR a) = ((D.host.rdE : ℂ) ^ (D.R.rS - a.1)) • Fw X u v a.castSucc := by
      rw [hF a, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hr), one_smul]
    rw [sub_one_mulVec X, he, Matrix.mulVec_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ (hcol a.castSucc)
  · have hz : Fw X u v (Fin.last D.R.rS) = rv X.B.I v (X.zR u) := by
      simp [Fw, frm, famSc, fam]
    rw [sub_one_mulVec X, ← hz]
    exact hcol (Fin.last D.R.rS)
  · have hx : ∀ a, a ≠ Fin.last D.R.rS → hJ (X.B.I.ε v) (Fw X u v a) y = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc :=
        ⟨⟨a.1, Fin.val_lt_last ha⟩, Fin.ext rfl⟩
      rw [hF b, hJs_l, hy b, mul_zero]
    have hp := Yc_perpF (ε := X.B.I.ε v) (F := Fw X u v) (G := Gw X u u' w v) (T := (Tw u : ℝ))
      (T' := (Tw u' : ℝ)) (π := piW w) (blk := blkW w)
      (hFF := fun a b => gram_frm (X := X) v u D.host.rdE a b)
      (hGG := fun a b => hGG_w (X := X) (u := u) (u' := u') (w := w) v a b)
      (hπ := fun a => piW_invol (w := w) a) (hblk := fun a => piW_blk (w := w) a)
      (hanti := fun a b h hab => piW_anti (w := w) a b h hab)
      (hZ := fun c b => hZ_w (X := X) (u := u) (u' := u') (w := w) hw v c b)
      (hgap := hgap_w X u u' w v hw) (hC := isUB_Cw w c) y hx
    rw [lt_last_set] at hp
    rw [sub_one_mulVec X]
    exact hspan D.R.rS le_rfl hp

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
