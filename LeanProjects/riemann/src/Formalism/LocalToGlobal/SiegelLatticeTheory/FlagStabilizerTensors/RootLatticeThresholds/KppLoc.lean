import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFrameW
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppIdx
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRhoX

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx

section Gen

variable {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {g : ℕ}

theorem zmod_Wq (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g c) : c ∈ Wq I w := by
  obtain ⟨t, ht, rfl⟩ := h
  have : (g : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    have := iE_mem (I := I) hg
    simpa [iE] using this
  exact Wq_mul' this ht

theorem zmod_sg {c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g c) : ZMod' I g (sg I c) := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨sg I t, DictLat.sigR_int I ht, by rw [map_mul, sg_natCast]⟩

theorem mL_le (hg : (g : 𝓞 I.E) ∈ w.asIdeal) : mL I g ≤ Lq I w := by
  unfold mL
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have := smul_mem I w hg hx
  simpa using this

theorem hhat_neg_left (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I (-u) v = -hhat I u v := by
  have := hhat_sub_left I 0 u v
  rwa [zero_sub, DictLat.hhat_zero_left, zero_sub] at this

theorem hhat_neg_right (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I u (-v) = -hhat I u v := by
  have := hhat_sub_right I u 0 v
  rwa [zero_sub, DictLat.hhat_zero_right, zero_sub] at this

theorem pair_right (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {u : Fin I.n → I.E ⊗[I.F] Af I.F} (hu : u ∈ I.Lf)
    {S : Set (VA I)} (hS : ∀ s ∈ S, hhat I u s ∈ Wq I w) {v : VA I} (hv : InMod I g S v) : hhat I u v ∈ Wq I w := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  clear hv
  rw [DictLat.hhat_add_right]
  refine add_mem ?_ (hhat_Lq_right hu (mL_le hg hz))
  induction hy using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => rw [DictLat.hhat_zero_right]; exact zero_mem _
  | add a b _ _ ha hb => rw [DictLat.hhat_add_right]; exact add_mem ha hb
  | smul r a _ ha =>
    show hhat I u ((r : I.E ⊗[I.F] Af I.F) • a) ∈ Wq I w
    rw [DictLat.hhat_smul_right]; exact Wq_mul ha r.2

theorem pair_left (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {v : Fin I.n → I.E ⊗[I.F] Af I.F} (hv : v ∈ I.Lf)
    {S : Set (VA I)} (hS : ∀ s ∈ S, hhat I s v ∈ Wq I w) {u : VA I} (hu : InMod I g S u) : hhat I u v ∈ Wq I w := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  clear hu
  rw [DictLat.hhat_add_left]
  refine add_mem ?_ ?_
  · induction hy using Submodule.span_induction with
    | mem s hs => exact hS s hs
    | zero => rw [DictLat.hhat_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [DictLat.hhat_add_left]; exact add_mem ha hb
    | smul r a _ ha =>
      show hhat I ((r : I.E ⊗[I.F] Af I.F) • a) v ∈ Wq I w
      rw [DictLat.hhat_smul_left]; exact Wq_mul ha (DictLat.sigR_int I r.2)
  · have hgW : (g : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
      have := iE_mem (I := I) hg
      simpa [iE] using this
    unfold mL at hz
    induction hz using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨x, hx, rfl⟩ := hs
      rw [DictLat.hhat_smul_left, sg_natCast]
      exact Wq_mul' hgW (dual_hat_integral I x hx v hv)
    | zero => rw [DictLat.hhat_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [DictLat.hhat_add_left]; exact add_mem ha hb
    | smul r a _ ha =>
      show hhat I ((r : I.E ⊗[I.F] Af I.F) • a) v ∈ Wq I w
      rw [DictLat.hhat_smul_left]; exact Wq_mul ha (DictLat.sigR_int I r.2)

theorem dir_col (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {x : I.Gf} {u v : VA I} (hu : u ∈ I.Lf) {S : Set (VA I)}
    (hS : ∀ s ∈ S, hhat I u s ∈ Wq I w) (hx : InMod I g S ((I.fmat x - 1) *ᵥ v)) :
    hhat I u (I.fmat x *ᵥ v) - hhat I u v ∈ Wq I w := by
  have := pair_right hg hu hS hx
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, hhat_sub_right] at this

theorem dual_col (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {x : I.Gf} {u v : VA I} (hv : v ∈ I.Lf) {S : Set (VA I)}
    (hS : ∀ s ∈ S, hhat I s v ∈ Wq I w) (hx : InMod I g S ((I.fmat x⁻¹ - 1) *ᵥ u)) :
    hhat I u (I.fmat x *ᵥ v) - hhat I u v ∈ Wq I w := by
  have h1 : hhat I u (I.fmat x *ᵥ v) = hhat I (I.fmat x⁻¹ *ᵥ u) v := by
    have := hhat_fmat I x (I.fmat x⁻¹ *ᵥ u) v
    rw [Matrix.mulVec_mulVec, ← fmat_mul, mul_inv_cancel, fmat_one, Matrix.one_mulVec] at this
    exact this
  have := pair_left hg hv hS hx
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, hhat_sub_left, ← h1] at this

variable {p : ℕ} {r : ℕ}

theorem cong_dir (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {fr frd : Fin r → VA I} (hfrd : ∀ i, frd i ∈ I.Lf)
    (hgr : GramW w fr frd) {x : I.Gf} (i j : Fin r) {S : Set (VA I)}
    (hS : ∀ s ∈ S, ∃ j', s = fr j' ∧ j' ≠ i) (hx : InMod I g S ((I.fmat x - 1) *ᵥ fr j)) :
    CongW (w := w) p (hhat I (frd i) (I.fmat x *ᵥ fr j)) (if i = j then 1 else 0) := by
  have h1 := dir_col hg (hfrd i) (fun s hs => by
    obtain ⟨j', rfl, hj'⟩ := hS s hs
    have := hgr i j'
    rwa [if_neg (Ne.symm hj'), sub_zero] at this) hx
  refine congW_of_sub ?_ h1
  refine congW_of_sub (t := ((if i = j then 1 else 0 : ℤ) : I.E ⊗[I.F] Af I.F)) ?_ ?_
  · have := congW_intCast (I := I) (w := w) (p := p) (if i = j then 1 else 0)
    convert this using 2
    split_ifs <;> simp
  · have := hgr i j
    convert this using 2
    split_ifs <;> simp

theorem cong_dual (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {fr frd : Fin r → VA I} (hfr : ∀ j, fr j ∈ I.Lf)
    (hgr : GramW w fr frd) {x : I.Gf} (i j : Fin r) {S : Set (VA I)}
    (hS : ∀ s ∈ S, ∃ i', s = frd i' ∧ i' ≠ j) (hx : InMod I g S ((I.fmat x⁻¹ - 1) *ᵥ frd i)) :
    CongW (w := w) p (hhat I (frd i) (I.fmat x *ᵥ fr j)) (if i = j then 1 else 0) := by
  have h1 := dual_col hg (hfr j) (fun s hs => by
    obtain ⟨i', rfl, hi'⟩ := hS s hs
    have := hgr i' j
    rwa [if_neg hi', sub_zero] at this) hx
  refine congW_of_sub ?_ h1
  refine congW_of_sub (t := ((if i = j then 1 else 0 : ℤ) : I.E ⊗[I.F] Af I.F)) ?_ ?_
  · have := congW_intCast (I := I) (w := w) (p := p) (if i = j then 1 else 0)
    convert this using 2
    split_ifs <;> simp
  · have := hgr i j
    convert this using 2
    split_ifs <;> simp

theorem inMod_neg {S : Set (VA I)} {v : VA I} (h : InMod I g S v) : InMod I g S (-v) := neg_mem h

end Gen

variable {D : D7} (X : HidaSetting D)

theorem hrD (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

def fr (ob : Bool) (j : Fin D.R.r) : VA X.B.I :=
  if h1 : j.1 < D.R.rS then X.e0 ⟨j.1, h1⟩
  else if h2 : j.1 < D.R.rS + D.R.k then
    (if ob then X.bw ⟨j.1 - D.R.rS, by omega⟩ else X.bwd ⟨D.R.k - 1 - (j.1 - D.R.rS), by omega⟩)
  else if j.1 = D.R.rS + D.R.k then X.z0
  else if h4 : j.1 - (D.R.rS + D.R.k + 1) < D.R.rS then X.f0 ⟨D.R.rS - 1 - (j.1 - (D.R.rS + D.R.k + 1)), by omega⟩
  else 0

def frd (ob : Bool) (j : Fin D.R.r) : VA X.B.I :=
  if h1 : j.1 < D.R.rS then X.f0 ⟨j.1, h1⟩
  else if h2 : j.1 < D.R.rS + D.R.k then
    (if ob then X.bwd ⟨j.1 - D.R.rS, by omega⟩ else X.bw ⟨D.R.k - 1 - (j.1 - D.R.rS), by omega⟩)
  else if j.1 = D.R.rS + D.R.k then -X.z0
  else if h4 : j.1 - (D.R.rS + D.R.k + 1) < D.R.rS then X.e0 ⟨D.R.rS - 1 - (j.1 - (D.R.rS + D.R.k + 1)), by omega⟩
  else 0

def rv {n : ℕ} (a : Fin n) : Fin n := ⟨n - 1 - a.1, by omega⟩

@[simp] theorem rv_val {n : ℕ} (a : Fin n) : (rv a).1 = n - 1 - a.1 := rfl

theorem rv_rv {n : ℕ} (a : Fin n) : rv (rv a) = a := Fin.ext (by simp <;> omega)

theorem frame_isotropic (ob : Bool) (a : Fin D.R.rS) : fr X ob (xI (hrD D) a) = X.e0 a := by
  unfold fr; rw [dif_pos (show (xI (hrD D) a).1 < D.R.rS from a.2)]; rfl

theorem fr_w (ob : Bool) (i : Fin D.R.k) : fr X ob (wI (hrD D) i) = if ob then X.bw i else X.bwd (rv i) := by
  unfold fr
  rw [dif_neg (show ¬ (wI (hrD D) i).1 < D.R.rS by simp), dif_pos (show (wI (hrD D) i).1 < D.R.rS + D.R.k by simp)]
  congr 1 <;> congr 1 <;> ext <;> simp

theorem frame_anisotropic (ob : Bool) : fr X ob (zI (hrD D)) = X.z0 := by
  unfold fr
  rw [dif_neg (show ¬ (zI (hrD D)).1 < D.R.rS by simp <;> omega),
    dif_neg (show ¬ (zI (hrD D)).1 < D.R.rS + D.R.k by simp), if_pos (by simp)]

theorem fr_y (ob : Bool) (a : Fin D.R.rS) : fr X ob (yI (hrD D) a) = X.f0 (rv a) := by
  unfold fr
  rw [dif_neg (show ¬ (yI (hrD D) a).1 < D.R.rS by simp <;> omega),
    dif_neg (show ¬ (yI (hrD D) a).1 < D.R.rS + D.R.k by simp <;> omega), if_neg (by simp <;> omega),
    dif_pos (show (yI (hrD D) a).1 - (D.R.rS + D.R.k + 1) < D.R.rS by simp)]
  congr 1; ext; simp

theorem dual_frame_isotropic (ob : Bool) (a : Fin D.R.rS) : frd X ob (xI (hrD D) a) = X.f0 a := by
  unfold frd; rw [dif_pos (show (xI (hrD D) a).1 < D.R.rS from a.2)]; rfl

theorem frd_w (ob : Bool) (i : Fin D.R.k) : frd X ob (wI (hrD D) i) = if ob then X.bwd i else X.bw (rv i) := by
  unfold frd
  rw [dif_neg (show ¬ (wI (hrD D) i).1 < D.R.rS by simp), dif_pos (show (wI (hrD D) i).1 < D.R.rS + D.R.k by simp)]
  congr 1 <;> congr 1 <;> ext <;> simp

theorem dual_frame_anisotropic (ob : Bool) : frd X ob (zI (hrD D)) = -X.z0 := by
  unfold frd
  rw [dif_neg (show ¬ (zI (hrD D)).1 < D.R.rS by simp <;> omega),
    dif_neg (show ¬ (zI (hrD D)).1 < D.R.rS + D.R.k by simp), if_pos (by simp)]

theorem frd_y (ob : Bool) (a : Fin D.R.rS) : frd X ob (yI (hrD D) a) = X.e0 (rv a) := by
  unfold frd
  rw [dif_neg (show ¬ (yI (hrD D) a).1 < D.R.rS by simp <;> omega),
    dif_neg (show ¬ (yI (hrD D) a).1 < D.R.rS + D.R.k by simp <;> omega), if_neg (by simp <;> omega),
    dif_pos (show (yI (hrD D) a).1 - (D.R.rS + D.R.k + 1) < D.R.rS by simp)]
  congr 1; ext; simp

end Formalism.L2.SG.Pf.KppLoc
