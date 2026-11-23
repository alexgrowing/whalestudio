import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.ExpSecondHermitianMemLevel

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TPresMain

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}

lemma entry_cd (a b : Fin (2 * r + k + 1)) : ContDiff ℝ ∞ (fun g : Mx k r => g a b) := by
  exact (contDiff_apply ℝ ℂ b).comp (contDiff_apply ℝ (Fin (2 * r + k + 1) → ℂ) a)

lemma inv_glev {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg.1, Formalism.QuantumDeterminants.GBasic.Hpk_sq]

private lemma contDiff_mulVec_apply_of_contDiff {M : Mx k r → Mx k r} (hM : ∀ a b, ContDiff ℝ ∞ (fun g => M g a b))
    (v : (Fin (2 * r + k + 1) → ℂ)) (p : Fin (2 * r + k + 1)) : ContDiff ℝ ∞ (fun g => (M g *ᵥ v) p) := by
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun q _ => (hM p q).mul contDiff_const

private lemma contDiff_mul_left_apply (H : Mx k r) (a b : Fin (2 * r + k + 1)) :
    ContDiff ℝ ∞ (fun g : Mx k r => (H * g) a b) := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun c _ => contDiff_const.mul (entry_cd c b)

private lemma contDiff_hpk_conjTranspose_hpk_apply (a b : Fin (2 * r + k + 1)) :
    ContDiff ℝ ∞ (fun g : Mx k r => (Hpk k r * gᴴ * Hpk k r) a b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hs : ∀ c d : Fin (2 * r + k + 1), ContDiff ℝ ∞ (fun g : Mx k r => star (g c d)) :=
    fun c d => Complex.conjCLE.contDiff.comp (entry_cd c d)
  exact ContDiff.sum fun c _ => (ContDiff.sum fun d _ => contDiff_const.mul (hs c d)).mul contDiff_const

lemma ybv_sg (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothG k r i (fun g => ybv k r z i g j) := by
  refine ⟨fun g => ybv k r z i g j, ?_, fun _ _ => rfl⟩
  simp only [ybv, herm, dotProduct, Matrix.mulVec_mulVec]
  exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_mulVec_apply_of_contDiff (contDiff_mul_left_apply (Hpk k r)) _ x)

lemma yv_sg (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothG k r i (fun g => yv k r z i g j) := by
  refine ⟨fun g => ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z i) (posL k r i j), ?_, fun g hg => ?_⟩
  · exact contDiff_mulVec_apply_of_contDiff contDiff_hpk_conjTranspose_hpk_apply _ _
  · simp only [yv, inv_glev hg]

section Ops

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

lemma chatL_smooth (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothG k r i (fun g => a g j)) (hβ : ∀ j, SmoothG k r i (fun g => β g j))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (chatL (EH k r) (posL k r i) u a β f) := by
  unfold chatL
  exact sl_sum' _ fun i0 => sl_sum' _ fun j0 =>
    sl_smul_fun (sg_mul (sg_mul (sg_const _) (hβ i0)) (ha j0)) (qminor_smooth hD _ _ u f hf)

lemma chatL_local (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chatL (EH k r) (posL k r i) u a β f g = chatL (EH k r) (posL k r i) u a β f' g := by
  simp only [chatL]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun j0 _ => ?_
  congr 1
  exact qminor_local hD _ _ u f f' h g hg

lemma chatL_clm (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chatL (EH k r) (posL k r i) u a β (fun y => L (f y)) g = L (chatL (EH k r) (posL k r i) u a β f g) := by
  simp only [chatL, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun j0 _ => ?_
  congr 1
  exact qminor_clm hD _ _ u L f hf g hg

private lemma smoothLev_ite_zero (P : Prop) [Decidable P] {F : Mx k r → E} (hF : P → SmoothLev k r i D F) :
    SmoothLev k r i D (fun g => if P then F g else 0) := by
  by_cases hP : P
  · simp only [hP, ↓reduceIte]
    exact hF hP
  · simp only [hP, ↓reduceIte]
    exact sl_zero

lemma second_capelli_minor_smooth (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothG k r i (fun g => a g j)) (ha' : ∀ j, SmoothG k r i (fun g => a' g j))
    (hβ : ∀ j, SmoothG k r i (fun g => β g j)) (hβ' : ∀ j, SmoothG k r i (fun g => β' g j))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (chat2L (EH k r) (posL k r i) u a a' β β' f) := by
  unfold chat2L
  exact sl_sum' _ fun i0 => sl_sum' _ fun i1 => sl_sum' _ fun j0 => sl_sum' _ fun j1 =>
    smoothLev_ite_zero _ fun _ => sl_smul_fun
      (sg_mul (sg_mul (sg_const _) (sg_sub (sg_mul (hβ i0) (hβ' i1)) (sg_mul (hβ i1) (hβ' i0))))
        (sg_sub (sg_mul (ha j0) (ha' j1)) (sg_mul (ha j1) (ha' j0))))
      (qminor_smooth hD _ _ u f hf)

lemma second_capelli_minor_local (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' f g = chat2L (EH k r) (posL k r i) u a a' β β' f' g := by
  simp only [chat2L]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun i1 _ =>
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 _ => ?_
  split_ifs
  · congr 1
    exact qminor_local hD _ _ u f f' h g hg
  · rfl

lemma second_capelli_minor_continuousLinear (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' (fun y => L (f y)) g =
      L (chat2L (EH k r) (posL k r i) u a a' β β' f g) := by
  simp only [chat2L, map_sum]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun i1 _ =>
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 _ => ?_
  split_ifs
  · rw [map_smul]
    congr 1
    exact qminor_clm hD _ _ u L f hf g hg
  · exact (map_zero L).symm

lemma tl_smooth (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2)
    (f : Mx k r → E) (hf : SmoothLev k r i D f) : SmoothLev k r i D (tL k r z z' i Y p q f) := by
  fin_cases p <;> fin_cases q
  · exact qminor_smooth hD (fun j => j) (fun j => j) _ f hf
  · exact sl_neg (chatL_smooth hD _ (fun _ => xv k r z' i) (ybv k r z i) (fun _ => sg_const _)
      (fun j => ybv_sg z j) f hf)
  · exact sl_neg (chatL_smooth hD _ (yv k r z i) (fun _ => xbv k r z' i) (fun j => yv_sg z j)
      (fun _ => sg_const _) f hf)
  · exact sl_neg (second_capelli_minor_smooth hD _ (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i)
      (fun j => yv_sg z j) (fun _ => sg_const _) (fun j => ybv_sg z j) (fun _ => sg_const _) f hf)

lemma tl_local (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2)
    (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    tL k r z z' i Y p q f g = tL k r z z' i Y p q f' g := by
  fin_cases p <;> fin_cases q
  · exact qminor_local hD (fun j => j) (fun j => j) _ f f' h g hg
  · exact congrArg Neg.neg (chatL_local hD _ (fun _ => xv k r z' i) (ybv k r z i) f f' h g hg)
  · exact congrArg Neg.neg (chatL_local hD _ (yv k r z i) (fun _ => xbv k r z' i) f f' h g hg)
  · exact congrArg Neg.neg (second_capelli_minor_local hD _ (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i)
      (fun _ => xbv k r z' i) f f' h g hg)

lemma tl_clm (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    tL k r z z' i Y p q (fun y => L (f y)) g = L (tL k r z z' i Y p q f g) := by
  fin_cases p <;> fin_cases q
  · exact qminor_clm hD (fun j => j) (fun j => j) _ L f hf g hg
  · exact (congrArg Neg.neg (chatL_clm hD _ (fun _ => xv k r z' i) (ybv k r z i) L f hf g hg)).trans
      (map_neg L _).symm
  · exact (congrArg Neg.neg (chatL_clm hD _ (yv k r z i) (fun _ => xbv k r z' i) L f hf g hg)).trans
      (map_neg L _).symm
  · exact (congrArg Neg.neg (second_capelli_minor_continuousLinear hD _ (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i)
      (fun _ => xbv k r z' i) L f hf g hg)).trans (map_neg L _).symm

end Ops

lemma one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z := by
  simp [UWset, UH]

lemma one_mem_Nlev : (1 : Mx k r) ∈ Nlev k r i := by
  simp [Nlev, Formalism.QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]

private lemma mul_mem_Slev_of_mem_UWset_of_mem_Nlev {z : (Fin (2 * r + k + 1) → ℂ)} {h m : Mx k r} (hh : h ∈ UWset k r z)
    (hm : m ∈ Nlev k r i) : h * m ∈ Slev k r z i := by
  simp only [Slev, Set.mem_setOf_eq]
  exact ⟨h, hh, m, hm, rfl⟩

theorem qnTPres_of (hT : TInvariant) : TPreservesFF := by
  intro Wp Wq _ _ _ _ k r z z' π π' i D Y p q hz hz' hDom J hJ
  simp only [FFl, Set.mem_setOf_eq] at hJ ⊢
  obtain ⟨hs, hL, hR, hW⟩ := hJ
  have hD : IsOpen D := hDom.1
  refine ⟨tl_smooth hD z z' Y p q J hs, ?_, ?_, ?_⟩
  · intro g hg n hn
    have e := hT (Wq →L[ℂ] Wp) k r z z' i D J Y p q hz hz' hDom hs (1 * n) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z) hn)
      (1 * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z') one_mem_Nlev) g hg
    simp only [one_mul, mul_one] at e
    have hloc : ∀ x ∈ Glev k r i ∩ D,
        J (n * x) = (psi k r z cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (J x) := by
      intro x hx
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      exact hL x hx n hn
    rw [← e, tl_local hD z z' Y p q _ _ hloc g hg, tl_clm hD z z' Y p q _ J hs g hg,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  · intro g hg n hn
    have e := hT (Wq →L[ℂ] Wp) k r z z' i D J Y p q hz hz' hDom hs (1 * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z) one_mem_Nlev)
      (1 * n) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z') hn) g hg
    simp only [one_mul, mul_one] at e
    have hloc : ∀ x ∈ Glev k r i ∩ D,
        J (x * n) = (psi k r z' cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (J x) := by
      intro x hx
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      exact hR x hx n hn
    rw [← e, tl_local hD z z' Y p q _ _ hloc g hg, tl_clm hD z z' Y p q _ J hs g hg,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  · intro g hg h hh h' hh'
    have e := hT (Wq →L[ℂ] Wp) k r z z' i D J Y p q hz hz' hDom hs (h * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev hh one_mem_Nlev)
      (h' * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev hh' one_mem_Nlev) g hg
    simp only [mul_one] at e
    obtain ⟨L, hLx⟩ : ∃ L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp), ∀ A, L A = (π h).comp (A.comp (π' h')) :=
      ⟨(ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (π' h')),
        fun A => by simp⟩
    have hloc : ∀ x ∈ Glev k r i ∩ D, J (h * x * h') = L (J x) := by
      intro x hx
      rw [hLx]
      exact hW x hx h hh h' hh'
    rw [← e, tl_local hD z z' Y p q _ _ hloc g hg, tl_clm hD z z' Y p q L J hs g hg, hLx]

theorem qnTPres_of' (hT : TInvariant) (_ : EabPres) : TPreservesFF := by
  exact qnTPres_of hT

end Formalism.FourierDecayAlt.Q.TPresMain
