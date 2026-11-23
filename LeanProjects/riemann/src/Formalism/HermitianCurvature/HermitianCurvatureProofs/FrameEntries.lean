import Formalism.HermitianCurvature.StatementQr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace FrameEntries

section Hom

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ldV_smul (X : Mx k r) (c : ℂ) (f : Mx k r → E) : Q.LdV X (fun x => c • f x) = fun x => c • Q.LdV X f x := by
  funext x
  unfold Q.LdV
  by_cases hc : c = 0
  · simp [hc]
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * x)) 0
  · exact deriv_const_smul c hd
  · rw [deriv_zero_of_not_differentiableAt hd, smul_zero, deriv_zero_of_not_differentiableAt]
    intro h
    apply hd
    have h2 : DifferentiableAt ℝ (fun t : ℝ => c⁻¹ • c • f (NormedSpace.exp ((t : ℂ) • X) * x)) 0 :=
      h.const_smul c⁻¹
    simpa [smul_smul, inv_mul_cancel₀ hc] using h2

theorem lZ_smul (Z : Mx k r) (c : ℂ) (f : Mx k r → E) :
    LZ (Hpk k r) Z (fun x => c • f x) = fun x => c • LZ (Hpk k r) Z f x := by
  funext x
  unfold LZ
  simp only [ldV_smul, smul_add]
  rw [smul_comm Complex.I c]

theorem foldl_smul (L : List ((Mx k r → E) → Mx k r → E)) (c : ℂ)
    (hL : ∀ T ∈ L, ∀ f, T (fun x => c • f x) = fun x => c • T f x) (f : Mx k r → E) :
    L.foldl (fun h T => T h) (fun x => c • f x) = fun x => c • L.foldl (fun h T => T h) f x := by
  induction L generalizing f with
  | nil => rfl
  | cons T L ih =>
    simp only [List.foldl_cons]
    rw [hL T (by simp) f]
    exact ih (fun T' hT' => hL T' (by simp [hT'])) (T f)

theorem capLft_smul {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (w c : ℂ) (f : Mx k r → E) :
    capLft k r Bs w (fun x => c • f x) = fun x => c • capLft k r Bs w f x := by
  funext x
  unfold capLft qmFrev
  simp only [Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [foldl_smul _ c ?_ f]
  · exact smul_comm _ _ _
  · intro T hT g
    simp only [List.mem_ofFn] at hT
    obtain ⟨j, rfl⟩ := hT
    funext y
    simp only [lZ_smul, Pi.add_apply]
    split_ifs <;> simp [smul_comm c, smul_add]

end Hom

section Grp

variable {k r : ℕ}

private theorem Hpk_mul_self_eq_one (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.2
  have hj := j.2
  let p : ℕ → ℕ := fun a => if a < r ∨ r + k < a then 2 * r + k - a else a
  have hp : ∀ a < 2 * r + k + 1, p a < 2 * r + k + 1 := by
    intro a ha
    simp only [p]
    split_ifs <;> omega
  have hent : ∀ a b : Fin (2 * r + k + 1),
      Hpk k r a b = if (b : ℕ) = p a then (if (a : ℕ) = r + k then -1 else 1) else 0 := by
    intro a b
    have := a.2
    have := b.2
    simp only [Hpk, p, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  rw [Finset.sum_eq_single ⟨p i, hp i hi⟩]
  · rw [hent, hent]
    simp only [p, Fin.ext_iff]
    split_ifs <;> first | omega | norm_num
  · intro b _ hb
    rw [hent i b]
    have hb' : (b : ℕ) ≠ p i := fun h => hb (Fin.ext h)
    simp [hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_inv_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', Hpk_mul_self_eq_one]
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl)

theorem inv_mul_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (Matrix.isUnit_det_of_right_inverse (mul_inv_uh hg))

theorem glev_inv {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  simp only [Glev, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hfix⟩ := hg
  have h1 := mul_inv_uh hU
  have h2 := inv_mul_uh hU
  refine ⟨?_, fun a ha => ?_⟩
  · have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
    show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
    calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · obtain ⟨e1, e2⟩ := hfix a ha
    constructor
    · conv_lhs => rw [← e1]
      rw [mulVec_mulVec, h2, one_mulVec]
    · conv_lhs => rw [← e2]
      rw [mulVec_mulVec, h2, one_mulVec]

theorem herm_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ x) y = herm (Hpk k r) x (g⁻¹ *ᵥ y) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have key2 : Hpk k r * g = (g⁻¹)ᴴ * Hpk k r := by
    calc Hpk k r * g = (g * g⁻¹)ᴴ * (Hpk k r * g) := by
          rw [mul_inv_uh hg, conjTranspose_one, Matrix.one_mul]
      _ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (g⁻¹)ᴴ * Hpk k r := by rw [hg']
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [key2]

private theorem hpk_conjTranspose_eq_self (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  have := i.2
  have := j.2
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | norm_num

theorem herm_self (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have hH := hpk_conjTranspose_eq_self k r
  have hs : star (herm (Hpk k r) z z) = herm (Hpk k r) z z := by
    unfold herm
    conv_rhs => rw [Matrix.star_dotProduct]
    rw [Matrix.star_mulVec, hH, ← Matrix.dotProduct_mulVec]
  have him : (herm (Hpk k r) z z).im = 0 := by
    have h2 := congrArg Complex.im hs
    simp at h2
    linarith
  unfold Tz
  apply Complex.ext <;> simp [him]

theorem frame_inv {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) {m : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs) :
    IsFrameOf k r [g⁻¹ *ᵥ z] (fun a => g⁻¹ *ᵥ Bs a) := by
  have hi := glev_inv hg
  refine ⟨fun a => Qx8.inWb_mulVec hi (hB.1 a), fun a b => ?_, fun a v hv => ?_⟩
  · rw [Qx2.herm_uh hi.1]; exact hB.2.1 a b
  · rw [List.mem_singleton] at hv
    rw [hv, Qx2.herm_uh hi.1]; exact hB.2.2 a z (by simp)

end Grp

section Main

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem uC_last (Y : ℂ) : uC k r (Fin.last r) Y = Y + (k : ℂ) / 2 := by
  unfold uC mdim
  simp <;> ring

theorem uC_succ (Y : ℂ) : uC k r i (Y + 1) = uC k r i Y + 1 := by
  unfold uC
  ring

theorem chatA_eval (u : ℂ) (a β : Fin (mdim k r i) → ℂ) (ψ : SV k r i D E) (g : Mx k r) :
    (chatA (EV k r i D E) u a β ψ).1 g =
      ∑ p : Fin (mdim k r i), ∑ q : Fin (mdim k r i), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β p * a q) • (qminor (EV k r i D E) (skip1 p) (skip1 q) u ψ).1 g := by
  unfold chatA
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply]

theorem chYY_eval (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (ψ : SV k r i D E) {g : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) :
    (chYY (EV k r i D E) u (yV k r z i D E) (etaV k r z i D E) ψ).1 g =
      (chatA (EV k r i D E) u (yv k r z i g) (ybv k r z i g) ψ).1 g := by
  rw [chatA_eval]
  unfold chYY
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have h1 : ((etaV k r z i D E p * yV k r z i D E q * qminor (EV k r i D E) (skip1 p) (skip1 q) u) ψ).1 g =
      ybv k r z i g p • yv k r z i g q • (qminor (EV k r i D E) (skip1 p) (skip1 q) u ψ).1 g := by
    show (etaV k r z i D E p (yV k r z i D E q (qminor (EV k r i D E) (skip1 p) (skip1 q) u ψ))).1 g = _
    rw [(OperatorRepresentations.rep_etaV hD z p).2 _ g hg]
    show ybv k r z i g p • (yV k r z i D E q (qminor (EV k r i D E) (skip1 p) (skip1 q) u ψ)).1 g = _
    rw [(OperatorRepresentations.rep_yV hD z q).2 _ g hg]
    rfl
  rw [h1, smul_smul, smul_smul]

theorem qhat_ring (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) {f : Mx k r → E}
    (hf : SmoothLev k r (Fin.last r) D f) (Y : ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    qhat k r z z' Y f g =
      ((tV k r z z' (Fin.last r) D E (Y + 1) 0 0 * tV k r z z' (Fin.last r) D E Y 1 1 -
        tV k r z z' (Fin.last r) D E (Y + 1) 1 0 * tV k r z z' (Fin.last r) D E Y 0 1) (mkV hD f hf)).1 g := by
  have key : ∀ p q p' q' : Fin 2,
      tL k r z z' (Fin.last r) (Y + 1) p q (tL k r z z' (Fin.last r) Y p' q' f) g =
        ((tV k r z z' (Fin.last r) D E (Y + 1) p q * tV k r z z' (Fin.last r) D E Y p' q') (mkV hD f hf)).1 g := by
    intro p q p' q'
    obtain ⟨sm, e⟩ := transfer_representation E k r z z' (Fin.last r) D hD f hf Y p' q'
    rw [(transfer_representation E k r z z' (Fin.last r) D hD _ sm (Y + 1) p q).2 g hg]
    have e2 : mkV hD _ sm = tV k r z z' (Fin.last r) D E Y p' q' (mkV hD f hf) := SV_ext fun x hx => by
      rw [← e x hx]; exact cutF_of_mem hx
    rw [e2]; rfl
  unfold qhat
  rw [key, key]; rfl

theorem ring_id (hA : AlgDet) (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) :
    tV k r z z' i D E (Y + 1) 0 0 * tV k r z z' i D E Y 1 1 - tV k r z z' i D E (Y + 1) 1 0 * tV k r z z' i D E Y 0 1 =
      -(chYY (EV k r i D E) (uC k r i Y) (yV k r z i D E) (etaV k r z i D E) *
        chatA (EV k r i D E) (uC k r i Y) (xv k r z' i) (xbv k r z' i)) := by
  obtain ⟨h1, h2, h3, h4⟩ := relation_representation E k r z i D hD
  rw [← hA _ _ _ _ _ h1 h2 h3 h4 (uC k r i Y) (xv k r z' i) (xbv k r z' i)]
  show qdet (EV k r i D E) (uC k r i (Y + 1)) *
      -ch2 (EV k r i D E) (uC k r i Y - 1) (yV k r z i D E) (xv k r z' i) (etaV k r z i D E) (xbv k r z' i) -
      -chY (EV k r i D E) (uC k r i (Y + 1)) (yV k r z i D E) (xbv k r z' i) *
        -chX (EV k r i D E) (uC k r i Y - 1) (xv k r z' i) (etaV k r z i D E) = _
  rw [uC_succ, mul_neg, neg_mul_neg, neg_add, sub_eq_add_neg]

end Main

end FrameEntries

theorem qr_detHat_of (hA : Formalism.FourierDecayAlt.Qr.AlgDet) (hC : Formalism.FourierDecayAlt.Qr.ChatFrame) (hR : Formalism.FourierDecayAlt.Qr.CapRGood)
    (hS : Formalism.FourierDecayAlt.Qr.LeftRightSwap) : Formalism.FourierDecayAlt.Q.DetHat := by
  intro E _ _ k r z z' D f hz hz' hT hT' hD hf Bs Bs' hB hB' g hg Y
  have hne : herm (Hpk k r) z z ≠ 0 := by
    rw [FrameEntries.herm_self, neg_ne_zero, Complex.ofReal_ne_zero]; exact hT.ne'
  have hne' : herm (Hpk k r) z' z' ≠ 0 := by
    rw [FrameEntries.herm_self, neg_ne_zero, Complex.ofReal_ne_zero]; exact hT'.ne'
  have hgi := FrameEntries.glev_inv hg.1
  rw [FrameEntries.qhat_ring hD z z' hf Y hg, FrameEntries.ring_id hA hD z z' Y]
  obtain ⟨u, hu⟩ : ∃ u, u = uC k r (Fin.last r) Y := ⟨_, rfl⟩
  rw [← FrameEntries.uC_last, ← hu]
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = chatA (EV k r (Fin.last r) D E) u (xv k r z' (Fin.last r)) (xbv k r z' (Fin.last r))
    (mkV hD f hf) := ⟨_, rfl⟩
  have e3 : ∀ x ∈ Glev k r (Fin.last r) ∩ D, ψ.1 x = herm (Hpk k r) z' z' • capR k r Bs' u f x := by
    intro x hx
    have e4 : xv k r z' (Fin.last r) = fun j => z' (posL k r (Fin.last r) j) := by
      funext j; simp only [xv, Qx8.fvec_last]
    have e5 : xbv k r z' (Fin.last r) = fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) z' := by
      funext j; simp only [xbv, Qx8.fvec_last]
    rw [hψ, e4, e5, hC E k r D hD z' Bs' hz' hne' hB' u _ x hx]
    congr 1
    exact (hR E k r k (Fin.last r) D hD Bs' hB'.1 u).loc _ _ (fun y hy => cutF_of_mem hy) x hx
  have e1 : yv k r z (Fin.last r) g = fun j => (g⁻¹ *ᵥ z) (posL k r (Fin.last r) j) := by
    funext j; simp only [yv, Qx8.fvec_last]
  have e2 : ybv k r z (Fin.last r) g = fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) (g⁻¹ *ᵥ z) := by
    funext j; simp only [ybv, Qx8.fvec_last]; exact FrameEntries.herm_inv hg.1.1 _ _
  have hne2 : herm (Hpk k r) (g⁻¹ *ᵥ z) (g⁻¹ *ᵥ z) ≠ 0 := by rw [Qx2.herm_uh hgi.1]; exact hne
  show -((chYY (EV k r (Fin.last r) D E) u (yV k r z (Fin.last r) D E) (etaV k r z (Fin.last r) D E)
    (chatA (EV k r (Fin.last r) D E) u (xv k r z' (Fin.last r)) (xbv k r z' (Fin.last r)) (mkV hD f hf))).1 g) = _
  rw [← hψ, FrameEntries.chYY_eval hD z u ψ hg, e1, e2,
    hC E k r D hD (g⁻¹ *ᵥ z) _ (Qx8.inWb_mulVec hgi hz) hne2 (FrameEntries.frame_inv hg.1 hB) u ψ g hg,
    Qx2.herm_uh hgi.1, hS E k r k (Fin.last r) D hD Bs hB.1 u ψ.1 ψ.2.1 g hg,
    Qx8.loc_capLft hD Bs hB.1 u _ _ e3 g hg, FrameEntries.capLft_smul, FrameEntries.herm_self, FrameEntries.herm_self, smul_smul, ← neg_smul]
  congr 1
  push_cast
  ring

namespace FrameEntries

section Reg

variable {k r : ℕ}

def entL (k r : ℕ) (p q : Fin (2 * r + k + 1)) : Mx k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M p q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem poly_contDiff
    (p : MvPolynomial ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ) :
    ContDiff ℝ ∞ fun g : Mx k r => MvPolynomial.eval
      (Sum.elim (fun x => g x.1 x.2) (fun x => (Hpk k r * gᴴ * Hpk k r) x.1 x.2)) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Mx k r => a)
  | add p q hp hq =>
    simpa only [map_add] using hp.add hq
  | mul_X p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    cases n with
    | inl x =>
      simp only [Sum.elim_inl]
      exact (entL k r x.1 x.2).contDiff
    | inr x =>
      simp only [Sum.elim_inr, Matrix.mul_apply, Matrix.conjTranspose_apply]
      refine ContDiff.sum fun c _ => ContDiff.mul ?_ contDiff_const
      refine ContDiff.sum fun d _ => ContDiff.mul contDiff_const ?_
      exact Complex.conjCLE.contDiff.comp (entL k r c d).contDiff

theorem regular_smooth {f : Mx k r → ℂ} (hf : IsRegular k r f) (i : Fin (r + 1)) (D : Set (Mx k r)) :
    SmoothLev k r i D f := by
  obtain ⟨p, hp⟩ := hf
  intro g₀ _
  refine ⟨Set.univ, _, isOpen_univ, Set.mem_univ _, (poly_contDiff p).contDiffOn, fun g _ hg => ?_⟩
  have hU : gᴴ * Hpk k r * g = Hpk k r := by
    simp only [Glev, UH, Set.mem_setOf_eq] at hg
    exact hg.1
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Hpk_mul_self_eq_one]
  rw [hp g]
  simp only [Matrix.inv_eq_left_inv hl]

end Reg

end FrameEntries

theorem qr_detHatRegular_of (h : Formalism.FourierDecayAlt.Q.DetHat) : Formalism.FourierDecayAlt.Q.DetHatRegular := by
  intro k r z z' f hz hz' hT hT' hf
  exact h ℂ k r z z' Set.univ f hz hz' hT hT' isOpen_univ (FrameEntries.regular_smooth hf (Fin.last r) Set.univ)

theorem qr_detGeneric_of (h : Formalism.FourierDecayAlt.Q.DetHatRegular) : Formalism.FourierDecayAlt.Q.DetGeneric := by
  intro k r z z' f u u' hz hz' hT hT' hf _ Bs Bs' hB hB' hE g hg Y
  rw [h k r z z' f hz hz' hT hT' hf Bs Bs' hB hB' g ⟨hg, Set.mem_univ _⟩ Y,
    Qx8.loc_capLft isOpen_univ Bs hB.1 _ _ _ (fun x hx => (hE x hx.1 Y).2) g ⟨hg, Set.mem_univ _⟩,
    FrameEntries.capLft_smul]
  beta_reduce
  rw [(hE g hg Y).1, Finset.prod_mul_distrib]
  simp only [smul_eq_mul]
  ring

end Formalism.FourierDecayAlt.P
