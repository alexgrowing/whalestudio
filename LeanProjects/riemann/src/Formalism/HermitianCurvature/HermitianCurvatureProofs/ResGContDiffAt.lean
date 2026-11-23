import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.FormalDegreeBessel.FinalWR

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cell

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

open Classical in

def resW (h : Mx k r → V) (g : Mx k r) : (Fin r → ℂ) → V :=
  fun c' => if c' ∈ OmX r then resG k r (Fin.last r) h c' g else 0

theorem resG_contDiffAt (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V}
    (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hG : 0 < GGl k r Bs.z Bs.z' g) {c₀ : Fin r → ℂ} (hc₀ : c₀ ∈ OmX r) :
    ContDiffAt ℝ ∞ (fun c' => resG k r (Fin.last r) h c' g) c₀ := by
  have hsf := Formalism.FourierDecayAlt.P5.Rad.sf_resG hh
  obtain ⟨U, F, hU, hxU, hF, hE⟩ := hsf (c₀, g)
    ⟨hc₀, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc₀ hg hG⟩ hg
  have hpre : IsOpen ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) := hU.preimage (by fun_prop)
  have hmem : c₀ ∈ (fun c : Fin r → ℂ => (c, g)) ⁻¹' U := hxU
  have hcd : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) c₀ := by
    have h1 : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) :=
      hF.comp (by fun_prop : ContDiff ℝ ∞ (fun c : Fin r → ℂ => (c, g))).contDiffOn (fun c hc => hc)
    exact h1.contDiffAt (hpre.mem_nhds hmem)
  refine hcd.congr_of_eventuallyEq ?_
  filter_upwards [hpre.mem_nhds hmem] with c hc
  exact hE (c, g) hc hg

theorem resG_wsm (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) :
    resW h g ∈ WSm r V := by
  refine ⟨?_, fun x hx => by simp [resW, hx]⟩
  intro c hc
  have h1 := (resG_contDiffAt Bs hh hg hG hc).contDiffWithinAt (s := OmX r)
  refine h1.congr (fun c' hc' => by simp [resW, hc']) (by simp [resW, hc])

theorem wsm_resG_eq (h : Mx k r → V) (g : Mx k r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    resW h g c = resG k r (Fin.last r) h c g := by
  simp [resW, hc]

theorem cell_diff (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : DifferentiableAt ℝ (fun c' => h (wCell k r (Fin.last r) c' * g)) c := by
  have hgl : ∀ c' ∈ OmX r, wCell k r (Fin.last r) c' * g ∈ Glev k r 0 := fun c' hc' =>
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc' _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg)
  obtain ⟨U, F, hU, hgU, hF, hE⟩ := hh (wCell k r (Fin.last r) c * g)
    ⟨hgl c hc, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hg hG⟩
  have hw : ContDiffOn ℝ ∞ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) (OmX r) :=
    Formalism.FourierDecayAlt.P.Qx3.cdo_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _) contDiffOn_const
  have hwc : ContinuousAt (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
    (hw.continuousOn).continuousAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
  have hd : DifferentiableAt ℝ (fun c' => F (wCell k r (Fin.last r) c' * g)) c := by
    have hFd : DifferentiableAt ℝ F (wCell k r (Fin.last r) c * g) :=
      (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
    have hwd : DifferentiableAt ℝ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
      (hw.differentiableOn (by simp)).differentiableAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
    exact hFd.comp c hwd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc, hwc.preimage_mem_nhds (hU.mem_nhds hgU)]
    with c' h1 h2
  exact hE _ h2 (hgl c' h1)

end cell

section chain

variable {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem wsm_sub {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) : f - g ∈ WSm r V :=
  (WSm r V).sub_mem hf hg

theorem opL_mem (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) : opL l i f ∈ WSm r V :=
  preserved_operators_holds r V l i f hf

theorem opL_sub (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f - g) = opL l i f - opL l i g := by
  have hng : (-1 : ℂ) • g ∈ WSm r V := (WSm r V).smul_mem _ hg
  have e : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, (linear_operators_holds r V l i f _ 1 hf hng).1, (linear_operators_holds r V l i g g (-1) hg hg).2, neg_one_smul,
    sub_eq_add_neg]

theorem opL_add (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f + g) = opL l i f + opL l i g :=
  (linear_operators_holds r V l i f g 1 hf hg).1

theorem opL_smul (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (a : ℂ) :
    opL l i (a • f) = a • opL l i f :=
  (linear_operators_holds r V l i f f a hf hf).2

theorem pOp_zero (l : Fin r) : pOp l (fun _ : Fin r → ℂ => (0 : V)) = fun _ => 0 := by
  funext x; unfold pOp wirt; split_ifs <;> simp

theorem vAB_mem (y : ℂ) : ∀ (i : ℕ) {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V
  | 0, G, hG => ⟨hG, (WSm r V).zero_mem⟩
  | i + 1, G, hG => by
    obtain ⟨hA, hB⟩ := vAB_mem y i hG
    by_cases hi : i < r
    · simp only [vAB, dif_pos hi]
      refine ⟨wsm_sub ((WSm r V).add_mem ((WSm r V).smul_mem y hA) (opL_mem ⟨i, hi⟩ 0 hA))
        (opL_mem ⟨i, hi⟩ 1 hB), opL_mem ⟨i, hi⟩ 2 hA⟩
    · simp only [vAB, dif_neg hi]
      exact ⟨hA, hB⟩

theorem vAB_lin (y : ℂ) : ∀ (i : ℕ) {G₁ G₂ : (Fin r → ℂ) → V}, G₁ ∈ WSm r V → G₂ ∈ WSm r V → ∀ s : ℂ,
    (vAB r y i).1 (G₁ + s • G₂) = (vAB r y i).1 G₁ + s • (vAB r y i).1 G₂ ∧
      (vAB r y i).2 (G₁ + s • G₂) = (vAB r y i).2 G₁ + s • (vAB r y i).2 G₂
  | 0, G₁, G₂, _, _, s => ⟨rfl, by show (0 : (Fin r → ℂ) → V) = 0 + s • 0; simp⟩
  | i + 1, G₁, G₂, h₁, h₂, s => by
    obtain ⟨ih1, ih2⟩ := vAB_lin y i h₁ h₂ s
    obtain ⟨hA₁, hB₁⟩ := vAB_mem y i h₁
    obtain ⟨hA₂, hB₂⟩ := vAB_mem y i h₂
    have hsA := (WSm r V).smul_mem s hA₂
    have hsB := (WSm r V).smul_mem s hB₂
    by_cases hi : i < r
    · simp only [vAB, dif_pos hi]
      rw [ih1, ih2]
      refine ⟨?_, ?_⟩
      · have e1 : pOp ⟨i, hi⟩ ((vAB r y i).1 G₁ + s • (vAB r y i).1 G₂) =
            pOp ⟨i, hi⟩ ((vAB r y i).1 G₁) + s • pOp ⟨i, hi⟩ ((vAB r y i).1 G₂) := by
          rw [show pOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 0 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
        have e2 : cOp ⟨i, hi⟩ ((vAB r y i).2 G₁ + s • (vAB r y i).2 G₂) =
            cOp ⟨i, hi⟩ ((vAB r y i).2 G₁) + s • cOp ⟨i, hi⟩ ((vAB r y i).2 G₂) := by
          rw [show cOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 1 from rfl, opL_add _ _ hB₁ hsB, opL_smul _ _ hB₂]
        rw [e1, e2]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_add, smul_sub]
        rw [smul_comm y s]
        abel
      · rw [show ciOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 2 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
    · simp only [vAB, dif_neg hi]
      exact ⟨ih1, ih2⟩

theorem vAB_comm (y : ℂ) (j : Fin r) : ∀ (i : ℕ), i ≤ j.val → ∀ {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V ∧
      (vAB r y i).1 (pOp j G) = pOp j ((vAB r y i).1 G) ∧ (vAB r y i).2 (pOp j G) = pOp j ((vAB r y i).2 G)
  | 0, _, G, hG => ⟨hG, (WSm r V).zero_mem, rfl, by simp only [vAB]; exact (pOp_zero j).symm⟩
  | i + 1, hij, G, hG => by
    obtain ⟨hA, hB, c1, c2⟩ := vAB_comm y j i (by omega) hG
    have hpG : pOp j G ∈ WSm r V := opL_mem j 0 hG
    have hi : i < r := by have := j.isLt; omega
    have hne : (⟨i, hi⟩ : Fin r) ≠ j := by intro h; rw [← h] at hij; simp at hij
    obtain ⟨hm1, hm2⟩ := vAB_mem y (i + 1) hG
    refine ⟨hm1, hm2, ?_, ?_⟩
    · simp only [vAB, dif_pos hi]
      rw [c1, c2]
      have hpA : pOp ⟨i, hi⟩ ((vAB r y i).1 G) ∈ WSm r V := opL_mem _ 0 hA
      have hcB : cOp ⟨i, hi⟩ ((vAB r y i).2 G) ∈ WSm r V := opL_mem _ 1 hB
      have hyA : y • (vAB r y i).1 G ∈ WSm r V := (WSm r V).smul_mem y hA
      rw [show pOp j = opL j 0 from rfl, opL_sub _ _ ((WSm r V).add_mem hyA hpA) hcB,
        opL_add _ _ hyA hpA, opL_smul _ _ hA]
      have k1 : opL j 0 (pOp ⟨i, hi⟩ ((vAB r y i).1 G)) = pOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).1 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 0 _ hA (Or.inl (Ne.symm hne)))
      have k2 : opL j 0 (cOp ⟨i, hi⟩ ((vAB r y i).2 G)) = cOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).2 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 1 _ hB (Or.inl (Ne.symm hne)))
      rw [k1, k2]
    · simp only [vAB, dif_pos hi]
      rw [c1]
      exact (commuting_functional_holds r V j ⟨i, hi⟩ 0 2 _ hA (Or.inl (Ne.symm hne))).symm

end chain

end Formalism.FourierDecayAlt.P.PBN.MC
