import Formalism.HermitianCurvature.CompositeFormulaLevelZero

open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

lemma mul_mem (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x)
    (Φ : RadSp k r z z' π π') :
    (fun c g => m (c, g) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) ∈ RadSp k r z z' π π' := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, he⟩ := hΦm
  refine (show _ ∧ _ ∧ _ from ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩)
  · show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0
    rw [h0 x hx, smul_zero]
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
    refine ⟨U, fun x => m x • F x, hU, hxU, hm.contDiffOn.smul hF, fun x hx hg => ?_⟩
    show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = m x • F x
    rw [hΦ x hx hg]
  · show m (x.1, h * x.2 * h') • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
      (π h).comp ((m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
    rw [hinv x hx h hh h' hh', he x hx h hh h' hh']
    ext v
    simp

def mulOp (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x) :
    Module.End ℂ (RadSp k r z z' π π') where
  toFun Φ := ⟨_, mul_mem m hm hinv Φ⟩
  map_add' Φ Ψ := by
    ext c g v
    simp [smul_add]
  map_smul' a Φ := by
    ext c g v
    simp [smul_smul, mul_comm]

lemma mulOp_isMulOp (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x) :
    multiplicationOperator (mulOp (π := π) (π' := π') m hm hinv) (fun c g => m (c, g)) := by
  intro _ _ _
  rfl

lemma contDiff_fsv (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hL : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul Complex.conjCLE.contDiff)
  exact Complex.contDiff_exp.comp hL

lemma contDiff_fsv_coord (l : Fin r) (s : ℂ) :
    ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => fsv s (x.1 l)) :=
  (contDiff_fsv s).comp (by fun_prop : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l))

def hermLin (H : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℂ] ℂ where
  toFun g := herm H (g *ᵥ v) w
  map_add' g g' := by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  map_smul' a g := by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]

lemma contDiff_zeta : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => zeta k r z z' x.2) := by
  unfold zeta zetaL
  let Lc : Mx k r →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (hermLin (Hpk k r) (fvec k r z' (Fin.last r)) (fvec k r z (Fin.last r)))
  have h1 : ContDiff ℝ ∞ (fun g : Mx k r => Lc g) := (Lc.restrictScalars ℝ).contDiff
  exact h1.comp contDiff_snd

lemma herm_mulVec_mulVec (H h : Mx k r) (hh : hᴴ * H * h = H) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm H (h *ᵥ v) (h *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh]

lemma zeta_inv (g : Mx k r) (h h' : Mx k r) (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    zeta k r z z' (h * g * h') = zeta k r z z' g := by
  simp only [UWset, Set.mem_setOf_eq] at hh hh'
  obtain ⟨hU, hb, hz⟩ := hh
  obtain ⟨hU', hb', hz'⟩ := hh'
  simp only [UH, Set.mem_setOf_eq] at hU
  have hf' : h' *ᵥ fvec k r z' (Fin.last r) = fvec k r z' (Fin.last r) := by
    unfold fvec
    rw [dif_neg (by simp)]
    exact hz'
  have hf : h *ᵥ fvec k r z (Fin.last r) = fvec k r z (Fin.last r) := by
    unfold fvec
    rw [dif_neg (by simp)]
    exact hz
  unfold zeta zetaL
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf']
  conv_lhs => rw [← hf]
  exact herm_mulVec_mulVec _ _ hU _ _

end Wave

theorem waveCExists : WaveCExists := by
  intro Wp Wq _ _ _ _ k r z z' π π' l s
  exact ⟨mulOp (π := π) (π' := π') (fun x => fsv s (x.1 l)) (contDiff_fsv_coord l s)
    (fun _ _ _ _ _ _ => rfl), mulOp_isMulOp _ _ _⟩

theorem waveZExists : WaveZExists := by
  intro Wp Wq _ _ _ _ k r z z' π π' s
  exact ⟨mulOp (π := π) (π' := π') (fun x => fsv s (zeta k r z z' x.2))
    ((contDiff_fsv s).comp (contDiff_zeta (k := k) (r := r) (z := z) (z' := z')))
    (fun x _ h hh h' hh' => by
      show fsv s (zeta k r z z' (h * x.2 * h')) = fsv s (zeta k r z z' x.2)
      rw [zeta_inv _ _ _ hh hh']), mulOp_isMulOp _ _ _⟩

section Zero

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

end Zero

end Formalism.FourierDecayAlt.P5
