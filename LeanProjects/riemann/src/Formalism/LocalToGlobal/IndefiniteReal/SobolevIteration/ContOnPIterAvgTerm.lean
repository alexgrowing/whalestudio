import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.PdsEqIteratedFDeriv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexOrder

namespace Formalism.IndefR.Tow.SobPf.Avg

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def hcFun (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : (Fin n → Fin n → ℂ) → ℂ) (w : H)
    (u : Matrix (Fin n) (Fin n) ℂ) {d d' : ℕ} (Z : Fin (d + d') → Matrix (Fin n) (Fin n) ℂ) (j : ℕ)
    (q : (Fin (d + d') → ℝ) × (Fin n → Fin n → ℂ)) : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) H :=
  (p q.2 • (π u).restrictScalars ℝ).compContinuousMultilinearMap
    ((iteratedFDeriv ℝ j (fun r => π (oneProd Z r) w) q.1).compContinuousLinearMap (fun _ => appL d d'))

set_option maxHeartbeats 1000000 in
theorem continuous_hcFun {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : (Fin n → Fin n → ℂ) → ℂ} {w : H}
    (u : Matrix (Fin n) (Fin n) ℂ) {d d' : ℕ} {Z : Fin (d + d') → Matrix (Fin n) (Fin n) ℂ}
    (hp : Continuous p) (hGZ : ContDiff ℝ ∞ fun r => π (oneProd Z r) w) (j : ℕ) :
    Continuous (hcFun π p w u Z j) := by
  have hM : Continuous fun q : (Fin (d + d') → ℝ) × (Fin n → Fin n → ℂ) =>
      (iteratedFDeriv ℝ j (fun r => π (oneProd Z r) w) q.1).compContinuousLinearMap
        (fun _ : Fin j => appL d d') :=
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => appL d d')).continuous.comp
      ((hGZ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp continuous_fst)
  have hL : Continuous fun q : (Fin (d + d') → ℝ) × (Fin n → Fin n → ℂ) =>
      p q.2 • (π u).restrictScalars ℝ :=
    (hp.comp continuous_snd).smul continuous_const
  have h := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => Fin d → ℝ) H H).continuous.comp
    hL).clm_apply hM
  unfold hcFun
  simpa using h

set_option maxHeartbeats 1000000 in

theorem contOn_pIter_avgTerm (h4 : SobChart) {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s)
    {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hπ : IsGRep G π) {w : H} (hw : SmoothVec (lieG G) π w)
    {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) {d : ℕ} {Xs : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (hXs : ∀ i, Xs i ∈ lieG G) (j : ℕ) :
    ContinuousOn (fun q : (Fin d → ℝ) × (Fin n → Fin n → ℂ) => pIter (avgTerm π p w Xs) j q.1 q.2)
      (Set.univ ×ˢ Kset G s) := by
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    have h1 := hs.2.2.det_pos.ne'
    rw [Matrix.det_mul] at h1
    exact left_ne_zero_of_mul h1
  obtain ⟨d', Y, hY, hch⟩ := h4 G s hs
  intro q0 hq0
  obtain ⟨t0, k0⟩ := q0
  have hk0 : Matrix.of k0 ∈ KAt G s := hq0.2
  obtain ⟨u, hu_eq⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ, u = Matrix.of k0 := ⟨_, rfl⟩
  have hu : u ∈ Formalism.QuantumDeterminants.UH G := by rw [hu_eq]; exact hk0.1
  have hdu : IsUnit u.det := by
    have h : uᴴ * G * u = G := hu
    have h' := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul] at h'
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h'
    exact hG.ne_zero h'.symm
  have hA : ∀ i, Fin.append (fun i => u⁻¹ * Xs i * u) Y i ∈ lieG G :=
    append_mem_lieG (fun i => conj_mem_lieG hG hu (hXs i)) hY
  have hc := continuous_hcFun (π := π) (w := w) u (Z := Fin.append (fun i => u⁻¹ * Xs i * u) Y) hp
    (contDiff_orbit hw hA) j
  have hk0' : Matrix.of k0 = u * oneProd Y 0 := by rw [oneProd_zero, mul_one, hu_eq]
  have hval : ∀ (t : Fin d → ℝ) (k : Fin n → Fin n → ℂ) (s' : Fin d' → ℝ), Matrix.of k = u * oneProd Y s' →
      pIter (avgTerm π p w Xs) j t k =
        hcFun π p w u (Fin.append (fun i => u⁻¹ * Xs i * u) Y) j (Fin.append t s', k) :=
    fun t k s' hk => pIter_avgTerm hG hπ hw hXs hY hu s' hk j t
  refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
  obtain ⟨η, hη, hHc⟩ := Metric.continuous_iff.1 hc (Fin.append t0 0, k0) ε hε
  obtain ⟨δ, hδ, hchδ⟩ := hch η hη
  have hV : IsOpen {k : Fin n → Fin n → ℂ |
      ∀ i j, ‖(u⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ} := by
    have hcont : ∀ i j, Continuous fun k : Fin n → Fin n → ℂ =>
        ‖(u⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ := fun i j =>
      (((continuous_const.matrix_mul
        (continuous_id' : Continuous fun k : Fin n → Fin n → ℂ => Matrix.of k)).matrix_elem i j).sub
          continuous_const).norm
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt (hcont i j) continuous_const
  have hk0V : ∀ i j, ‖(u⁻¹ * Matrix.of k0) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ := by
    intro i j
    rw [← hu_eq, Matrix.nonsing_inv_mul _ hdu, sub_self, norm_zero]
    exact hδ
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hV k0 hk0V
  refine ⟨min η ρ, lt_min hη hρ, fun {x} hx hdx => ?_⟩
  obtain ⟨t, k⟩ := x
  rw [Prod.dist_eq] at hdx
  have hd1 : dist t t0 < η := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hdx (min_le_left _ _))
  have hd2 : dist k k0 < ρ := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hdx (min_le_right _ _))
  have hd3 : dist k k0 < η := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hdx (min_le_left _ _))
  have hkV := hρV (Metric.mem_ball.2 hd2)
  have hkK : Matrix.of k ∈ KAt G s := hx.2
  have hg : u⁻¹ * Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := mul_mem_UH₂ G _ (inv_mem_UH hG hu) _ hkK.1
  obtain ⟨s', hs', hgs⟩ := hchδ _ hg hkV
  have hks : Matrix.of k = u * oneProd Y s' := by
    rw [← hgs, Matrix.mul_nonsing_inv_cancel_left _ _ hdu]
  dsimp only
  rw [hval t k s' hks, hval t0 k0 0 hk0']
  apply hHc
  rw [Prod.dist_eq]
  refine max_lt ?_ hd3
  rw [dist_pi_lt_iff hη]
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left]
    exact lt_of_le_of_lt (dist_le_pi_dist t t0 i) hd1
  · simp only [Fin.append_right, Pi.zero_apply]
    rw [Real.dist_eq, sub_zero]
    exact hs' i

end Formalism.IndefR.Tow.SobPf.Avg

end
