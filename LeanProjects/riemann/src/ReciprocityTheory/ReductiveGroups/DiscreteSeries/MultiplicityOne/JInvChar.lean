import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCharB

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stInvChar : StInvChar := by
  intro k r Wp _ _ _ D X _ _ γ hγ m hm
  have hE : IsUnit (embWb k r γ).det := InvChr.unit_embWb (InvChr.unit_of_frame hγ.1)
  have hcc : InvChr.cc γ D.z = D.z := InvChr.frame_conjugation_fixes_vector hE D.z D.T_pos hγ.2
  have hbar : ∀ n : Mat k r, ell k r D.z (gbar k r γ n) = starRingEnd ℂ (ell k r D.z n) :=
    fun n => InvChr.ell_gbar hE D.z hcc n
  have hdet : IsUnit m.det := by
    have hU : m.conjTranspose * Hpk k r * m = Hpk k r := hm.1
    refine Matrix.isUnit_det_of_left_inverse (B := Hpk k r * m.conjTranspose * Hpk k r) ?_
    calc Hpk k r * m.conjTranspose * Hpk k r * m = Hpk k r * (m.conjTranspose * Hpk k r * m) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, InvChr.Hpk_sq k r]
  have hinv : ell k r D.z m⁻¹ = -ell k r D.z m :=
    InvChr.ell_inv_N D.z D.z_mem m m⁻¹ hm (Matrix.nonsing_inv_mul m hdet)
  have hth : th k r γ m = gbar k r γ m⁻¹ := (InvChr.gbar_inv hE m hdet).symm
  refine ⟨?_, ?_⟩
  · simp only [lam, hbar, InvChr.cStd_conj_re]
  · simp only [psiD, psi, hth, hbar, hinv, map_neg, mul_neg, Complex.neg_re,
      InvChr.cStd_conj_re, neg_neg]

end ReciprocityTheory.ChartRestriction.DS.Mult1
