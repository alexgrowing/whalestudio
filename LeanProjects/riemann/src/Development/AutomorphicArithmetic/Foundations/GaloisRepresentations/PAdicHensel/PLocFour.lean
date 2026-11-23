import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pLocFour :
    LocFour := by
  intro F _ _ v tr nm hΔ u hu
  haveI : CharZero (HeightOneSpectrum.adicCompletion F v) :=
    (RingHom.charZero_iff (algebraMap F (HeightOneSpectrum.adicCompletion F v)).injective).mp inferInstance
  have h2 : (2 : HeightOneSpectrum.adicCompletion F v) ≠ 0 := two_ne_zero
  have hD : ((tr : HeightOneSpectrum.adicCompletion F v) ^ 2 - 4 * nm) ≠ 0 := by
    have h := (Int.cast_ne_zero (α := HeightOneSpectrum.adicCompletion F v)).mpr hΔ
    push_cast at h
    exact h
  set D : HeightOneSpectrum.adicCompletion F v := (tr : HeightOneSpectrum.adicCompletion F v) ^ 2 - 4 * nm
    with hDdef
  let c : Fin 5 → HeightOneSpectrum.adicCompletion F v := ![1, -(D / 4), 1, -(D / 4), -u]
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i <;> simp [c, hD, hu]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.LocalQuad.isotropic_adicCompletion_of_five_le F v (ι := Fin 5) (by simp) c
  obtain ⟨z, hz4, hz⟩ := GlobalTheory.HermLocal.exists_zero_coord h2 hc hx0 hx 4
  have hz' : z 0 ^ 2 + -(D / 4) * z 1 ^ 2 + z 2 ^ 2 + -(D / 4) * z 3 ^ 2 + -u * z 4 ^ 2 = 0 := by
    rw [Fin.sum_univ_five] at hz
    simpa [c] using hz
  obtain ⟨w, hw⟩ : ∃ w, z 4 * w = 1 := ⟨(z 4)⁻¹, mul_inv_cancel₀ hz4⟩
  refine ⟨z 0 * w - tr / 2 * (z 1 * w), z 1 * w, z 2 * w - tr / 2 * (z 3 * w), z 3 * w, ?_⟩
  unfold qf
  rw [hDdef] at hz'
  linear_combination w ^ 2 * hz' + u * (z 4 * w + 1) * hw
