import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ScaledFormDenEqOneOnLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntAfIntCast
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.scaled_form_congr_mod_n_of_unit_congr :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (n : ℕ) (ν : ℤ) (b : AfP p) (u u' : VQ D) (a a' : D.La) (e e' : AfP p ⊗[ℚ] VQ D), 0 < n → n.Coprime p → IsIntAf b → (X.ε : AfP p) = (ν : AfP p) + (n : AfP p) * b → u ∈ X.lat → u' ∈ X.lat → e ∈ LaHat D → e' ∈ LaHat D → X.r u = inAf D a + n • e → X.r u' = inAf D a' + n • e' → ∃ z : ℤ, X.s * X.B u u' = (ν : ℚ) * (D.EF a a' : ℤ) + (n : ℚ) * z := by
  intro p _ D X n ν b u u' a a' e e' hn hc hb hε hu hu' he he' hr hr'
  have hden := UpperTheory.scaled_form_den_eq_one_on_lattice p D X u u' hu hu'
  have hform : algebraMap ℚ (AfP p) (X.s * X.B u u') =
      (X.ε : AfP p) * MultScale.EFA D (X.r u) (X.r u') := X.form u u'
  generalize X.s * X.B u u' = q at hden hform ⊢
  have hqz : ((q.num : ℤ) : ℚ) = q := Rat.coe_int_num_of_den_eq_one hden
  have ha := MultScale.inAf_mem D a
  have ha' := MultScale.inAf_mem D a'
  obtain ⟨y, hy, hexp⟩ : ∃ y : AfP p, IsIntAf y ∧
      MultScale.EFA D (inAf D a + n • e) (inAf D a' + n • e') =
        ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * y := by
    refine ⟨MultScale.EFA D (inAf D a) e' + MultScale.EFA D e (inAf D a') +
      (n : AfP p) * MultScale.EFA D e e', ?_, ?_⟩
    · exact MultScale.isIntAf_add (MultScale.isIntAf_add (MultScale.isIntAf_EFA D ha he')
        (MultScale.isIntAf_EFA D he ha')) (MultScale.isIntAf_mul
          (by simpa using MultScale.isIntAf_intCast (p := p) (n : ℤ)) (MultScale.isIntAf_EFA D he he'))
    · simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
        MultScale.EFA_inAf]
      ring
  rw [hr, hr', hexp, hε] at hform
  have hE := MultScale.isIntAf_intCast (p := p) (D.EF a a')
  have hN : IsIntAf (n : AfP p) := by simpa using MultScale.isIntAf_intCast (p := p) (n : ℤ)
  have hy' : IsIntAf ((ν : AfP p) * y + b * (((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * y)) :=
    MultScale.isIntAf_add (MultScale.isIntAf_mul (MultScale.isIntAf_intCast ν) hy)
      (MultScale.isIntAf_mul hb (MultScale.isIntAf_add hE (MultScale.isIntAf_mul hN hy)))
  have hc' : algebraMap ℚ (AfP p) (((q.num - ν * (D.EF a a' : ℤ) : ℤ)) : ℚ) =
      (n : AfP p) * ((ν : AfP p) * y + b * (((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * y)) := by
    have h1 : algebraMap ℚ (AfP p) ((q.num : ℤ) : ℚ) = algebraMap ℚ (AfP p) q := by rw [hqz]
    rw [map_intCast] at h1 ⊢
    push_cast
    rw [h1, hform]
    ring
  obtain ⟨k, hk⟩ := IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _ _ hy' hc'
  refine ⟨k, ?_⟩
  have hk' : ((q.num : ℤ) : ℚ) - (ν : ℚ) * (D.EF a a' : ℤ) = (n : ℚ) * k := by exact_mod_cast hk
  rw [← hqz]
  linarith
