import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotIsFieldAdicCompletionTensorOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplit

open NumberField IsDedekindDomain

namespace PositivityTheory.Lord

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def badSet : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | ¬ ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal}

theorem badSet_finite : (badSet F E).Finite := by
  classical
  let _ : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 E)) := FractionRing.liftAlgebra _ _
  have hD : differentIdeal (𝓞 F) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hW := Ideal.finite_factors (R := 𝓞 E) hD
  refine (hW.image (HeightOneSpectrum.under (𝓞 F))).subset ?_
  intro v hv
  simp only [badSet, Set.mem_ofPred_eq, not_forall] at hv
  obtain ⟨w, hwv, hw⟩ := hv
  refine ⟨w, ?_, ?_⟩
  · have := w.isPrime
    exact (dvd_differentIdeal_iff (P := w.asIdeal)).2 hw
  · ext1
    simp [hwv.over]

theorem fib_finite (v : HeightOneSpectrum (𝓞 F)) :
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.LiesOver v.asIdeal}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).preimage
    (Set.injOn_of_injective (fun a b h => HeightOneSpectrum.ext h))).subset ?_
  intro P hP
  exact ⟨P.isPrime, hP⟩

noncomputable def fib (v : HeightOneSpectrum (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 E)) :=
  (fib_finite F E v).toFinset

theorem mem_fib {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} :
    P ∈ fib F E v ↔ P.asIdeal.LiesOver v.asIdeal := by
  simp [fib]

theorem natCast_pow_cpow (q f : ℕ) (s : ℂ) : ((q ^ f : ℕ) : ℂ) ^ s = ((q : ℂ) ^ s) ^ f := by
  induction f with
  | zero => simp
  | succ n ih =>
    have h := Complex.mul_cpow_ofReal_nonneg (a := ((q ^ n : ℕ) : ℝ)) (b := (q : ℝ)) (by positivity) (by positivity) s
    have e1 : ((q ^ (n + 1) : ℕ) : ℂ) = (((q ^ n : ℕ) : ℝ) : ℂ) * ((q : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, h, pow_succ, ← ih]
    simp only [Complex.ofReal_natCast]

private theorem inertiaDeg_eq_ramIdx_mul_of_ramIdx_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (p : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (he : p.ramificationIdx' P.asIdeal = 1) :
    p.inertiaDeg' P.asIdeal = p.ramificationIdx' P.asIdeal * p.inertiaDeg' P.asIdeal := by
  rw [he, one_mul]

theorem local_factor (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ badSet F E) (s : ℂ) :
    ∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) =
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
        (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  classical
  set p := v.asIdeal with hpdef
  have hp0 : p ≠ ⊥ := v.ne_bot
  haveI hpm : p.IsMaximal := v.isMaximal
  have hmap0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp0
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver p →
      Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := by
    simpa [badSet] using hv
  have hlies : ∀ P ∈ fib F E v, P.asIdeal.LiesOver p := fun P hP => (mem_fib F E).mp hP
  have hmapfib : (fib F E v).map ⟨HeightOneSpectrum.asIdeal, fun a b h => HeightOneSpectrum.ext h⟩ =
      IsDedekindDomain.primesOverFinset p (𝓞 E) := by
    ext Q
    rw [Finset.mem_map, IsDedekindDomain.mem_primesOverFinset_iff hp0]
    constructor
    · rintro ⟨P, hP, rfl⟩
      exact ⟨P.isPrime, (mem_fib F E).mp hP⟩
    · intro hQ
      have hQ0 : Q ≠ ⊥ := by
        intro h
        apply hp0
        rw [hQ.2.over, h]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
      exact ⟨⟨Q, hQ.1, hQ0⟩, (mem_fib F E).mpr hQ.2, rfl⟩
  have hcard_eq : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = (fib F E v).card := by
    rw [← hmapfib, Finset.card_map]
  have he : ∀ P ∈ fib F E v, p.ramificationIdx' P.asIdeal = 1 := by
    intro P hP
    haveI := hlies P hP
    haveI := hunr P (hlies P hP)
    rw [Ideal.ramificationIdx'_eq_ramificationIdx' p P.asIdeal hmap0]
    exact Ideal.ramificationIdx_eq_one _ _
  have hsum : ∑ P ∈ fib F E v, p.inertiaDeg' P.asIdeal = 2 := by
    have h := Ideal.sum_ramification_inertia (𝓞 E) F E hp0
    rw [← hmapfib, Finset.sum_map] at h
    rw [← h2, ← h]
    refine Finset.sum_congr rfl fun P hP => ?_
    exact inertiaDeg_eq_ramIdx_mul_of_ramIdx_eq_one p P (he P hP)
  have hnorm : ∀ P ∈ fib F E v,
      Ideal.absNorm P.asIdeal = Ideal.absNorm p ^ p.inertiaDeg' P.asIdeal := by
    intro P hP
    haveI := hlies P hP
    exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal p hpm.isPrime hp0
  have hfpos : ∀ P ∈ fib F E v, 0 < p.inertiaDeg' P.asIdeal := by
    intro P hP
    haveI := hlies P hP
    exact Ideal.inertiaDeg'_pos p P.asIdeal
  have hcard_le : (fib F E v).card ≤ 2 := by
    rw [← hsum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun P hP => hfpos P hP
  have hcard_pos : 0 < (fib F E v).card := by
    rw [Finset.card_pos]
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hsum
    simp at hsum
  rcases (show (fib F E v).card = 1 ∨ (fib F E v).card = 2 by omega) with hc | hc
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hamem : a ∈ fib F E v := by
      rw [ha]
      exact Finset.mem_singleton_self a
    have haf : p.inertiaDeg' a.asIdeal = 2 := by
      rw [ha, Finset.sum_singleton] at hsum
      exact hsum
    have hmapa : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p = a.asIdeal := by
      haveI := hlies a hamem
      have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ a.asIdeal :=
        Ideal.map_le_of_le_comap (le_of_eq (Ideal.LiesOver.over))
      obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
      have hn := congrArg Ideal.absNorm hJ
      rw [Ideal.absNorm_algebraMap, map_mul, hnorm a hamem, haf,
        ← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2] at hn
      have hNp : 0 < Ideal.absNorm p :=
        Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
      have hJ1 : Ideal.absNorm J = 1 := by
        have h' : Ideal.absNorm p ^ 2 * 1 = Ideal.absNorm p ^ 2 * Ideal.absNorm J := by
          rw [mul_one]
          exact hn
        exact (Nat.eq_of_mul_eq_mul_left (by positivity) h').symm
      rw [Ideal.absNorm_eq_one_iff.mp hJ1, Ideal.mul_top] at hJ
      exact hJ
    have hfield : IsField (TensorProduct F (HeightOneSpectrum.adicCompletion F v) E) :=
      GlobalTheory.InertField.isField_of_inert F E h2 v (by rw [hmapa]; exact a.isPrime)
    have heSp : PositivityTheory.SiegelWeilFormula.Gen.eSp E v = -1 := by
      unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
      exact if_pos hfield
    rw [ha, Finset.prod_singleton, hnorm a hamem, haf, heSp, natCast_pow_cpow]
    ring
  · obtain ⟨a, b, hab, hfab⟩ := Finset.card_eq_two.mp hc
    have hamem : a ∈ fib F E v := by
      rw [hfab]
      simp
    have hbmem : b ∈ fib F E v := by
      rw [hfab]
      simp
    have hpa := hfpos a hamem
    have hpb := hfpos b hbmem
    rw [hfab, Finset.sum_pair hab] at hsum
    have ha1 : p.inertiaDeg' a.asIdeal = 1 := by omega
    have hb1 : p.inertiaDeg' b.asIdeal = 1 := by omega
    have hsplit : (p.primesOver (𝓞 E)).ncard = 2 := by
      rw [← IsDedekindDomain.coe_primesOverFinset hp0, Set.ncard_coe_finset, hcard_eq, hc]
    have hnf := GlobalTheory.SplitPlace.not_isField_of_split F E h2 v hsplit
    have heSp : PositivityTheory.SiegelWeilFormula.Gen.eSp E v = 1 := by
      unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
      exact if_neg hnf
    rw [hfab, Finset.prod_pair hab, hnorm a hamem, hnorm b hbmem, ha1, hb1, heSp, pow_one]
    ring

end PositivityTheory.Lord
