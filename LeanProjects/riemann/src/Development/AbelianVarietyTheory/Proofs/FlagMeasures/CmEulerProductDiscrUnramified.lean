import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotIsFieldAdicCompletionTensorOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplex
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.DensityEuler

open private euler_factor_log_bound partial_sums_log_euler_factor_le from Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def conjInt (hc : Formalism.BasicNotions.CMData F E) : 𝓞 E →ₐ[𝓞 F] 𝓞 E := RingOfIntegers.mapAlgHom hc.sig

theorem conjInt_coe (hc : Formalism.BasicNotions.CMData F E) (x : 𝓞 E) :
    algebraMap (𝓞 E) E (conjInt hc x) = star (algebraMap (𝓞 E) E x) := rfl

theorem conjInt_conjInt (hc : Formalism.BasicNotions.CMData F E) (x : 𝓞 E) : conjInt hc (conjInt hc x) = x := by
  apply IsFractionRing.injective (𝓞 E) E
  rw [conjInt_coe, conjInt_coe, star_star]

theorem conjIdeal_eq_comap (hc : Formalism.BasicNotions.CMData F E) (P : Ideal (𝓞 E)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := E) P = P.comap (conjInt hc) := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, h⟩
    have : r = conjInt hc s := IsFractionRing.injective (𝓞 E) E (h.trans (conjInt_coe hc s).symm)
    rw [SetLike.mem_coe, Ideal.mem_comap, this, conjInt_conjInt]
    exact hs
  · intro r hr
    refine Ideal.subset_span ⟨conjInt hc r, hr, ?_⟩
    rw [conjInt_coe, star_star]

theorem comap_mem_primesOver (hc : Formalism.BasicNotions.CMData F E) (v : Ideal (𝓞 F)) {P : Ideal (𝓞 E)}
    (hP : P ∈ v.primesOver (𝓞 E)) : P.comap (conjInt hc) ∈ v.primesOver (𝓞 E) := by
  have := hP.1
  refine ⟨Ideal.comap_isPrime _ _, ⟨?_⟩⟩
  rw [hP.2.over]
  ext x
  simp only [Ideal.under, Ideal.mem_comap, AlgHom.commutes]

omit [NumberField F] [StarRing E] in
theorem isMaximal_of_mem (v : HeightOneSpectrum (𝓞 F)) {P : Ideal (𝓞 E)}
    (hP : P ∈ v.asIdeal.primesOver (𝓞 E)) : P.IsMaximal := by
  have := hP.1
  have := hP.2
  exact hP.1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P)

theorem comap_ne_of_inertiaDeg_eq_one (hc : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F))
    {P : Ideal (𝓞 E)} (hP : P ∈ v.asIdeal.primesOver (𝓞 E)) (hf : P.inertiaDeg (𝓞 F) = 1) :
    P.comap (conjInt hc) ≠ P := by
  intro h
  have hm := isMaximal_of_mem v hP
  have := hP.2
  have := v.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal P] at hf
  let : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  let : Field (𝓞 E ⧸ P) := Ideal.Quotient.field _
  have hs := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hf).2
  obtain ⟨θ, t, ht, hn⟩ := hc.cmUnram.2.2 P hm
  obtain ⟨a, ha⟩ := hs (Ideal.Quotient.mk P θ)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h1 : θ - algebraMap (𝓞 F) (𝓞 E) a ∈ P := by
    rw [← Ideal.Quotient.eq, ← ha]; rfl
  have h2 : t - algebraMap (𝓞 F) (𝓞 E) a ∈ P := by
    have ht' : t = conjInt hc θ :=
      IsFractionRing.injective (𝓞 E) E (ht.trans (conjInt_coe hc θ).symm)
    have h3 := h1
    rw [← h, Ideal.mem_comap, map_sub, AlgHom.commutes, ← ht'] at h3
    exact h3
  apply hn
  simpa using P.sub_mem h1 h2

omit [StarRing E] in
theorem sum_eq_two (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F))
    [Fintype (v.asIdeal.primesOver (𝓞 E))] :
    ∑ P : v.asIdeal.primesOver (𝓞 E), P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) = 2 := by
  have := v.isPrime
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rwa [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2] at hsum

theorem unramifiedPlace (hc : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v := by
  classical
  intro w hw
  have := v.isMaximal
  have : (w.asIdeal.under (𝓞 F)).IsMaximal := by rw [← hw.over]; exact v.isMaximal
  refine Ideal.ramificationIdx_eq_one_iff.1 ?_
  have hsum := sum_eq_two hc.deg2 v
  have hP : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, hw⟩
  have hpos : ∀ P : v.asIdeal.primesOver (𝓞 E),
      1 ≤ P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) := fun P =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos _ _
  have hf : 0 < w.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos _ _
  have h1 : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) ≤ 2 :=
    hsum ▸ Finset.single_le_sum
      (f := fun P : v.asIdeal.primesOver (𝓞 E) =>
        P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨_, hP⟩)
  by_contra hne
  have hf1 : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    have : 2 ≤ w.asIdeal.ramificationIdx (𝓞 F) := by omega
    nlinarith
  have hneq := comap_ne_of_inertiaDeg_eq_one hc v hP hf1
  have h3 := Finset.add_le_sum (s := Finset.univ)
    (f := fun P : v.asIdeal.primesOver (𝓞 E) =>
        P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨_, comap_mem_primesOver hc _ hP⟩) (Finset.mem_univ ⟨_, hP⟩)
    (fun h => hneq (congrArg Subtype.val h))
  have h4 := hpos ⟨_, comap_mem_primesOver hc _ hP⟩
  rw [hsum] at h3
  simp only [hf1] at h3 h4
  omega

theorem hasProd_fibre (hc : Formalism.BasicNotions.CMData F E) (M : ℕ) (hM : 1 ≤ M)
    (v : HeightOneSpectrum (𝓞 F)) :
    HasProd (fun P : v.asIdeal.primesOver (𝓞 E) => Formalism.HermitianLatticesTheory.eulerFac E M P.1)
      (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹)⁻¹ := by
  classical
  have := v.isMaximal
  have hpos := GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.density_factor_pos F E v M hM
  have hsum := sum_eq_two hc.deg2 v
  have hq := GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.one_lt_resCard F v
  suffices h : ∏ P : v.asIdeal.primesOver (𝓞 E), Formalism.HermitianLatticesTheory.eulerFac E M P.1 =
      (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹)⁻¹ from
    h ▸ hasProd_fintype _
  rcases (GlobalTheory.quadratic_unramified_iff_inert_or_split F E hc.deg2 v).1 (unramifiedPlace hc v)
    with h | h
  · have heta : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v = -1 :=
      if_pos (GlobalTheory.InertField.isField_of_inert F E hc.deg2 v h)
    have hm := h.isMaximal (Ideal.map_ne_bot_of_ne_bot v.ne_bot)
    have heq : ∀ Q : v.asIdeal.primesOver (𝓞 E),
        v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = Q.1 := fun Q =>
      hm.eq_of_le Q.2.1.ne_top (Ideal.map_le_iff_le_comap.2 Q.2.2.over.le)
    have : Subsingleton (v.asIdeal.primesOver (𝓞 E)) :=
      ⟨fun a b => Subtype.ext ((heq a).symm.trans (heq b))⟩
    obtain ⟨P⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 E)
    have hfix : Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.1 = P.1 := by
      rw [conjIdeal_eq_comap hc]
      exact congrArg Subtype.val (Subsingleton.elim (⟨_, comap_mem_primesOver hc _ P.2⟩ :
        v.asIdeal.primesOver (𝓞 E)) P)
    have hN : (Ideal.absNorm P.1 : ℝ) = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ 2 := by
      rw [← heq P, Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, hc.deg2,
        Nat.cast_pow]
      rfl
    rw [Fintype.prod_subsingleton _ P, Formalism.HermitianLatticesTheory.eulerFac, if_pos hfix, hN,
      Real.sqrt_sq (by linarith), heta, zpow_neg, zpow_natCast]
  · have heta : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v = 1 :=
      if_neg (GlobalTheory.SplitPlace.not_isField_of_split F E hc.deg2 v h)
    have hcard : Fintype.card (v.asIdeal.primesOver (𝓞 E)) = 2 := by
      rw [← h, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hone : ∀ P : v.asIdeal.primesOver (𝓞 E),
        1 ≤ P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) := fun P =>
      Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
    have h1 : ∑ _P : v.asIdeal.primesOver (𝓞 E), 1 =
        ∑ P : v.asIdeal.primesOver (𝓞 E),
          P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) := by
      rw [hsum]; simpa using hcard
    rw [heta, one_pow, one_mul] at hpos ⊢
    have hfac : ∀ P : v.asIdeal.primesOver (𝓞 E), Formalism.HermitianLatticesTheory.eulerFac E M P.1 =
        (1 - (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹) ^ (-(1 : ℝ) / 2) := by
      intro P
      have hf : P.1.inertiaDeg (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_left
        ((Finset.sum_eq_sum_iff_of_le (fun P _ => hone P)).1 h1 P (Finset.mem_univ _)).symm
      have hne : Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.1 ≠ P.1 := by
        rw [conjIdeal_eq_comap hc]
        exact comap_ne_of_inertiaDeg_eq_one hc v P.2 hf
      have hN : (Ideal.absNorm P.1 : ℝ) = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v := by
        have := P.2.1
        have := P.2.2
        rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal P.1, hf, pow_one]
        rfl
      rw [Formalism.HermitianLatticesTheory.eulerFac, if_neg hne, hN, zpow_neg, zpow_natCast]
    rw [Finset.prod_congr rfl (fun P _ => hfac P), Finset.prod_const, Finset.card_univ, hcard,
      ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
      show (-(1 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]

def fibreEquiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    (Σ v : HeightOneSpectrum (𝓞 F), v.asIdeal.primesOver (𝓞 E)) ≃
      {P : Ideal (𝓞 E) // P.IsMaximal} :=
  Equiv.ofBijective (fun x => ⟨x.2.1, isMaximal_of_mem x.1 x.2.2⟩) <| by
    constructor
    · rintro ⟨v, P, hP⟩ ⟨w, Q, hQ⟩ h
      obtain rfl : P = Q := congrArg Subtype.val h
      obtain rfl : v = w := HeightOneSpectrum.ext (hP.2.over.trans hQ.2.over.symm)
      rfl
    · rintro ⟨P, hP⟩
      have hm : (P.under (𝓞 F)).IsMaximal := Ideal.IsMaximal.under _ P
      exact ⟨⟨⟨P.under (𝓞 F), hm.isPrime,
        Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩,
        P, hP.isPrime, ⟨rfl⟩⟩, rfl⟩

theorem hasProd_eulerFac (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (M : ℕ) (hM : 2 ≤ M) :
    HasProd (fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac E M P.1)
      (Formalism.HermitianLatticesTheory.lValEta E M) ∧ 0 < Formalism.HermitianLatticesTheory.lValEta E M := by
  have hpos : ∀ P : {P : Ideal (𝓞 E) // P.IsMaximal}, 0 < Formalism.HermitianLatticesTheory.eulerFac E M P.1 :=
    fun P => (euler_factor_log_bound E hE M (by omega) P.1 P.2).1
  have hsum : Summable (fun P : {P : Ideal (𝓞 E) // P.IsMaximal} =>
      Real.log (Formalism.HermitianLatticesTheory.eulerFac E M P.1)) :=
    (summable_of_sum_le (fun P => abs_nonneg _) (partial_sums_log_euler_factor_le E hE M hM)).of_abs
  refine ⟨(Real.multipliable_of_summable_log hpos hsum).hasProd, ?_⟩
  rw [Formalism.HermitianLatticesTheory.lValEta, ← Real.rexp_tsum_eq_tprod hpos hsum]
  exact Real.exp_pos _

theorem hasProd_inv (hc : Formalism.BasicNotions.CMData F E) (M : ℕ) (hM : 2 ≤ M) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
      (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹)⁻¹)
      (Formalism.HermitianLatticesTheory.lValEta E M) :=
  ((fibreEquiv F E).hasProd_iff.2 (hasProd_eulerFac hc.cmUnram M hM).1).sigma
    fun v => hasProd_fibre hc M (by omega) v

theorem hasProd_density (hc : Formalism.BasicNotions.CMData F E) (M : ℕ) (hM : 2 ≤ M) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
      1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹)
      (Formalism.HermitianLatticesTheory.lValEta E M)⁻¹ := by
  simpa only [inv_inv] using
    (hasProd_inv hc M hM).inv₀ (hasProd_eulerFac hc.cmUnram M hM).2.ne'

theorem differentIdeal_eq_top (hc : Formalism.BasicNotions.CMData F E) : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  by_contra h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
  obtain ⟨⟨v, Q, hQ⟩, h⟩ := (fibreEquiv F E).surjective ⟨P, hP⟩
  obtain rfl : Q = P := congrArg Subtype.val h
  have := hQ.2
  have hu := unramifiedPlace hc v ⟨Q, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩ hQ.2
  exact (not_dvd_differentIdeal_iff.2 hu) (Ideal.dvd_iff_le.2 hle)

theorem abs_discr_eq (hc : Formalism.BasicNotions.CMData F E) :
    |(discr F : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv E) ^ Module.finrank ℚ F := by
  obtain ⟨h1, -, -, h4⟩ := GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex E hc.cmUnram.1
  have h2 := Module.finrank_mul_finrank ℚ F E
  rw [hc.deg2] at h2
  have hf : Module.finrank ℚ F = Formalism.HermitianLatticesTheory.fDeg E := by omega
  have hd := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [differentIdeal_eq_top hc, Ideal.absNorm_top, one_mul, hc.deg2] at hd
  have hd' : |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
    rw [← Int.cast_abs, ← Int.cast_abs, ← Nat.cast_natAbs, ← Nat.cast_natAbs, hd, Nat.cast_pow]
  rw [hf, ← h4, hd', Real.sqrt_sq (abs_nonneg _)]

theorem euler_product_discr_unramified : ∀ (I : Formalism.MainNotions.S.AutInst) (M : ℕ), 2 ≤ M →
    HasProd (fun u : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) =>
      1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta I.F I.E u ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard I.F u ^ M)⁻¹)
      (Formalism.HermitianLatticesTheory.lValEta I.E M)⁻¹ ∧
    |(discr I.F : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ I.f ∧
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace I.F I.E u :=
  fun I M hM => ⟨hasProd_density I.cm M hM, abs_discr_eq I.cm, unramifiedPlace I.cm⟩

end GlobalTheory.DensityEuler
