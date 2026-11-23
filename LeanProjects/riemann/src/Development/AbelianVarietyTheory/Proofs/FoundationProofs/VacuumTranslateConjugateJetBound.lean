import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCoeffMonomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SupLeEuclidean
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaNormUnimodularLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ConjJet

open MeasureTheory in

theorem mean_transport {V : Type} [NormedAddCommGroup V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddLeftInvariant]
    (P : V ≃+ V) (e : V ≃ᵐ V) (he : ∀ x, e x = P x) (hP : MeasurePreserving e μ μ)
    (A A' : AddSubgroup V) [DiscreteTopology A] (hA : ∀ x, P x ∈ A' ↔ x ∈ A) (f : V → ℝ)
    (hf : ∀ x ∈ A, ∀ z, f (P (x + z)) = f (P z)) :
    ⨍ z in Classical.epsilon (fun Fd => IsAddFundamentalDomain A' Fd μ), f z ∂μ =
      ⨍ z in Classical.epsilon (fun Fd => IsAddFundamentalDomain A Fd μ), f (P z) ∂μ := by
  haveI := GlobalTheory.countable_of_discrete_addSubgroup A
  obtain ⟨F0, -, -, hF0⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup A
  let φ : A ≃ A' :=
    { toFun := fun a => ⟨P a, (hA _).2 a.2⟩
      invFun := fun a => ⟨P.symm a, (hA _).1 (by simp)⟩
      left_inv := fun a => by simp
      right_inv := fun a => by simp }
  have hex' : ∃ Fd, IsAddFundamentalDomain A' Fd μ := by
    refine ⟨e.symm ⁻¹' F0, (hF0 μ).preimage_of_equiv (hP.symm e).quasiMeasurePreserving
      φ.bijective ?_⟩
    intro g z
    apply e.injective
    have h1 : ∀ y, P (e.symm y) = y := fun y => by rw [← he]; simp
    simp only [MeasurableEquiv.apply_symm_apply]
    change P g + z = e (g + e.symm z)
    rw [he, map_add, h1]
  have h' := Classical.epsilon_spec hex'
  have h := Classical.epsilon_spec (⟨F0, hF0 μ⟩ : ∃ Fd, IsAddFundamentalDomain A Fd μ)
  set S' := Classical.epsilon (fun Fd => IsAddFundamentalDomain A' Fd μ)
  set S := Classical.epsilon (fun Fd => IsAddFundamentalDomain A Fd μ)
  have h2 : IsAddFundamentalDomain A (e ⁻¹' S') μ := by
    refine h'.preimage_of_equiv hP.quasiMeasurePreserving φ.symm.bijective ?_
    intro g z
    change e (P.symm g + z) = g + e z
    rw [he, he, map_add]; simp
  have hi : ∫ z in S', f z ∂μ = ∫ z in S, f (P z) ∂μ := by
    rw [← hP.setIntegral_preimage_emb e.measurableEmbedding]
    simp only [he]
    exact h2.setIntegral_eq h (fun g z => hf g g.2 z)
  have hm : μ S' = μ S := by
    rw [← hP.measure_preimage_equiv S']
    have := h2.setLIntegral_eq h (fun _ => (1 : ENNReal)) (fun _ _ => rfl)
    simpa using this
  rw [setAverage_eq, setAverage_eq, hi, Measure.real, Measure.real, hm]

theorem Hf_re (D : D7) (T : Tor D) {N N' : ℕ} (z : VC D N N') :
    (Hf D T z z).re = (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area T.abelian₂ := by
  unfold Hf
  rw [Complex.div_ofReal_re]
  simp only [Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem Hf_add_re (D : D7) (T : Tor D) {N N' : ℕ} (z x : VC D N N') :
    (Hf D T (z + x) (z + x)).re = (Hf D T z z).re + 2 * (Hf D T z x).re + (Hf D T x x).re := by
  unfold Hf
  simp only [Complex.div_ofReal_re, Complex.re_sum]
  rw [mul_div_assoc', ← add_div, ← add_div]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem weight_periodic (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N'))
    (G : VC D N N' → ℂ) (hG : G ∈ ThSp D T A) (x : VC D N N') (hx : x ∈ A) (z : VC D N N') :
    ‖G (x + z)‖ ^ 2 * Real.exp (-Real.pi * (Hf D T (x + z) (x + z)).re) =
      ‖G z‖ ^ 2 * Real.exp (-Real.pi * (Hf D T z z).re) := by
  rw [← hG.2 x hx z, add_comm x z, Hf_add_re]
  simp only [al, U, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, Complex.norm_exp,
    mul_pow]
  rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  simp
  ring

def perm (D : D7) (N N' : ℕ) (π : Equiv.Perm D.what₂.Tau) : VC D N N' ≃+ VC D N N' where
  toFun z τ := z (π τ)
  invFun z τ := z (π.symm τ)
  left_inv z := by funext τ; simp
  right_inv z := by funext τ; simp
  map_add' _ _ := rfl

section Perm

variable {D : D7} {T T' : Tor D} {N N' : ℕ} {π : Equiv.Perm D.what₂.Tau}

theorem Hf_perm (hL : T'.abelian₂ = T.abelian₂) (z w : VC D N N') :
    Hf D T' (perm D N N' π z) (perm D N N' π w) = Hf D T z w := by
  unfold Hf
  rw [hL]
  congr 1
  exact Equiv.sum_comp π (fun τ => ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j))

theorem U_perm (hL : T'.abelian₂ = T.abelian₂) (x z : VC D N N') (G : VC D N N' → ℂ) :
    U D T' (perm D N N' π x) G (perm D N N' π z) = U D T x (fun w => G (perm D N N' π w)) z := by
  simp only [U, Hf_perm hL, map_add]

theorem La_perm (hL : T'.abelian₂ = T.abelian₂) (hE : ∀ τ x, T'.emb τ x = T.emb (π τ) x) (L L')
    (x : VC D N N') : perm D N N' π x ∈ La D T' L L' ↔ x ∈ La D T L L' := by
  have h : La D T' L L' = (La D T L L').map (perm D N N' π).toAddMonoidHom := by
    unfold La
    rw [AddMonoidHom.map_closure, hL]
    congr 1
    have hv : ∀ (w : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E),
        (perm D N N' π).toAddMonoidHom (w • embV D T A) = w • embV D T' A := by
      intro w A
      funext τ i j
      change w * T.emb (π τ) (A i j) = w * T'.emb τ (A i j)
      rw [hE]
    ext z
    constructor
    · rintro ⟨w, hw, A, hA, rfl⟩
      exact ⟨_, ⟨w, hw, A, hA, rfl⟩, hv w A⟩
    · rintro ⟨_, ⟨w, hw, A, hA, rfl⟩, rfl⟩
      exact ⟨w, hw, A, hA, hv w A⟩
  rw [h]
  exact AddSubgroup.mem_map_iff_mem (f := (perm D N N' π).toAddMonoidHom) (perm D N N' π).injective

theorem Th_perm (hL : T'.abelian₂ = T.abelian₂) (hE : ∀ τ x, T'.emb τ x = T.emb (π τ) x) (L L')
    (G : VC D N N' → ℂ) (hG : G ∈ Th D T' L L') :
    (fun w => G (perm D N N' π w)) ∈ Th D T L L' := by
  refine ⟨hG.1.comp ?_, fun x hx z => ?_⟩
  · change Differentiable ℂ (fun (z : VC D N N') τ => z (π τ))
    fun_prop
  · have := hG.2 _ ((La_perm hL hE L L' x).2 hx) (perm D N N' π z)
    rw [U_perm hL] at this
    simp only [al, Hf_perm hL] at this ⊢
    exact this

theorem normSq_perm (hL : T'.abelian₂ = T.abelian₂) (hE : ∀ τ x, T'.emb τ x = T.emb (π τ) x) (L L')
    [DiscreteTopology (La D T L L' : AddSubgroup (VC D N N'))]
    (G : VC D N N' → ℂ) (hG : G ∈ Th D T' L L') :
    normSq D T' (La D T' L L') G = normSq D T (La D T L L') (fun w => G (perm D N N' π w)) := by
  haveI h1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N → ℂ)).IsAddLeftInvariant :=
    MeasureTheory.Measure.pi.isAddLeftInvariant _
  haveI h2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddLeftInvariant :=
    MeasureTheory.Measure.pi.isAddLeftInvariant _
  haveI h3 : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddLeftInvariant :=
    MeasureTheory.Measure.pi.isAddLeftInvariant _
  have h := mean_transport (V := VC D N N') MeasureTheory.volume (perm D N N' π)
    (MeasurableEquiv.piCongrLeft (fun _ : D.what₂.Tau => Fin N' → Fin N → ℂ) π).symm
    (fun _ => rfl) (MeasureTheory.MeasurePreserving.symm _
      (MeasureTheory.volume_measurePreserving_piCongrLeft _ π))
    (La D T L L') (La D T' L L') (La_perm hL hE L L')
    (fun z => ‖G z‖ ^ 2 * Real.exp (-Real.pi * (Hf D T' z z).re))
    (fun x hx z => by
      simp only [Hf_perm hL]
      exact weight_periodic D T _ _ (Th_perm hL hE L L' G hG) x hx z)
  simp only [Hf_perm hL] at h
  exact h

end Perm

theorem discrete_of_int (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N'))
    (ha : 0 < area T.abelian₂) (hd : 0 < D.host.d) (h : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m) :
    DiscreteTopology A := by
  have hc : Continuous (fun x : VC D N N' => qH D T x) := by
    simp only [qH, Hf_re]
    fun_prop
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have : ({0} : Set A) = Subtype.val ⁻¹' ((fun x : VC D N N' => qH D T x) ⁻¹' Set.Iio 1) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_Iio]
    constructor
    · rintro rfl
      simp [qH, Hf_re]
    · intro hx
      obtain ⟨m, hm⟩ := h x x.2
      have hs : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
      have h0 : 0 ≤ qH D T (x : VC D N N') := by
        simp only [qH, Hf_re]
        positivity
      have hm0 : m = 0 := by
        rw [hm] at hx h0
        have h1 : m < 1 := by exact_mod_cast hx
        have h2 : 0 ≤ m := by exact_mod_cast h0
        omega
      rw [hm0] at hm
      simp only [qH, Hf_re, Int.cast_zero, mul_eq_zero, div_eq_zero_iff] at hm
      have hz : ∑ τ, ∑ i, ∑ j, ‖(x : VC D N N') τ i j‖ ^ 2 = 0 := by
        rcases hm with (h1 | h1) | h1 | h1
        · exact absurd h1 hs.ne'
        · norm_num at h1
        · exact h1
        · exact absurd h1 ha.ne'
      apply Subtype.ext
      funext τ i j
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hz τ (Finset.mem_univ _)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 h1 i (Finset.mem_univ _)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 h2 j (Finset.mem_univ _)
      simpa using h3
  rw [this]
  exact (isOpen_Iio.preimage hc).preimage continuous_subtype_val

theorem area_pos (D : D7) (hg : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) :
    0 < area (lamOf D cc δ) := by
  obtain ⟨-, hδ, -, ha, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hN : (0 : ℝ) < (Ideal.absNorm cc : ℝ) := by
    have : Ideal.absNorm cc ≠ 0 := fun h => hc.1.1 (Ideal.absNorm_eq_zero_iff.1 h)
    positivity
  have := norm_pos_iff.2 hδ
  rw [ha]
  positivity

theorem thetaZeroNormSq_ne_zero_cmLattice (D : D7) (hg : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ t : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) :
    nrm1Sq (lamOf D cc δ) (GL3Theta.th0 (lamOf D cc δ) t) ≠ 0 := by
  have ha := area_pos D hg cc δ hc
  obtain ⟨hl, -, hΔ, -, hO⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc
  obtain ⟨h1, h2⟩ := GlobalTheory.OddThetaNorm.odd_theta_norm_sigma_star _ hl hΔ
  have htn : t ∉ lamOf D cc δ := by
    intro h
    obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
    have := hO a t h
    rw [ha] at this
    exact ht.2.1 this
  have hu : U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ)) 0 ≠ 0 := by
    unfold U1
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    rw [zero_add]
    exact fun h => htn (((GlobalTheory.OddTheta.sgStar_laws _ hl).2.1 t).1 h)
  rw [h2 t hu]
  refine div_ne_zero (fun h => ?_) (pow_ne_zero _ (norm_ne_zero_iff.2 hu))
  rw [h] at h1
  have : 0 < 2 * Real.pi ^ 2 / area (lamOf D cc δ) := by
    have := Real.pi_pos
    positivity
  rw [← h1] at this
  simp at this

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z
  simp [U, Hf]

theorem U_ne_zero (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (G : VC D N N' → ℂ)
    (hG : G ≠ 0) : U D T x G ≠ 0 := by
  intro h
  apply hG
  funext z
  have := congrFun h (z - x)
  simpa [U] using this

theorem U_diff (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (G : VC D N N' → ℂ)
    (hG : Differentiable ℂ G) : Differentiable ℂ (U D T x G) := by
  unfold U Hf
  fun_prop

theorem normSq_nonneg (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N'))
    (G : VC D N N' → ℂ) : 0 ≤ normSq D T A G := by
  unfold normSq
  simp only [MeasureTheory.average_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 MeasureTheory.measureReal_nonneg)
    (MeasureTheory.integral_nonneg fun z => by positivity)

theorem comb_one (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) :
    comb D T (fun _ : Fin 1 => 1) (fun _ => 0) G = G := by
  funext z
  simp [comb, U_zero]

theorem sup_perm (D : D7) (hg : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ)
    (T : Tor D) (π : Equiv.Perm D.what₂.Tau) (hL : T.abelian₂ = lamOf D cc δ)
    (hE : ∀ τ x, T.emb τ x = embT D (π τ) x) (N N' : ℕ) (L L') (h1 : SD D L) (h2 : SD D L')
    (G : VC D N N' → ℂ) (hG : G ∈ Th D T L L') (y z : VC D N N') :
    ‖U D T y G z‖ ^ 2 ≤ 3 * (2 * ((fF D * N * N' : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * N * N') *
      normSq D T (La D T L L') G * Real.exp (Real.pi * (Hf D T z z).re) := by
  have hL' : T.abelian₂ = (tor0 D cc δ).abelian₂ := hL
  have hE' : ∀ τ x, T.emb τ x = (tor0 D cc δ).emb (π τ) x := hE
  haveI : DiscreteTopology (La D (tor0 D cc δ) L L' : AddSubgroup (VC D N N')) :=
    discrete_of_int D (tor0 D cc δ) _ (area_pos D hg cc δ hc) D.host.hyp.2.1.pos
      (GlobalTheory.ThetaLine.theta_line D hg cc δ hc N N' _ (Or.inr ⟨L, L', h1, h2, rfl⟩)).2.2.2.2.2.2
  obtain ⟨y, rfl⟩ := (perm D N N' π).surjective y
  obtain ⟨z, rfl⟩ := (perm D N N' π).surjective z
  rw [U_perm hL', Hf_perm hL', normSq_perm hL' hE' L L' G hG]
  exact GlobalTheory.ThetaSupPair.sup_translate_le D hg cc δ hc N N' L L' h1 h2 _ (Th_perm hL' hE' L L' G hG) y z

theorem cj_bar (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) :
    ‖cj M (rhoBar M ρ) x‖ = ‖cj M ρ x‖ := by
  simp [cj, rhoBar]

theorem area_conj (Λ : AddSubgroup ℂ) :
    area (Λ.map (starRingEnd ℂ).toAddMonoidHom) = area Λ := by
  unfold area
  congr 1
  ext a
  have key : ∀ u v : ℂ, |((starRingEnd ℂ) ((starRingEnd ℂ) u) * (starRingEnd ℂ) v).im| =
      |((starRingEnd ℂ) u * v).im| := by
    intro u v
    rw [← map_mul, Complex.conj_im, abs_neg]
  constructor
  · rintro ⟨h0, _, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, h⟩
    exact ⟨h0, u, hu, v, hv, h.trans (key u v)⟩
  · rintro ⟨h0, u, hu, v, hv, h⟩
    exact ⟨h0, _, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, h.trans (key u v).symm⟩

theorem jet_bound_fix (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (hGT : G ∈ Th D (tor0 D cc δ) L L')
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (n : D.what₂.Tau → ℕ) (B : ℝ) (hB : 1 ≤ B) (hn : ∀ τ, (n τ : ℝ) ≤ 2 * B)
    (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) (T : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
    ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤
      ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 *
        (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) *
          normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
            (fnConj D Qbar ρ G) *
          (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (hI.t0Ex cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := hI.curve cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := hI.perm Qbar ρ hρ hdata.1
  have hne : fnConj D Qbar ρ G ≠ 0 := by
    intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hI.g1 cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  obtain ⟨m, hm, hmy⟩ := id hy
  obtain ⟨y', hy', -⟩ := hI.galEx cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy
    (by omega)
  have hgal := (hI.gal cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m
    hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA)
    (by rw [comb_one]; exact hAU y hy)).1
  rw [comb_one] at hgal
  have hdiff := U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1
  obtain ⟨hmem, hcj⟩ := (GlobalTheory.ConjSeries.taylor_fnConj D a d Qbar ρ (U D (tor0 D cc δ) y G)
    (by rw [hgal]; exact hdiff) (by rw [hgal]; exact U_ne_zero D _ _ _ hne)).2 (hAU y hy) n T
  refine ⟨hmem, ?_⟩
  rw [hcj, hgal]
  have hr : 0 ≤ D.host.rdE := Real.rpow_nonneg (abs_nonneg _) _
  refine (GlobalTheory.MinorBound.minor_bound D a d n _ _ (area (lamConj Qbar ρ (lamOf D cc δ))) B
    (by rw [hΛ]; exact area_pos D hI.g1 cc' δ' hc') hB ?_ hn hdiff fun z => ?_).2 T
  · have := normSq_nonneg D (torConj D (tor0 D cc δ) Qbar ρ)
      (La D (torConj D (tor0 D cc δ) Qbar ρ) L L') (fnConj D Qbar ρ G)
    positivity
  · have := sup_perm D hI.g1 cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
      hTh y' z
    rw [Hf_re, ← mul_div_assoc] at this
    exact this

theorem vacuum_mem_thetaSpace_pair (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ∈ Th D (tor0 D cc δ) L L' := by
  obtain ⟨b, κ, hb, -, rfl⟩ := hG
  obtain ⟨-, ⟨hd, hinv⟩, -⟩ := hI.uni cc δ hc a d _ _ (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨L, L', h1, h2, rfl⟩) _ (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D hI.g1 cc δ t0 hc ht b hb.1)
  refine ⟨hd.const_mul κ, fun x hx z => ?_⟩
  have := hinv x hx z
  simp only [U] at this ⊢
  rw [show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]
  ring

theorem conj_jet_bound : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L', SD D L → SD D L' → Even (a * d) → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ∀ y, LaQ D (tor0 D cc δ) L L' y → ∀ (n : D.what₂.Tau → ℕ) (B : ℝ), 1 ≤ B → (∀ τ, (n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ T : Tup D a d n, GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧ ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * a * d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  intro D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy n B hB hn ρ t0' ht' T
  have hGT := vacuum_mem_thetaSpace_pair D hI cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t0' ht'
  rw [← hN]
  obtain ⟨hfix | hfix, htor, hbar⟩ := hI.bar cc δ hc Qbar ρ hdata
  · exact jet_bound_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB hn ρ hfix T
  · obtain ⟨hmem, hle⟩ := jet_bound_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB
      hn (rhoBar Qbar ρ) hfix T
    refine ⟨hmem, ?_⟩
    obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
    have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
    rw [U_zero] at hn2
    have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
        (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg Tor.abelian₂ htor
    rw [cj_bar, (hbar a d L L' G).1, htor, hn2, hL, area_conj] at hle
    exact hle

end GlobalTheory.ConjJet
