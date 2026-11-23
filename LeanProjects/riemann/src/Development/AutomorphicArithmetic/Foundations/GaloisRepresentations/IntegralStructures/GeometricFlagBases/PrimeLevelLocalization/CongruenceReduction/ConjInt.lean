import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.Int.Geo.Pl.Tj.TorusKilling

variable {E : Type} [Field E] [NumberField E]

private theorem val_alg (u : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) :
    Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) c) = u.intValuation c := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u (c : E)
  rw [show (u.valuation E) (c : E) = u.intValuation c from HeightOneSpectrum.valuation_of_algebraMap u c] at h
  exact h

private theorem alg_int (u : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) :
    algebraMap (𝓞 E) (u.adicCompletion E) c ∈ u.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, val_alg]
  exact u.intValuation_le_one c

private theorem exS (w : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) (hc : c ≠ 0) :
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ u : HeightOneSpectrum (𝓞 E), u ≠ w →
      Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) s) ≤ Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) c) := by
  classical
  have hI : Ideal.span {c} ≠ ⊥ := by simpa using hc
  have := w.isMaximal
  obtain ⟨Q, hQ, hIQ⟩ := Ideal.eq_prime_pow_mul_coprime hI w.asIdeal
  have hex : ∃ s ∈ Q, s ∉ w.asIdeal := by
    by_contra hcon
    push_neg at hcon
    have : Q ≤ w.asIdeal := hcon
    rw [sup_eq_left.2 this] at hQ
    exact w.isPrime.ne_top hQ
  obtain ⟨s, hsQ, hsw⟩ := hex
  refine ⟨s, hsw, fun u hu => ?_⟩
  rw [val_alg, val_alg]
  rw [HeightOneSpectrum.intValuation_if_neg u hc]
  refine (HeightOneSpectrum.intValuation_le_pow_iff_mem u s _).2 ?_
  set e := (Associates.mk u.asIdeal).count (Associates.mk (Ideal.span {c})).factors with he
  have hce : c ∈ u.asIdeal ^ e := by
    refine (HeightOneSpectrum.intValuation_le_pow_iff_mem u c e).1 ?_
    rw [HeightOneSpectrum.intValuation_if_neg u hc]
  have hle : Ideal.span {c} ≤ u.asIdeal ^ e := (Ideal.span_singleton_le_iff_mem _).2 hce
  generalize Multiset.count w.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {c})) = m at hIQ
  have hdvd : u.asIdeal ^ e ∣ w.asIdeal ^ m * Q := by
    rw [← hIQ]; exact Ideal.dvd_iff_le.2 hle
  have hcop : IsCoprime (u.asIdeal ^ e) (w.asIdeal ^ m) := by
    refine IsCoprime.pow ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne u.isMaximal w.isMaximal (fun h => hu (HeightOneSpectrum.ext h))
  exact Ideal.le_of_dvd (hcop.dvd_of_dvd_mul_left hdvd) hsQ

private theorem conj_int [IsCMField E] {n : ℕ} (u : HeightOneSpectrum (𝓞 E)) (a h : GL (Fin n) (u.adicCompletion E)) (ha : a ∈ KGL u n)
    (t : u.adicCompletion E) (ht : ∀ i k, (t • h.val) i k ∈ u.adicCompletionIntegers E) (i k : Fin n) :
    t * (a * h * a⁻¹).val i k ∈ u.adicCompletionIntegers E := by
  obtain ⟨h1, h2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 ha
  have e : t * (a * h * a⁻¹).val i k = (a.val * (t • h.val) * (a⁻¹).val) i k := by
    simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [e, Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ (h2 _ _)
  rw [Matrix.mul_apply]
  exact sum_mem fun m _ => mul_mem (h1 _ _) (ht _ _)

private theorem diag_int {n : ℕ} (u : HeightOneSpectrum (𝓞 E)) (ϖ : u.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E u ϖ) (i : ℕ)
    (y : 𝓞 E) (hy : y ∈ u.asIdeal) (a b : Fin n) :
    (algebraMap (𝓞 E) (u.adicCompletion E) y •
      Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1) a b ∈ u.adicCompletionIntegers E := by
  rw [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h1 h2
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, val_alg]
    have h3 : u.intValuation y ≤ Valued.v ϖ := by
      rw [hϖ]
      have := (HeightOneSpectrum.intValuation_le_pow_iff_mem u y 1).2 (by rwa [pow_one])
      exact this
    exact mul_inv_le_one_of_le₀ h3 zero_le'
  · rw [mul_one]; exact alg_int u y
  · rw [mul_zero]; exact zero_mem _

end UpperTheory.Gal.Int.Geo.Pl.Tj.TorusKilling

open UpperTheory.Gal.Int.Geo.Pl.Tj.TorusKilling in
theorem UpperTheory.Gal.Int.Geo.Pl.Tj.tKill :
    UpperTheory.Gal.Int.Geo.Pl.Tj.TKill := by
  intro hS hD hL E _ _ _ A n p _ S F x hx N w σ i hi g hg
  have hqp := σ.atp.prime
  have hqw : ((σ.q : ℕ) : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hc : ((Ideal.absNorm w.asIdeal ^ i : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hN0)
  obtain ⟨s, hsw, hs⟩ := exS w _ hc
  refine ⟨s, hsw, fun y hy v hv => ?_⟩
  have key : ∀ (u : Plc E) (a b : Fin n), algebraMap (𝓞 E) (u.adicCompletion E) (s * y) * F.cmp u g⁻¹ a b ∈ u.adicCompletionIntegers E := by
    intro u a b
    by_cases hqu : ((σ.q : ℕ) : 𝓞 E) ∈ u.asIdeal
    · have ha := F.a_int u σ.q hqp σ.good hqu
      by_cases huw : u = w
      · subst huw
        obtain ⟨ϖ, hϖ, ht⟩ := hg.at_w
        have hϖ0 : ϖ ≠ 0 := by
          intro h0
          rw [Formalism.UG.IsUnifV, h0, map_zero] at hϖ
          exact WithZero.zero_ne_coe hϖ
        have hinv : (comp u g⁻¹).val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1 := by
          have h1 : (comp u g⁻¹).val * (comp u g).val = 1 := by
            rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
          have h2 : (comp u g).val * (Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1) = 1 := by
            rw [ht, Matrix.diagonal_mul_diagonal]
            have hk : ∀ k : Fin n, (if (k : ℕ) < i then ϖ else 1) * (if (k : ℕ) < i then ϖ⁻¹ else 1) = (1 : u.adicCompletion E) := by
              intro k
              split_ifs
              · exact mul_inv_cancel₀ (G₀ := u.adicCompletion E) hϖ0
              · exact mul_one 1
            simp only [hk]
            exact Matrix.diagonal_one
          calc (comp u g⁻¹).val = (comp u g⁻¹).val * ((comp u g).val * _) := by rw [h2, Matrix.mul_one]
            _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        rw [map_mul, mul_assoc]
        refine mul_mem (alg_int u s) (conj_int u _ _ ha _ (fun a b => ?_) a b)
        rw [hinv]
        exact diag_int u ϖ hϖ i y hy a b
      · have h1 := conj_int u (F.a u) (comp u g⁻¹) ha ((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E) (hg.back u) a b
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
        rw [map_mul, map_mul, map_mul, mul_comm (Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) s)), mul_assoc]
        have h2 := hs u huw
        rw [map_natCast] at h2
        have h3 : Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) y) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (alg_int u y)
        rw [map_mul] at h1
        calc _ ≤ 1 * (Valued.v (((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E)) * Valued.v (F.cmp u g⁻¹ a b)) :=
              mul_le_mul' h3 (mul_le_mul' h2 le_rfl)
          _ ≤ 1 := by rw [one_mul]; exact h1
    · have hne : u ≠ w := fun h => hqu (h ▸ hqw)
      have hoff : comp u g = 1 := hg.off u hne fun hK => hqu ?_
      · have h1 : F.cmp u g⁻¹ = 1 := by
          simp [Frame.cmp, map_inv, hoff]
        rw [h1, Matrix.one_apply]
        split_ifs
        · rw [mul_one]; exact alg_int u _
        · rw [mul_zero]; exact zero_mem _
      · have hq' : ((σ.q : ℕ) : 𝓞 E) ∈ (cj u).asIdeal := (hK _ (by simp)).2 hqw
        have e : (cj u).asIdeal = _ := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (GlobalTheory.CuspRep.conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
        rw [e, Ideal.mem_comap, map_natCast] at hq'
        exact hq'
  classical
  let Y : ∀ u : Plc E, Fin n → u.adicCompletion E := fun u =>
    if (p : 𝓞 E) ∈ u.asIdeal then 0 else algebraMap (𝓞 E) (u.adicCompletion E) (s * y) • (F.cmp u g⁻¹ *ᵥ F.vec u (v))
  have hY : ∀ u k, Y u k ∈ u.adicCompletionIntegers E := by
    intro u k
    by_cases hp : (p : 𝓞 E) ∈ u.asIdeal
    · simp only [Y, if_pos hp]; exact zero_mem _
    · simp only [Y, if_neg hp, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]
      refine sum_mem fun l _ => ?_
      rw [← mul_assoc]
      exact mul_mem (key u k l) ((F.vec_hat v).1 hv u hp l)
  obtain ⟨v', hv'⟩ := F.vec_surj Y hY
  refine ⟨v', (F.vec_hat v').2 fun u hu k => ?_, ?_⟩
  · rw [hv' u hu]; exact hY u k
  · refine sub_eq_zero.1 (F.vec_inj _ fun u hu => ?_)
    have hmul : (F.a u * comp u g * (F.a u)⁻¹).val * F.cmp u g⁻¹ = 1 := by
      rw [Frame.cmp, ← Units.val_mul, map_inv]
      simp
    rw [map_sub, F.vec_act u hu, F.vec_mul u hu, hv' u hu]
    simp only [Y, if_neg hu]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec, sub_self]
