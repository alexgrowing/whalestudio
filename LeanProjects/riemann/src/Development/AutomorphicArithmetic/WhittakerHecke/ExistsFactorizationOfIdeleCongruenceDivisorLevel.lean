import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharpolySmulMap
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem cp_pv (v w : H.P ℚ) :
    H.cp v ((pv w : (A ℚ)ˣ) : A ℚ) = if w = v then ((atFin v (unif v) : (H.Kv v)ˣ) : H.Kv v) else 1 := by
  obtain ⟨-, -, h3, h4, -, -, -, h8, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws ℚ w
  rw [pv, h4, map_add, map_one]
  split_ifs with h
  · subst h
    rw [h3, add_sub_cancel]
  · have : H.cp v (H.sg w (((atFin w (unif w) : (H.Kv w)ˣ) : H.Kv w) - 1)) = 0 := (h8 _).2 v (Ne.symm h)
    rw [this, add_zero]

private theorem fin_supp {n : ℕ} : (Function.mulSupport fun v : H.P ℚ => pv v ^ n.factorization (normV v)).Finite := by
  refine (n.factorization.support.finite_toSet.preimage GlobalTheory.TwAtt.normV_injective.injOn).subset fun v hv => ?_
  exact Finsupp.mem_support_iff.2 fun (h : n.factorization (normV v) = 0) => hv (by simp only [h, pow_zero])

private theorem cp_pin (n : ℕ) (v : H.P ℚ) :
    H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) = ((atFin v (unif v) : (H.Kv v)ˣ) : H.Kv v) ^ n.factorization (normV v) := by
  have h := ((H.cp v).toMonoidHom.comp (Units.coeHom (A ℚ))).map_finprod (fin_supp (n := n))
  refine h.trans ((finprod_eq_single _ v fun w hw => ?_).trans ?_)
  · rw [map_pow]
    change H.cp v ((pv w : (A ℚ)ˣ) : A ℚ) ^ _ = 1
    rw [cp_pv, if_neg hw, one_pow]
  · rw [map_pow]
    change H.cp v ((pv v : (A ℚ)ˣ) : A ℚ) ^ _ = _
    rw [cp_pv, if_pos rfl]

private theorem val_nat (v : H.P ℚ) (n : ℕ) : Valued.v (n : H.Kv v) = v.intValuation (n : 𝓞 ℚ) := by
  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (n : 𝓞 ℚ)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
  simpa using h1

private theorem fst_pin (n : ℕ) : ((pin n : (A ℚ)ˣ) : A ℚ).1 = 1 := by
  have h := ((RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom.comp
    (Units.coeHom (A ℚ))).map_finprod (fin_supp (n := n))
  refine h.trans (finprod_eq_one_of_forall_eq_one fun w => ?_)
  rw [map_pow]
  exact one_pow _

private theorem iy_val {r : ℝ} (hr : r ≠ 0) :
    ((iy r : (A ℚ)ˣ) : A ℚ).1 = TR.infEq ℚ (fun _ => r) ∧ ∀ v : H.P ℚ, H.cp v ((iy r : (A ℚ)ˣ) : A ℚ) = 1 := by
  rw [iy, dif_neg hr]
  have e : ∀ u : (TR.Rinf ℚ)ˣ, ((TR.infId ℚ u : (A ℚ)ˣ) : A ℚ) = 1 - TR.sInf ℚ 1 + TR.sInf ℚ u := fun _ => rfl
  rw [e]
  refine ⟨?_, fun v => ?_⟩
  · change 1 - TR.infEq ℚ 1 + TR.infEq ℚ _ = _
    rw [map_one, sub_self, zero_add]
  · rw [map_add, map_sub, map_one]
    change 1 - 0 + 0 = _
    simp

theorem UpperTheory.exists_factorization_of_ideleCongruence_divisor_level :
    ∀ (L N : ℕ), 0 < N → L ∣ N → (∀ v, Bad N v → Bad L v) → ∀ y : (A ℚ)ˣ, (∀ v, Bad N v → Dv L v ((y : A ℚ) - 1)) → (∀ v : H.P ℚ, ¬ Bad N v → Valued.v (H.cp v (y : A ℚ)) ≤ 1) → ∃ (n : ℕ) (r : ℝ) (τ : (A ℚ)ˣ), 0 < n ∧ n.Coprime N ∧ r ≠ 0 ∧ τ ∈ TT L ∧ y = iy r * pin n * τ := by
  intro L N hN hLN hbad y h1 h2
  have hv : ∀ (M : ℕ) (v : H.P ℚ), (Bad M v → Valued.v (M : H.Kv v) < 1) ∧ (¬ Bad M v → Valued.v (M : H.Kv v) = 1) := fun M v => by
    rw [val_nat]
    exact ⟨fun h => (v.intValuation_lt_one_iff_mem _).2 h, fun h => HeightOneSpectrum.intValuation_eq_one_iff.2 h⟩
  have hb : ∀ v, Bad N v → Valued.v (H.cp v (y : A ℚ)) = 1 := fun v h => by
    have h3 := (h1 v h).trans_lt ((hv L v).1 (hbad v h))
    rw [map_sub, map_one] at h3
    have := Valuation.map_one_add_of_lt Valued.v h3
    rwa [add_sub_cancel] at this
  have hle : ∀ v, Valued.v (H.cp v (y : A ℚ)) ≤ 1 := fun v => by
    by_cases h : Bad N v
    exacts [(hb v h).le, h2 v h]
  have hinv : ∀ v, H.cp v (y : A ℚ) * H.cp v ((y⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := fun v => by
    rw [← map_mul, Units.mul_inv, map_one]
  have hne : ∀ v, Valued.v (H.cp v (y : A ℚ)) ≠ 0 := fun v =>
    (Valuation.ne_zero_iff _).2 (left_ne_zero_of_mul_eq_one (hinv v))
  have hex : ∀ v, ∃ e : ℕ, Valued.v (H.cp v (y : A ℚ)) = WithZero.exp (-1 : ℤ) ^ e := fun v => by
    have h3 : WithZero.log (Valued.v (H.cp v (y : A ℚ))) ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log (hne v)]
      exact hle v
    refine ⟨(-WithZero.log (Valued.v (H.cp v (y : A ℚ)))).toNat, ?_⟩
    rw [← WithZero.exp_nsmul, nsmul_eq_mul, Int.toNat_of_nonneg (by omega), mul_neg_one, neg_neg, WithZero.exp_log (hne v)]
  choose e he using hex
  have he0 : ∀ v, Valued.v (H.cp v (y : A ℚ)) = 1 → e v = 0 := fun v h => by
    rw [he v, ← WithZero.exp_nsmul, WithZero.exp_eq_one] at h
    simpa using h
  have hfin : (Function.support e).Finite := by
    have h3 : ∀ᶠ v : H.P ℚ in cofinite, ((y⁻¹ : (A ℚ)ˣ) : A ℚ).2 v ∈ v.adicCompletionIntegers ℚ := ((y⁻¹ : (A ℚ)ˣ) : A ℚ).2.2
    refine (Filter.eventually_cofinite.1 h3).subset fun v hv' h4 => hv' (he0 v (le_antisymm (hle v) ?_))
    have h5 := congrArg Valued.v (hinv v)
    rw [map_mul, map_one] at h5
    have h6 : Valued.v (H.cp v ((y⁻¹ : (A ℚ)ˣ) : A ℚ)) ≤ 1 := h4
    exact h5.symm.trans_le (mul_le_of_le_one_right' h6)
  let f : ℕ →₀ ℕ := Finsupp.mapDomain normV (Finsupp.ofSupportFinite e hfin)
  have hf : ∀ v, f (normV v) = e v := fun v => Finsupp.mapDomain_apply GlobalTheory.TwAtt.normV_injective _ v
  have hfs : ∀ p ∈ f.support, ∃ v : H.P ℚ, normV v = p := fun p hp => by
    obtain ⟨v, -, hv'⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hp)
    exact ⟨v, hv'⟩
  have hpr : ∀ p ∈ f.support, p.Prime := fun p hp => (hfs p hp).elim fun v h => h ▸ GlobalTheory.TwAtt.normV_prime v
  have hfac := Nat.prod_pow_factorization_eq_self hpr
  set n := f.prod (· ^ ·) with hn
  have hn0 : 0 < n := Finset.prod_pos fun p hp => pow_pos (hpr p hp).pos _
  have hr : re (y : A ℚ) ≠ 0 := by
    have h3 := congrFun (congrArg (TR.pInf ℚ) y.mul_inv) Rat.infinitePlace
    rw [map_mul, map_one] at h3
    exact left_ne_zero_of_mul_eq_one h3
  obtain ⟨i1, i2⟩ := iy_val hr
  have hτ : ∀ v, H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) * H.cp v (((iy (re (y : A ℚ)) * pin n)⁻¹ * y : (A ℚ)ˣ) : A ℚ) =
      H.cp v (y : A ℚ) := fun v => by
    conv_rhs => rw [← mul_inv_cancel_left (iy (re (y : A ℚ)) * pin n) y, Units.val_mul, Units.val_mul, map_mul, map_mul, i2,
      one_mul]
  have hu : ∀ v, Valued.v (H.cp v (((iy (re (y : A ℚ)) * pin n)⁻¹ * y : (A ℚ)ˣ) : A ℚ)) = 1 := fun v => by
    have h3 := congrArg Valued.v (hτ v)
    rw [map_mul, cp_pin, map_pow, unif_spec v, hfac, hf, ← he v] at h3
    exact (mul_eq_left₀ (hne v)).1 h3
  refine ⟨n, re (y : A ℚ), (iy (re (y : A ℚ)) * pin n)⁻¹ * y, hn0, ?_, hr, ⟨⟨?_, hu⟩, fun v => ?_⟩,
    (mul_inv_cancel_left _ _).symm⟩
  · refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.pow_left _ (((hpr p hp).coprime_iff_not_dvd).2 fun hd => ?_)
    obtain ⟨v, rfl⟩ := hfs p hp
    exact Finsupp.mem_support_iff.1 hp ((hf v).trans (he0 v (hb v ((GlobalTheory.TwAtt.mem_iff v N).2 hd))))
  · have h3 : ((iy (re (y : A ℚ)) * pin n : (A ℚ)ˣ) : A ℚ).1 = (y : A ℚ).1 := by
      change ((iy (re (y : A ℚ)) : (A ℚ)ˣ) : A ℚ).1 * ((pin n : (A ℚ)ˣ) : A ℚ).1 = _
      rw [i1, fst_pin, mul_one, ← RingEquiv.eq_symm_apply]
      funext w
      rw [Subsingleton.elim w Rat.infinitePlace]
      rfl
    have h4 : (((iy (re (y : A ℚ)) * pin n)⁻¹ : (A ℚ)ˣ) : A ℚ).1 * ((iy (re (y : A ℚ)) * pin n : (A ℚ)ˣ) : A ℚ).1 = 1 :=
      congrArg Prod.fst (Units.inv_mul (iy (re (y : A ℚ)) * pin n))
    rw [h3] at h4
    exact h4
  · by_cases h : Bad N v
    · have h3 := hτ v
      rw [cp_pin, hfac, hf, he0 v (hb v h), pow_zero, one_mul] at h3
      have h4 := h1 v h
      simp only [Dv, map_sub] at h4 ⊢
      rwa [h3]
    · have h3 : ¬ Bad L v := fun h' => h ((GlobalTheory.TwAtt.mem_iff v N).2 (((GlobalTheory.TwAtt.mem_iff v L).1 h').trans hLN))
      simp only [Dv, map_sub, map_one]
      rw [(hv L v).2 h3]
      exact Valuation.map_sub_le _ (hu v).le (map_one _).le
