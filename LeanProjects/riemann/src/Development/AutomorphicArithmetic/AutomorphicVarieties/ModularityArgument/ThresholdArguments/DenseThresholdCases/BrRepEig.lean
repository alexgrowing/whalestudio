import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup
private theorem untwist (k N : ℕ) [NeZero N] (hk : 1 ≤ k) (χ ψ : DirichletCharacter ℂ N) (g : Eigenform k N χ) :
    ∃ (χ' : DirichletCharacter ℂ (N * N)) (g' : Eigenform k (N * N) χ'), ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      g'.a p * ψ (p : ZMod N) = g.a p ∧ χ' (p : ZMod (N * N)) * ψ (p : ZMod N) ^ 2 = χ (p : ZMod N) := by
  haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩
  obtain ⟨h, hc, hn⟩ := clTwist N k χ ψ⁻¹ g.f g.char
  have h0 : h ≠ 0 := by
    rintro rfl
    have := hn 1
    rw [g.one, Nat.cast_one, map_one, mul_one] at this
    simp [coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨g', hg'⟩ := eigEx (N * N) k hk _ h hc h0 fun p => ψ⁻¹ (p : ZMod N) * g.a p
  refine ⟨_, g', fun p hp hd => ?_⟩
  have hu : IsUnit (p : ZMod (N * N)) :=
    (ZMod.isUnit_prime_iff_not_dvd hp).2 fun e => hd ((hp.dvd_mul.1 e).elim id id)
  have hu' : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hd
  have e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ⁻¹ ^ 2) (p : ZMod (N * N)) =
      χ (p : ZMod N) * ψ⁻¹ (p : ZMod N) ^ 2 := by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ⁻¹ ^ 2) (dvd_mul_right N N) hu.unit
    rw [IsUnit.unit_spec, ZMod.cast_natCast (dvd_mul_right N N)] at this
    rw [this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
  have e1 : ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hu']
  constructor
  · rw [hg' p hp fun n h1 => ?_]
    · linear_combination g.a p * e1
    have := g.eig p hp n h1
    rw [e, hn, hn n, Nat.cast_mul, map_mul, Eigenform.a]
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hp.pos] at this ⊢
      rw [hn, Nat.cast_mul, map_mul]
      linear_combination ψ⁻¹ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ⁻¹ (m : ZMod N)) * this
    · rw [if_neg hpn] at this ⊢
      linear_combination ψ⁻¹ (p : ZMod N) * ψ⁻¹ (n : ZMod N) * this
  · rw [e]
    linear_combination χ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) + 1) * e1
private theorem eig_unique {k N p : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) (k : ℤ)} (hf : f ≠ 0)
    {a b : ℂ} (ha : IsEigAt k χ f p a) (hb : IsEigAt k χ f p b) : a = b := by
  by_contra h
  exact hf ((finDim N k).2 f fun n hn =>
    (mul_eq_zero.1 (show (a - b) * coef f n = 0 by linear_combination hb n hn - ha n hn)).resolve_left (sub_ne_zero.2 h))
private theorem level_zero_eq_maximal_compact {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    K1 w 0 = GlobalTheory.LFun.KGL w 2 := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _
private theorem lie_one (φ : TR.Sm ℚ 2) (h : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) : TR.lie ℚ 2 (TR.oneL ℚ 2) φ = 0 := by
  classical
  have hX : TR.lie ℚ 2 (TR.oneL ℚ 2) = ∑ i, TR.lieS ℚ 2 i i 1 := by
    simp only [TR.lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.sum_single_one (m := Fin 2) (α := TR.Rinf ℚ)).symm
  have h1 : ∀ i, TR.lieS ℚ 2 i i 1 = TR.Eop Rat.infinitePlace i i := fun i => by
    rw [TR.Eop_eq]
    congr 1
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    simp
  rw [hX, Fin.sum_univ_two, h1, h1]
  exact h _
private theorem ev_not_dvd {a : ℕ} (h : a ≠ 0) : ∀ᶠ w : Pl ℚ in Filter.cofinite, ¬ normV w ∣ a := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  obtain ⟨c, rfl⟩ := not_not.1 hw
  refine Ideal.dvd_span_singleton.2 ?_
  rw [Nat.cast_mul, (places w).2.1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
theorem UpperTheory.V.Br.repEig_of_printsH_of_hermEx :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.Gk.HermEx → UpperTheory.V.Br.RepEig := by
  intro P hH k hk π hπ
  have hk1 : 1 ≤ k := by omega
  obtain ⟨H, hH⟩ := hH ℚ 2 one_le_two π fun φ hφ => lie_one φ fun v => by
    rw [(capTwo ℚ π v _ _ (hπ v) φ hφ).1, add_neg_cancel, zero_smul]
  obtain ⟨N, ψ, ν, hN, hν, φ, hφ, h0, hlow, hfix⟩ := levelVec k π (holVec k hk π hπ H hH)
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt P.toClassicalTheorems ℚ (π.twist ν)
  have hc := fun z g => hω z φ hφ g
  obtain ⟨χ, hχ⟩ := charOf N hN ω φ h0 hlow.one hfix hc
  have hcusp := (π.twist ν).cusp φ hφ
  obtain ⟨f, hf, hL⟩ := deadel k N hN χ ω hχ φ hcusp hlow hfix hc
  have hf0 : f ≠ 0 := by
    rintro rfl
    refine h0 (Subtype.ext (funext fun g => ?_))
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp N hN g
    rw [hL γ h u hu]
    simp [nsl]
  have hhol : IsHol k (lev N) ω φ := ⟨hcusp.1, fun w u hu => hfix _ (kLocal N hN w u hu), hc, hlow.wt, hlow.low⟩
  obtain ⟨g, hg⟩ := eigEx N k hk1 χ f hf hf0 fun p => Classical.epsilon (IsEigAt k χ f p)
  obtain ⟨χ', g', hg'⟩ := untwist k N hk1 χ ψ g
  refine ⟨N * N, inferInstance, χ', g', ?_⟩
  filter_upwards [Gk.satAE ℚ 2 π, ev_not_dvd (NeZero.ne N),
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level ℚ ν).1] with w ⟨B, hB⟩ hw hu
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (TR.CuspSub.HasSat.card hB)
  refine ⟨α, β, hB, ?_⟩
  have hT := TR.CuspSub.HasSat.twist hB hu
  have hp := (places w).1
  have hv : GlobalTheory.LFun.IsSatVecGL w (locSm ℚ w) φ {α * ν.val w, β * ν.val w} :=
    (hT.2 ⟨φ, hφ⟩ (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal N hN w u (by
      rwa [(places w).2.2.2 N hN hw, level_zero_eq_maximal_compact])))) fun e => h0 (congrArg Subtype.val e)).map
      (π.twist ν).V.subtype (fun _ _ => rfl) h0
  obtain ⟨h1, h2⟩ := eigOf k N hk1 hN χ ω hχ f φ hL hhol w _ _ hw hv
  have h3 := Classical.epsilon_spec (p := IsEigAt k χ f (normV w)) ⟨_, h1⟩
  have h4 := (hg _ hp h3).trans (eig_unique hf0 h3 h1)
  obtain ⟨h5, h6⟩ := hg' _ hp hw
  have h7 := (charVal N hN ψ ν hν).2 w hw
  have h8 : ψ (normV w : ZMod N) ≠ 0 := h7 ▸ Units.ne_zero _
  simp only [Units.val_mul, h7] at h2 h4 ⊢
  constructor
  · refine mul_right_cancel₀ h8 ?_
    rw [h5, h4]; ring
  · refine mul_right_cancel₀ (pow_ne_zero 2 h8) ?_
    rw [h6, ← h2]; ring
end
