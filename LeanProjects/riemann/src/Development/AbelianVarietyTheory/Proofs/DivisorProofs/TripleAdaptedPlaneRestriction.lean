import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdaptedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAbsGtOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermHaarVanishStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKSplitEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def lawChr (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ℂ := (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)

theorem lawChr_one (χ : Chr F E) (z : ℝ) : lawChr χ z 1 = 1 := by simp [lawChr]

theorem lawChr_mul (χ : Chr F E) (z : ℝ) (s t : (AE F E)ˣ) :
    lawChr χ z (s * t) = lawChr χ z s * lawChr χ z t := by
  simp only [lawChr, map_mul, Circle.coe_mul, NNReal.coe_mul]
  rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  push_cast
  ring

theorem norm_lawChr (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ‖lawChr χ z t‖ = (absE F E t : ℝ) ^ z := by
  rw [lawChr, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]

theorem lawChr_ne (α β : Chr F E) {z z' : ℝ} (hz : z < z') {t : (AE F E)ˣ} (ht : 1 < (absE F E t : ℝ)) :
    lawChr α z t ≠ lawChr β z' t := fun e => by
  have h := congrArg norm e
  rw [norm_lawChr, norm_lawChr] at h
  exact (Real.rpow_lt_rpow_of_exponent_lt ht hz).ne h

theorem indep {f g : (AE F E)ˣ → ℂ} (hf : f 1 = 1) (hg : g 1 = 1) (hne : ∃ t, f t ≠ g t) {P Q : ℂ}
    (h : ∀ t, P * f t + Q * g t = 0) : P = 0 ∧ Q = 0 := by
  obtain ⟨t, ht⟩ := hne
  have h1 := h 1
  rw [hf, hg, mul_one, mul_one] at h1
  have hQ : Q = -P := by linear_combination h1
  have h2 := h t
  rw [hQ] at h2
  have h3 : P * (f t - g t) = 0 := by linear_combination h2
  have hP : P = 0 := (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 ht)
  exact ⟨hP, by rw [hQ, hP, neg_zero]⟩

variable {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem isLevi_one (H' : Plane E d d₁) : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat]

theorem isLevi_mul {H' : Plane E d d₁} {t s : (AE F E)ˣ} {m m' : UA σ W.J}
    (h : IsLevi (W₁ := W₁) H' t 1 m) (h' : IsLevi (W₁ := W₁) H' s 1 m') :
    IsLevi (W₁ := W₁) H' (t * s) 1 (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (1 : UA σ W₁.J) = 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h'.1, Matrix.mulVec_smul, h.1, smul_smul, Units.val_mul, mul_comm]
  · rw [e, ← Matrix.mulVec_mulVec, h'.2.1, Matrix.mulVec_smul, h.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [e, Matrix.mul_assoc, h'.2.2, e1, Matrix.mul_one]
    simpa [e1] using h.2.2

theorem split2_of {a a' : ℕ} {W : Spc F E (a + a')} {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁}
    {X : Chars F E} {f : UA σ W.J → ℂ}
    (hlevi : ∀ t : (AE F E)ˣ, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m)
    (hbig : ∃ t : (AE F E)ˣ, 1 < (absE F E t : ℝ)) (hlt : a' < a)
    (huniq : ∀ (μ₀ : Measure (unip σ W H')) (𝓕₀ : Set (unip σ W H')), μ₀.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕₀ μ₀ → μ₀ 𝓕₀ = 1 →
      IsCT H' f (fun h => ∫ u in 𝓕₀, f (u.1 * h) ∂μ₀))
    (hexp : ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h, ∃ A B : ℂ,
        ∀ t m, IsLevi (W₁ := W₁) H' t 1 m →
          ∫ u in 𝓕, f (u.1 * (m * h)) ∂μ = A * lawChr X.α ((a' : ℝ) / 2) t + B * lawChr X.β ((a : ℝ) / 2) t) :
    ∃ fa fb, Split2 W₁ H' X f fa fb := by
  classical
  by_cases hP : ∃ (μ₀ : Measure (unip σ W H')) (𝓕₀ : Set (unip σ W H')), μ₀.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕₀ μ₀ ∧ μ₀ 𝓕₀ = 1
  · obtain ⟨μ₀, 𝓕₀, h1, h2, h3⟩ := hP
    have hc := huniq μ₀ 𝓕₀ h1 h2 h3
    choose A B key using hexp μ₀ 𝓕₀ h1 h2 h3
    have hsum : (fun h => ∫ u in 𝓕₀, f (u.1 * h) ∂μ₀) = A + B := funext fun h => by
      have := key h 1 1 (isLevi_one H')
      simp only [one_mul, lawChr_one, mul_one] at this
      simpa using this
    obtain ⟨t₀, ht₀⟩ := hbig
    have hne : ∃ t, lawChr X.α ((a' : ℝ) / 2) t ≠ lawChr X.β ((a : ℝ) / 2) t := by
      refine ⟨t₀, lawChr_ne _ _ ?_ ht₀⟩
      have : (a' : ℝ) < a := by exact_mod_cast hlt
      linarith
    have law : ∀ s m, IsLevi (W₁ := W₁) H' s 1 m → ∀ h,
        A (m * h) = lawChr X.α ((a' : ℝ) / 2) s * A h ∧ B (m * h) = lawChr X.β ((a : ℝ) / 2) s * B h := by
      intro s m hm h
      have hind := indep (lawChr_one _ _) (lawChr_one _ _) hne
        (P := A (m * h) - lawChr X.α ((a' : ℝ) / 2) s * A h) (Q := B (m * h) - lawChr X.β ((a : ℝ) / 2) s * B h)
        (fun t => by
          obtain ⟨mt, hmt⟩ := hlevi t
          have e1 := key (m * h) t mt hmt
          have e2 := key h (t * s) (mt * m) (isLevi_mul hmt hm)
          rw [show mt * m * h = mt * (m * h) from mul_assoc _ _ _] at e2
          rw [e2, lawChr_mul, lawChr_mul] at e1
          linear_combination (-1 : ℂ) * e1)
      exact ⟨sub_eq_zero.1 hind.1, sub_eq_zero.1 hind.2⟩
    refine ⟨A, B, ?_, fun s m hm h => (law s m hm h).1, fun s m hm h => (law s m hm h).2⟩
    rw [← hsum]
    exact hc
  · exact ⟨0, 0, fun μ 𝓕 h1 h2 h3 => (hP ⟨μ, 𝓕, h1, h2, h3⟩).elim, fun _ _ _ _ => by simp,
      fun _ _ _ _ => by simp⟩

theorem two_of_fin {T M : Type} (L : T → M → Prop) (v : M → ℂ) (χ₁ χ₂ : T → ℂ) {N K : ℕ} (χ : Fin N → T → ℂ)
    (c : Fin N → Fin (K + 1) → ℂ) (lg : T → ℂ)
    (hexp : ∀ t m, L t m → v m = ∑ i, ∑ k, c i k * χ i t * lg t ^ (k : ℕ))
    (htyp : ∀ i k, c i k ≠ 0 → (k : ℕ) = 0 ∧ ((∀ t, χ i t = χ₁ t) ∨ (∀ t, χ i t = χ₂ t))) :
    ∃ A B : ℂ, ∀ t m, L t m → v m = A * χ₁ t + B * χ₂ t := by
  classical
  let p : Fin N → Prop := fun i => ∀ t, χ i t = χ₁ t
  refine ⟨∑ i ∈ Finset.univ.filter p, c i 0, ∑ i ∈ Finset.univ.filter (fun i => ¬ p i), c i 0, fun t m hm => ?_⟩
  rw [hexp t m hm]
  have hk : ∀ i, ∑ k, c i k * χ i t * lg t ^ (k : ℕ) = c i 0 * χ i t := fun i => by
    have hz : ∀ k : Fin K, c i k.succ = 0 := fun k => by
      by_contra h
      have := (htyp i k.succ h).1
      simp at this
    rw [Fin.sum_univ_succ]
    simp [hz]
  simp only [hk]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p, Finset.sum_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2 t]
  · refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h0 : c i 0 = 0
    · simp [h0]
    rcases (htyp i 0 h0).2 with h | h
    · exact absurd h (Finset.mem_filter.1 hi).2
    · rw [h t]

theorem splitEx_exists : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d₁) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → (∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ fa fb, GlobalTheory.ThK.Split2 W₁ H' X (G.M.I om Φ) fa fb) ∧ ∀ Φ' ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ fa fb, GlobalTheory.ThK.Split2 W₁ H' X (G.M'.I om' Φ') fa fb := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA
  have hlevi := GlobalTheory.T.exists_levi_element_adapted F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA
  have hbig := GlobalTheory.T.exists_idele_abs_gt_one F E
  have hu := GlobalTheory.T.constant_term_unipotent_integral F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA
  have hr := GlobalTheory.T.theta_lift_left_invariant hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA
  have hf := GlobalTheory.T.constant_term_fundamental_domain hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA
  have ht := GlobalTheory.T.constant_term_haar_vanish hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA
  refine ⟨fun Φ hΦ => split2_of hlevi hbig hT.geo.lt (fun μ₀ 𝓕₀ h1 h2 h3 => hu _ (hr.1 Φ hΦ) μ₀ 𝓕₀ h1 h2 h3)
    (fun μ 𝓕 h1 h2 h3 h => ?_), fun Φ hΦ => split2_of hlevi hbig hT.geo.lt
    (fun μ₀ 𝓕₀ h1 h2 h3 => hu _ (hr.2 Φ hΦ) μ₀ 𝓕₀ h1 h2 h3) (fun μ 𝓕 h1 h2 h3 h => ?_)⟩
  · obtain ⟨N, K, χ, c, hχ, he⟩ := hf.1 Φ hΦ μ 𝓕 h1 h2 h3 h
    exact two_of_fin _ _ _ _ (fun i t => ((χ i t : ℂˣ) : ℂ)) c _ he (ht.1 Φ hΦ μ 𝓕 h1 h2 h3 h N K χ c hχ he)
  · obtain ⟨N, K, χ, c, hχ, he⟩ := hf.2 Φ hΦ μ 𝓕 h1 h2 h3 h
    exact two_of_fin _ _ _ _ (fun i t => ((χ i t : ℂˣ) : ℂ)) c _ he (ht.2 Φ hΦ μ 𝓕 h1 h2 h3 h N K χ c hχ he)

end GlobalTheory.ThKSplitEx
