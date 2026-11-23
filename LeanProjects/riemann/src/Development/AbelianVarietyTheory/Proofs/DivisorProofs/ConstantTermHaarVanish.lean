import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAbsGtOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviIdeleHomExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralsContinuousAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermPolynomialDatumFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermPolynomialDatumSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPolynomialCoefficientsInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesAboveAndNontrivialAbsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedAtGoodPlacesStatement

noncomputable section

namespace GlobalTheory.CtTyp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem typ_of_local {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {d₁ : ℕ} {W₁ : Spc F E d₁}
    {H' : Plane E (a + a') d₁} (mt : (AE F E)ˣ →* UA σ G.W.J) (hmc : ∀ g, Continuous fun t => mt t * g)
    (hml : ∀ t, IsLevi (W₁ := W₁) H' t 1 (mt t))
    (hmr : ∀ x : Eˣ, mt (Units.map (inclR (F := F) (AF F)).toMonoidHom x) ∈ ratU σ G.W.J)
    (hmn : ∀ t, ∀ u ∈ unip σ G.W H', mt t * u * (mt t)⁻¹ ∈ unip σ G.W H')
    (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')) (f : UA σ G.W.J → ℂ)
    (hB : ∀ γ ∈ ratU σ G.W.J, (∀ u ∈ unip σ G.W H', γ * u * γ⁻¹ ∈ unip σ G.W H' ∧ γ⁻¹ * u * γ ∈ unip σ G.W H') →
      ∀ g, ctf H' μ 𝓕 f (γ * g) = ctf H' μ 𝓕 f g)
    (hC : Continuous (ctf H' μ 𝓕 f))
    (hD : ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ g : UA σ G.W.J, ∃ p q : ℂ,
      ∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m →
        ctf H' μ 𝓕 f (m * g) = p * ((twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) +
          q * ((twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ))
    (hv : ∃ v, X.Good v)
    (hP : (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), ∃ x : (w.adicCompletion E)ˣ, absE F E (locIdele F w x) ≠ 1)
    (hA : ∀ (T : Type) [CommGroup T] (L : T → ℝ), (∀ x y, L (x * y) = L x + L y) → (∃ t, L t ≠ 0) →
      ∀ (N K : ℕ) (χ : Fin N → T →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ → ∀ Φ : T → ℂ,
      (∀ t, Φ t = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((L t : ℝ) : ℂ) ^ (k : ℕ)) →
      (∀ γ, L γ = 0 → (∀ t, Φ (γ * t) = Φ t) → ∀ i k, c i k ≠ 0 → χ i γ = 1) ∧
      (∀ i k, c i k ≠ 0 → ∃ (n : ℕ) (s : Fin n → T) (b : Fin n → ℂ), ∀ t, ((χ i t : ℂˣ) : ℂ) = ∑ j, b j * Φ (s j * t)) ∧
      ∀ (H : Subgroup T) (ψ₁ ψ₂ : T →* ℂˣ), (∃ x ∈ H, L x ≠ 0) →
        (∀ s, ∃ p q : ℂ, ∀ x ∈ H, Φ (x * s) = p * ((ψ₁ x : ℂˣ) : ℂ) + q * ((ψ₂ x : ℂˣ) : ℂ)) →
        ∀ i k, c i k ≠ 0 → (k : ℕ) = 0 ∧ ((∀ x ∈ H, χ i x = ψ₁ x) ∨ ∀ x ∈ H, χ i x = ψ₂ x))
    (hG : ∀ χ : (AE F E)ˣ →* ℂˣ, Continuous (fun t => ((χ t : ℂˣ) : ℂ)) →
      (∀ x : Eˣ, χ (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1) →
      (∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
        (∀ x, χ (locIdele F w x) = twAbs X.α ((a' : ℝ) / 2) (locIdele F w x)) ∨
          ∀ x, χ (locIdele F w x) = twAbs X.β ((a : ℝ) / 2) (locIdele F w x)) →
      χ = twAbs X.α ((a' : ℝ) / 2) ∨ χ = twAbs X.β ((a : ℝ) / 2))
    (h : UA σ G.W.J) (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ) (hinj : Function.Injective χ)
    (hexp : ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m →
      ∫ u in 𝓕, f (u.1 * (m * h)) ∂μ = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ)) :
    ∀ i k, c i k ≠ 0 → (k : ℕ) = 0 ∧ ((∀ t, ((χ i t : ℂˣ) : ℂ) = (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) ∨
      (∀ t, ((χ i t : ℂˣ) : ℂ) = (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ))) := by
  intro i k hik
  let L : (AE F E)ˣ → ℝ := fun t => Real.log (absE F E t : ℝ)
  have hL0 : ∃ t, L t ≠ 0 := by
    obtain ⟨t, ht⟩ := GlobalTheory.DivAbsBig.exists_idele_absE_gt_one F E
    exact ⟨t, (Real.log_pos ht).ne'⟩
  let Φf : (AE F E)ˣ → ℂ := fun t => ctf H' μ 𝓕 f (mt t * h)
  have hΦ : ∀ t, Φf t = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((L t : ℝ) : ℂ) ^ (k : ℕ) := fun t => hexp t (mt t) (hml t)
  obtain ⟨Etr, Ecn, Eloc⟩ := hA _ L log_absE_mul hL0 N K χ c hinj Φf hΦ
  have hloc : ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → (k : ℕ) = 0 ∧
      ((∀ x ∈ (locIdele F w).range, χ i x = twAbs X.α ((a' : ℝ) / 2) x) ∨
        ∀ x ∈ (locIdele F w).range, χ i x = twAbs X.β ((a : ℝ) / 2) x) := by
    intro v hv w hw
    refine Eloc (locIdele F w).range _ _ ?_ ?_ i k hik
    · obtain ⟨x, hx⟩ := hP.2 w
      exact ⟨locIdele F w x, ⟨x, rfl⟩, fun h0 => hx (log_absE_eq_zero.1 h0)⟩
    · intro s
      obtain ⟨p, q, hpq⟩ := hD v hv w hw (mt s * h)
      refine ⟨p, q, ?_⟩
      rintro _ ⟨x, rfl⟩
      have := hpq x _ (hml (locIdele F w x))
      simp only [Φf, map_mul, mul_assoc]
      exact this
  obtain ⟨v, hv⟩ := hv
  obtain ⟨w, hw⟩ := hP.1 v
  refine ⟨(hloc v hv w hw).1, ?_⟩
  have htriv : ∀ x : Eˣ, χ i (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1 := by
    intro x
    refine Etr _ ?_ ?_ i k hik
    · show Real.log (absE F E _ : ℝ) = 0
      rw [GlobalTheory.Doubling.absE_inclR]; simp
    · intro t
      have hn : ∀ u ∈ unip σ G.W H', mt (Units.map (inclR (F := F) (AF F)).toMonoidHom x) * u *
          (mt (Units.map (inclR (F := F) (AF F)).toMonoidHom x))⁻¹ ∈ unip σ G.W H' ∧
          (mt (Units.map (inclR (F := F) (AF F)).toMonoidHom x))⁻¹ * u *
            mt (Units.map (inclR (F := F) (AF F)).toMonoidHom x) ∈ unip σ G.W H' := fun u hu => by
        refine ⟨hmn _ u hu, ?_⟩
        have := hmn (Units.map (inclR (F := F) (AF F)).toMonoidHom x)⁻¹ u hu
        rwa [map_inv, inv_inv] at this
      simp only [Φf, map_mul, mul_assoc]
      exact hB _ (hmr x) hn _
  have hcont : Continuous fun t => ((χ i t : ℂˣ) : ℂ) := by
    obtain ⟨n, s, b, hb⟩ := Ecn i k hik
    rw [show (fun t => ((χ i t : ℂˣ) : ℂ)) = fun t => ∑ j, b j * Φf (s j * t) from funext hb]
    refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
    have e : (fun t => Φf (s j * t)) = fun t => ctf H' μ 𝓕 f (mt t * (mt (s j) * h)) := funext fun t => by
      simp only [Φf]; rw [mul_comm (s j) t, map_mul, mul_assoc]
    rw [e]
    exact hC.comp (hmc _)
  have hlocal : ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
      (∀ x, χ i (locIdele F w x) = twAbs X.α ((a' : ℝ) / 2) (locIdele F w x)) ∨
        ∀ x, χ i (locIdele F w x) = twAbs X.β ((a : ℝ) / 2) (locIdele F w x) := by
    intro v hv w hw
    rcases (hloc v hv w hw).2 with e | e
    · exact Or.inl fun x => e _ ⟨x, rfl⟩
    · exact Or.inr fun x => e _ ⟨x, rfl⟩
  rcases hG (χ i) hcont htriv hlocal with e | e
  · exact Or.inl fun t => by rw [e, coe_twAbs]
  · exact Or.inr fun t => by rw [e, coe_twAbs]

theorem typ : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → (∀ Φ ∈ PolData B G.M, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, ∀ (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ → (∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m → ∫ u in 𝓕, G.M.I om Φ (u.1 * (m * h)) ∂μ = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ)) → ∀ i k, c i k ≠ 0 → (k : ℕ) = 0 ∧ ((∀ t, ((χ i t : ℂˣ) : ℂ) = (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) ∨ (∀ t, ((χ i t : ℂˣ) : ℂ) = (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)))) ∧ ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, ∀ (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ → (∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m → ∫ u in 𝓕, G.M'.I om' Φ' (u.1 * (m * h)) ∂μ = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ)) → ∀ i k, c i k ≠ 0 → (k : ℕ) = 0 ∧ ((∀ t, ((χ i t : ℂˣ) : ℂ) = (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) ∨ (∀ t, ((χ i t : ℂˣ) : ℂ) = (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ))) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  obtain ⟨mt, hmc, hml, hmr, hmn⟩ := GlobalTheory.T.continuous_levi_idele_hom_exists F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  obtain ⟨hth, hth'⟩ := GlobalTheory.T.theta_integrals_continuous_automorphic hKP F E σ B a a' G X om om' hT
  have hv : ∃ v, X.Good v := ⟨B.v₁, hT.chars.good⟩
  have hP := GlobalTheory.T.places_above_and_nontrivial_abs F E
  have hG := GlobalTheory.T.hecke_character_unramified_at_good_places hKP F E σ B a a' G X om om' hT
  refine ⟨fun Φ hΦ μ 𝓕 hμ h𝓕 h1 h N K χ c hinj hexp => ?_, fun Φ' hΦ' μ 𝓕 hμ h𝓕 h1 h N K χ c hinj hexp => ?_⟩
  · exact typ_of_local mt hmc hml hmr hmn μ 𝓕 _
      (GlobalTheory.T.constant_term_unipotent_integral_alt F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH _ (hth Φ hΦ).1 (hth Φ hΦ).2 μ 𝓕 hμ h𝓕 h1)
      (GlobalTheory.T.constant_term_unipotent_integral_bound F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH _ (hth Φ hΦ).1 (hth Φ hΦ).2 μ 𝓕 hμ h𝓕 h1)
      (GlobalTheory.T.constant_term_polynomial_datum_first hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH Φ hΦ μ 𝓕 hμ h𝓕 h1)
      hv hP GlobalTheory.T.character_polynomial_coefficients_invariant hG h N K χ c hinj hexp
  · exact typ_of_local mt hmc hml hmr hmn μ 𝓕 _
      (GlobalTheory.T.constant_term_unipotent_integral_alt F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH _ (hth' Φ' hΦ').1 (hth' Φ' hΦ').2 μ 𝓕 hμ h𝓕 h1)
      (GlobalTheory.T.constant_term_unipotent_integral_bound F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH _ (hth' Φ' hΦ').1 (hth' Φ' hΦ').2 μ 𝓕 hμ h𝓕 h1)
      (GlobalTheory.T.constant_term_polynomial_datum_second hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH Φ' hΦ' μ 𝓕 hμ h𝓕 h1)
      hv hP GlobalTheory.T.character_polynomial_coefficients_invariant hG h N K χ c hinj hexp

end GlobalTheory.CtTyp
