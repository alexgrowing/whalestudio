import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogCovolumeEqMeanClassGroup
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LogPiSubMeanLogLatticeNormDisc
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralDerivativeCurveHomGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieNormSqIffEqPiDivCovolume

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem exists_periodPair_image_ideal {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {σ : K →+* ℂ} (hσ : ¬ ComplexEmbedding.IsReal σ) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ a ∈ I, z = σ (a : K) := by
  have hr : Module.finrank ℤ I = 2 :=
    (Ideal.finrank_eq_finrank (RingOfIntegers.basis K) I hI).trans ((RingOfIntegers.rank K).trans hK)
  let b : Module.Basis (Fin 2) ℤ I := Module.finBasisOfFinrankEq ℤ _ hr
  have hs : ∀ x : I, σ ((x : 𝓞 K) : K) =
      b.repr x 0 * σ ((b 0 : 𝓞 K) : K) + b.repr x 1 * σ ((b 1 : 𝓞 K) : K) := by
    intro x
    have := congrArg (fun x : I => σ ((x : 𝓞 K) : K)) (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  obtain ⟨a, ha⟩ := CMLattice.exists_im_ne_zero σ hσ
  have hb0 : σ ((b 0 : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero]
    have : (b 0 : 𝓞 K) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    exact_mod_cast this
  have h0 : (σ ((b 1 : 𝓞 K) : K) * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im ≠ 0 := by
    intro h0
    have e := hs ⟨a * b 0, I.mul_mem_left a (b 0).2⟩
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e' h0 ha hb0
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨σ ((b 0 : 𝓞 K) : K), σ ((b 1 : 𝓞 K) : K), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 1 : 𝓞 K) : K)).im * e1 - (σ ((b 1 : 𝓞 K) : K)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 0 : 𝓞 K) : K)).re * e2 - (σ ((b 0 : 𝓞 K) : K)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, _, (hs ⟨x, hx⟩).symm⟩

theorem mean_log_lieNormSq_eq_mean_log_eta :
    ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) → (∃ β : ClassGroup (𝓞 K) → M, (∀ C, β C ≠ 0) ∧ (∀ a : 𝓞 K, (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![κ (a : K)] ![t₁] (v₁ ≫ f₁))) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ (Q C).A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) (Q C) Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ (t C) t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![β C * κ x] ![t₁] (v₁ ≫ f₁))) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ (Q C).A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) (Q C) P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ (t C) v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![(β C)⁻¹ * κ (y : K)] ![t₁] (v₁ ≫ f₁))) → ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → (∑ s, Real.log (n s)) / Module.finrank ℚ M = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  intro hU hB hN K _ _ hK σ₀ h₀ 𝔟 h𝔟 M _ κ P v L₀ Q t L δ ⟨_, ⟨hPg, hv, hvb, hPL⟩, hQ, hδ, _⟩
    ⟨β, hβ, hEnd, h1, h2⟩ n hn σ τ hτ
  let _ : Algebra K M := κ.toAlgebra
  have hvt : IsTangent v := hv.1 0
  have htt : ∀ C, IsTangent (t C) := fun C => (hQ C).2.1.1 0
  obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) M) P
  obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  choose Q₀ ψ hψ using fun C => exists_isPolFibre hB (algebraMap (𝓞 M) M) (Q C)
  choose t₀ ht₀ using fun C => (existsUnique_isVecOver (hψ C).2.1.1 (t C)).exists
  choose Lc hLc using fun C => exists_periodPair_image_ideal hK h₀ (nonZeroDivisors.coe_ne_zero (𝔟 C))
  have key := mean_log_covolume_eq_mean_classGroup K M hK σ₀ h₀ 𝔟 Lc h𝔟 hLc
    (fun s => L₀ (s.comp (algebraMap (𝓞 M) M))) (fun C s => L C (s.comp (algebraMap (𝓞 M) M))) δ β
    (fun s a => by
      obtain ⟨f, hf, hc⟩ := hEnd a P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ P P v v _ _ _ _ hPg hPg hvt hvt (hPL _) (hPL _)).2
        (hom_deriv_baseChange _ P P v v _ _ P₀ P₀ φ φ v₀ v₀ f _ hφ hφ hv₀ hv₀ hf hc ℂ s))
    (fun C s => hδ C _) hβ
    (fun C x hx => ⟨T.isIntegral_derivative_curve_hom_good_reduction hN hB M P (Q C) v (t C) _ hvt (hQ C).2.2.1 (h1 C x hx), fun s => by
      obtain ⟨f, hf, hc⟩ := h1 C x hx P₀ (Q₀ C) φ (ψ C) v₀ (t₀ C) hφ (hψ C) hv₀ (ht₀ C)
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ P (Q C) v (t C) _ _ _ _ hPg (hQ C).1 hvt (htt C) (hPL _) ((hQ C).2.2.2 _)).2
        (hom_deriv_baseChange _ P (Q C) v (t C) _ _ _ _ _ _ _ _ f _ hφ (hψ C) hv₀ (ht₀ C) hf hc ℂ s)⟩)
    (fun C y hy => ⟨T.isIntegral_derivative_curve_hom_good_reduction hN hB M (Q C) P (t C) v _ (htt C) hvb (h2 C y hy), fun s => by
      obtain ⟨f, hf, hc⟩ := h2 C y hy (Q₀ C) P₀ (ψ C) φ (t₀ C) v₀ (hψ C) hφ (ht₀ C) hv₀
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ (Q C) P (t C) v _ _ _ _ (hQ C).1 hPg (htt C) hvt ((hQ C).2.2.2 _) (hPL _)).2
        (hom_deriv_baseChange _ (Q C) P (t C) v _ _ _ _ _ _ _ _ f _ (hψ C) hφ (ht₀ C) hv₀ hf hc ℂ s)⟩)
  rw [← log_pi_sub_mean_log_latticeNormDisc K hK σ₀ h₀ 𝔟 Lc h𝔟 hLc σ τ hτ, ← key]
  have hlog : ∀ s : M →+* ℂ, Real.log (n s) = Real.log Real.pi -
      Real.log |((L₀ (s.comp (algebraMap (𝓞 M) M))).ω₁ *
        starRingEnd ℂ (L₀ (s.comp (algebraMap (𝓞 M) M))).ω₂).im| := by
    intro s
    obtain ⟨hp, hr⟩ := isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ _ hPg hvt (hPL (s.comp (algebraMap (𝓞 M) M)))
    rw [(hr _).1 (hn s), Real.log_div Real.pi_ne_zero]
    intro h
    rw [h, div_zero] at hp
    exact lt_irrefl _ hp
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  simp only [hlog, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
  field_simp

end GlobalTheory
