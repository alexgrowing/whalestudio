import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTransformEqOrientedThetaFunctionCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpaStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem psi_cancel [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (A C : AF F) (D : ℂ) :
    ψ (⅟2 * -A) * (ψ (C + ⅟2 * A) * D) = D * ψ C := by
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, show ⅟(2 : AF F) * -A + (C + ⅟2 * A) = C by ring]
  ring

theorem lam_formula {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (hβc : Continuous β) (hβs : Continuous β.symm)
    (hr1 : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = GlobalTheory.SWQ.rat y)
    (hr2 : ∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = GlobalTheory.SWQ.rat y) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F (Fin N), ∀ v : WOF F E nS nT,
      GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
        (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)) =
        c * Φ (α v) := by
  classical
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
  haveI hBor : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable E := GlobalTheory.ThetaParsevalInner.countable_numberField E
  haveI : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F
  haveI : Countable (ratLF F E nS nT) := by
    refine Function.Surjective.countable
      (f := fun m : Fin nT → Fin nS → E => (⟨(incAF F E).toAddMonoidHom.mapMatrix (Matrix.of m),
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : ratLF F E nS nT)) ?_
    rintro ⟨r, m, rfl⟩
    exact ⟨m, rfl⟩
  obtain ⟨Nn, hNn⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).2
    (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
  obtain ⟨h0, htop, -, -⟩ := hNn ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.mpr htop
  haveI := hν
  have hstd := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hstd.1
  refine ⟨((ν 𝓕).toReal : ℂ), ?_, fun Φ hΦ v => ?_⟩
  · exact_mod_cast (ENNReal.toReal_pos h0 htop).ne'
  set x : Fin N → AF F := α v with hx
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin N → F) → (Fin N → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (Fin N → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨ch, hch⟩ : ∃ ch : (Fin N → F) → WOF F E nS nT → ℂ, ch = fun ξ u => B.ψ (emb ξ ⬝ᵥ β u) := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have hch_norm : ∀ ξ u, ‖ch ξ u‖ = 1 := fun ξ u => by rw [hch]; exact hnorm _
  have hch_cont : ∀ ξ, Continuous (ch ξ) := fun ξ => by
    rw [hch]; exact hcont.comp (continuous_const.dotProduct hβc)

  have hint : ∀ u : WOF F E nS nT,
      heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)
        (dC (AF F ⊗[F] E) nT * u) = ∑' ξ, a ξ * ch ξ u := by
    intro u
    have h1 : e (dC (AF F ⊗[F] E) nT * u) = (0, β u) := by
      have := hCe u 0
      rwa [Matrix.mul_zero, add_zero, map_zero] at this
    have h2 : e (dCd F JT * v) = (α v, 0) := by
      have := hCe 0 v
      rwa [Matrix.mul_zero, zero_add, map_zero] at this
    simp only [heisOF, symplOHF, Function.comp_apply, he, h1, h2, hCe, GlobalTheory.ThetaOntoF.algebraMap_half]
    unfold thV GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
    rw [← tsum_mul_left]
    congr 1
    funext ξ
    subst ha hch hemb
    simp only [symV, dotProduct_zero, zero_dotProduct, zero_sub]
    exact psi_cancel B.ψ _ _ _
  have hFint : ∀ ξ, Integrable (fun u => a ξ * ch ξ u) (ν.restrict 𝓕) := fun ξ =>
    (Integrable.of_bound (hch_cont _).aestronglyMeasurable 1 (ae_of_all _ fun u => (hch_norm _ _).le)).const_mul _
  have hnormint : ∀ ξ, ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν = ‖a ξ‖ * ν.real 𝓕 := by
    intro ξ
    simp only [norm_mul, hch_norm, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun ξ => ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν := by
    simp_rw [hnormint]
    exact hsum.mul_right _
  have horth : ∀ ζ : Fin N → F, ∫ u in 𝓕, ch ζ u ∂ν = if ζ = 0 then (ν.real 𝓕 : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ u, ch 0 u = 1 := fun u => by simp [hch, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push Not at h; exact hζ (funext h)
      refine GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist ν (ratLF F E nS nT) h𝓕 (h := ch ζ) ?_
        (c := β.symm (Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0))) (a := B.ψ s0) ?_ hs0
      · intro r hr u
        obtain ⟨x₀, rfl⟩ := hr
        obtain ⟨η, hη⟩ := hr1 x₀
        have hr' : β ((incAF F E).toAddMonoidHom.mapMatrix x₀) = GlobalTheory.SWQ.rat η := hη
        simp only [hch, map_add, hr', dotProduct_add, AddChar.map_add_eq_mul]
        rw [show emb ζ ⬝ᵥ GlobalTheory.SWQ.rat η = algebraMap F (AF F) (ζ ⬝ᵥ η) by
          subst hemb; simp [dotProduct, map_sum, map_mul, GlobalTheory.SWQ.rat], htriv, one_mul]
      · intro u
        simp only [hch, map_add, LinearEquiv.apply_symm_apply, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [hint]
  rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
  simp_rw [integral_const_mul, horth]
  rw [tsum_eq_single 0 (fun ξ hξ => by rw [if_neg hξ, mul_zero])]
  rw [if_pos rfl, ha, hemb]
  have hz : (fun i : Fin N => (0 : AF F)) + x = x := by funext i; simp
  simp only [Pi.zero_apply, map_zero]
  rw [hz, Measure.real]
  ring

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
