import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ThTot
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.ThTot.OneRow

variable {D : D7}

theorem evalPoly_temperate {m n : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth
      (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (z τ))) := by
  have coord : ∀ k : D.what₂.Tau × Fin m × Fin n × Bool, Function.HasTemperateGrowth
      (fun z : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1) := by
    rintro ⟨τ, i, j, b⟩
    let L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))
    cases b
    · exact L.hasTemperateGrowth
    · exact (Complex.conjCLE.toContinuousLinearMap.comp L).hasTemperateGrowth
  induction p using MvPolynomial.induction_on with
  | C a => simpa [evalPoly] using Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) + fun z => evalPoly q (fun τ => Matrix.of (z τ)) := by
      funext z; simp [evalPoly]
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X k) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) * fun z =>
          if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1 := by
      funext z; simp [evalPoly]
    rw [this]; exact hp.mul (coord k)

theorem exists_schwartz_poly_gauss (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ))
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) :
    ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z,
      f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  refine ⟨SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ (fun z : D.what₂.Tau → Fin V.rank → Fin n → ℂ =>
    evalPoly p (fun τ => Matrix.of (z τ))) f, fun z => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evalPoly_temperate p)]
  simp [hf]

theorem fockA_le_schwartzA (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    fockA θ V n l s ≤ schwartzA θ V.rank n := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  obtain ⟨f, hf⟩ := exists_schwartz_poly_gauss n V l hl s hs p
  refine Submodule.subset_span ⟨f, g, hg, ?_⟩
  funext x
  rw [hf]
  rfl

theorem gram_rank_one_one : (V1 D).gram = 1 := by
  refine Matrix.ext fun (i j : Fin 1) => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  show ∑ k : Fin 1, star ((Pi.basisFun D.host.E (Fin 1)) 0 k) * Formalism.BasicNotions.Examples₂.sgn false * (Pi.basisFun D.host.E (Fin 1)) 0 k =
    (1 : Matrix (Fin 1) (Fin 1) D.host.E) 0 0
  simp [Formalism.BasicNotions.Examples₂.sgn]

theorem gram_at_place_rank_one (τ : D.what₂.Tau) : gramAt D (V1 D) τ = 1 := by
  unfold gramAt
  rw [gram_rank_one_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cartan_involution_rank_one (τ : D.what₂.Tau) : IsCartanInv (gramAt D (V1 D) τ) 1 := by
  rw [gram_at_place_rank_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one]
  exact Matrix.PosDef.one

theorem gram_rank_one_eq_one : gA (V1 D) = (1 : Mx D (V1 D).rank (V1 D).rank) := by
  unfold gA rat
  rw [gram_rank_one_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

set_option synthInstance.maxHeartbeats 400000 in
theorem incA_algebraMap (c : D.host.F) :
    incA D (algebraMap D.host.F D.host.E c) = (algebraMap D.host.F (AF D.host.F) c) • (1 : AE D) := by
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c) =
    (algebraMap D.host.F (AF D.host.F) c) • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E))
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem pr_eq {p : ℕ} (b₀ : HermE D 1) (c : D.host.F) (hc : algebraMap D.host.F D.host.E c = b₀.1 0 0)
    (x y : Mx D 1 p) :
    pr b₀ x y = (algebraMap D.host.F (AF D.host.F) c) • (inner (V1 D) x y : Mx D p p) := by
  have h1 : b₀.1.map (incA D) = (algebraMap D.host.F (AF D.host.F) c) • (1 : Mx D 1 1) := by
    refine Matrix.ext fun (i j : Fin 1) => ?_
    fin_cases i; fin_cases j
    simp [← hc, incA_algebraMap]
  have h2 : (inner (V1 D) x y : Mx D p p) = HMul.hMul (adj x) y := by
    unfold GlobalTheory.StdUnn.inner
    rw [gram_rank_one_eq_one]
    exact congrArg (fun t : Mx D 1 p => (HMul.hMul (adj x) t : Mx D p p)) (Matrix.one_mul y)
  rw [h2]
  unfold pr
  rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

theorem trA_smul (a : AF D.host.F) (z : AE D) : trA (a • z) = a * trA z := by
  simp [trA, map_smul]

theorem halfTr_smul (a : AF D.host.F) (z : AE D) : halfTr (a • z) = a * halfTr z := by
  simp only [halfTr, trA_smul]; ring

theorem exists_base (b₀ : HermE D 1) (h : b₀.1.det ≠ 0) :
    ∃ c : D.host.F, c ≠ 0 ∧ algebraMap D.host.F D.host.E c = b₀.1 0 0 := by
  have h0 : b₀.1 0 0 ≠ 0 := by simpa [Matrix.det_fin_one] using h
  have hfix : star (b₀.1 0 0) = b₀.1 0 0 := congrFun (congrFun b₀.2 0) 0
  have hF : b₀.1 0 0 ∈ D.host.F :=
    (NumberField.IsCMField.complexConj_eq_self_iff D.host.E _).1 hfix
  exact ⟨⟨_, hF⟩, fun e => h0 (by simpa using congrArg (fun u : D.host.F => (u : D.host.E)) e), rfl⟩

theorem exists_par (ψ₀ : AddChar (AF D.host.F) ℂ) (h₀ : IsStdChar D ψ₀ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (a : D.host.F) (ha : a ≠ 0) :
    IsCharAF D.host.F (shift ψ₀ a) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ₀ a) θ l ∧ ∀ τ, l τ ≠ 0 := by
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have haE : algebraMap D.host.F D.host.E a ≠ 0 := (map_ne_zero _).2 ha
  have hst : star (algebraMap D.host.F D.host.E a) = algebraMap D.host.F D.host.E a :=
    (NumberField.IsCMField.complexConj_eq_self_iff D.host.E _).2 a.2
  have hsk : IsSkew (-D.host.xi0 / algebraMap D.host.F D.host.E a) := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) haE, ?_⟩
    rw [star_div₀, star_neg, hst, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, neg_div]
  obtain ⟨lam, hlam, hc, l, hp, habs⟩ := shift_char_realPar D ψ₀ h₀ θ hθ _ hsk
  have : lam = a := by
    apply (algebraMap D.host.F D.host.E).injective
    rw [hlam]
    field_simp
  subst this
  refine ⟨hc, l, hp, fun τ h => ?_⟩
  have := habs τ
  rw [h, abs_zero] at this
  have h1 : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 hxi
  have h2 : tauE D τ (-D.host.xi0 / algebraMap D.host.F D.host.E lam) ≠ 0 := (map_ne_zero _).2 hsk.1
  exact (div_ne_zero (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)) this.symm

theorem oneTotal : WeilCont → FockTranslateSchwartzMajorant → FockTotal → OneTotal := by
  intro hC hM hF D p μ 𝓕 hμ ψ hψ b₀ hdet χ hχ hr θ hθ
  obtain ⟨c, hc0, hc⟩ := exists_base b₀ hdet
  obtain ⟨ψ₀, h₀, lam, hlam0, hlam⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hne : lam * c ≠ 0 := mul_ne_zero hlam0 hc0
  obtain ⟨hψ₁, l, hpar, hl⟩ := exists_par ψ₀ h₀ θ hθ (lam * c) hne
  have hs : ∀ t, shift ψ₀ (lam * c) t = ψ (algebraMap D.host.F (AF D.host.F) c * t) := by
    intro t
    rw [hlam]
    simp [shift, AddChar.mulShift_apply, map_mul, mul_assoc]
  obtain ⟨ω, hω⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D p (V1 D) ψ₀ h₀ (lam * c) hne χ hχ hr θ hθ μ 𝓕 hμ
  intro u huc hub hu
  refine hF D p θ hθ l hl μ 𝓕 hμ u huc hub fun φ hφ => ?_
  have hφS := fockA_le_schwartzA θ (V1 D) p l hl _ (fun τ => cartan_involution_rank_one τ) hφ
  let Φ : schwartzA θ (V1 D).rank p := ⟨φ, hφS⟩
  have e : ∀ g h : G D p, ω (g * h) Φ = ω g (ω h Φ) := fun g h => by rw [map_mul]; rfl
  have hT : IsTh ψ χ θ b₀ μ (fun h => (ω h Φ).1) :=
    { mem := fun h => (ω h Φ).2
      cont := hC D p (V1 D) _ hψ₁ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
      maj := hM D p _ hψ₁ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hpar hl Φ hφ
      levi := by
        intro g a hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e]
        exact hω.levi g a hg _ y
      unip := by
        intro g b hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e, hω.unip g b hg _ y, hs, pr_eq b₀ c hc, Matrix.mul_smul, Matrix.trace_smul, halfTr_smul]
      weyl := by
        intro g hg h x
        show (ω (g * h) Φ).1 x = _
        rw [e, hω.weyl g hg _ x]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show _ * shift ψ₀ (lam * c) _ = _ * ψ _
        rw [hs, pr_eq b₀ c hc x y, Matrix.trace_smul, trA_smul] }
  have h1 : ∫ y, u y * conj ((ω 1 Φ).1 y) ∂μ = 0 := hu _ hT
  have h2 : (ω 1 Φ).1 = φ := by rw [map_one]; rfl
  rw [h2] at h1
  exact h1

end GlobalTheory.CompanionTheory.ThTot.OneRow

end
