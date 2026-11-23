import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwichStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRationalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMatrixCoeffIsotropicEqMulMeanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslationStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem meanX_prod_zero_eq : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F₁ F₁' F₂ F₂' : WO V W → ℂ, IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₁' → IsThetaFunO ψ V W F₂ → IsThetaFunO ψ V W F₂' → (∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₁ u * star (F₁' u) ∂ν) ∂μ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₂ u * star (F₂' u) ∂ν) ∂μ) → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁' 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂' 0) := by
  intro D V W a b P Q hP hQ hiso ψ hψ μ 𝓨 hμ F₁ F₁' F₂ F₂' h₁ h₁' h₂ h₂' H
  obtain ⟨k, B, horth, hdec, huniq, hrat, hsep⟩ := GlobalTheory.T.exists_rational_complement_isotropic_sandwich D V W a b P Q hP hQ hiso ψ hψ
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  obtain ⟨η, 𝓩, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D 1 k
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V.rank
  have hμ' : IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 := hμ
  have hν2 : IsAddFundamentalDomain (ratL W V) 𝓕 ν := hν.2.1
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.integral_matrixCoeff_isotropic_eq_mul_mean D V W a b P Q hP hQ hiso k B horth hdec huniq hrat ψ hψ μ 𝓨 hμ' η 𝓩 hη.1 hη.2.1 ν 𝓕
    hν.1 hν2 (GlobalTheory.T.integrable_thetaMatrixCoeff_isotropic_rational D V W a b P Q hP hQ hiso ψ hψ μ hμ.1 ν 𝓕 hν.1 hν2)
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  set ι := GlobalTheory.IsoMean.cplx V W B with hι
  have hιrat : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ι c ∈ ratL W V := by
    rintro _ ⟨c, rfl⟩
    exact ⟨_, (GlobalTheory.IsoMean.cplx_rat V W B c).symm⟩
  have hT := @GlobalTheory.ThetaClosed.isThetaFunO_heisO_all D ψ hψ V W

  have hcomp : ∀ (w ξ : WO V W), symplOH V W ξ w = 0 → ∀ G : WO V W → ℂ,
      heisO ψ V W (w + ξ) G = heisO ψ V W ξ (heisO ψ V W w G) := by
    intro w ξ h G
    funext u
    simp only [heisO]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, l2, l1, h, add_zero, add_comm (symplOH V W u w),
      show u + ξ + w = u + (w + ξ) by abel]

  have hcoef : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∫ y, (∫ u in 𝓕, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) ∂μ =
        κ * ∫ z in 𝓩, ψ (symplO V W (ι z) (ι c)) *
          (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z))) ∂η := by
    intro c hc G G' hG hG'
    have e1 : ∀ y, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G =
        heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) (heisO ψ V W (ι c) G) := fun y =>
      hcomp _ _ (by rw [skew, hH0 _ _ (horth c y), neg_zero]) G
    simp only [e1]
    rw [hU _ G' (hT hG (ι c)) hG']
    congr 1
    congr 1
    funext z
    rw [GlobalTheory.IsoMean.meanX_heisO_rat V W P Q μ 𝓨 ψ G hG (ι c) (hιrat c hc) (horth c) (ι z) (horth z)]
    ring
  set g : (WO V W → ℂ) → (WO V W → ℂ) → Mx D 1 k → ℂ := fun G G' z =>
    GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z)) with hg
  have hιc : Continuous ι := GlobalTheory.IsoMean.continuous_cplx V W B
  have hgc : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (g G G') :=
    fun G G' hG hG' => ((GlobalTheory.T.continuous_isotropicSandwichMean_translation D V W a b P Q ψ hψ μ 𝓨 hμ' G hG).comp hιc).mul
      ((GlobalTheory.T.continuous_isotropicSandwichMean_translation D V W a b P Q ψ hψ μ 𝓨 hμ' G' hG').comp hιc).star
  have hgp : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ z, g G G' (γ + z) = g G G' z := by
    intro G G' hG hG' γ hγ z
    simp only [hg]
    rw [show ι (γ + z) = ι γ + ι z from GlobalTheory.IsoMean.cplx_add V W B γ z]
    exact GlobalTheory.IsoMean.meanX_mul_star_rat V W P Q μ 𝓨 ψ hψ G G' hG hG' (ι γ) (hιrat γ hγ) (horth γ) (ι z)
  have hχ1 : ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (ι γ) (ι c)) = 1 :=
    fun γ hγ => (hsep γ).2 hγ
  have hchar : ∀ c z z', ψ (symplO V W (ι (z + z')) (ι c)) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z') (ι c)) := by
    intro c z z'
    rw [show ι (z + z') = ι z + ι z' from GlobalTheory.IsoMean.cplx_add V W B z z', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l1, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hchar2 : ∀ c c' z, ψ (symplO V W (ι z) (ι (c + c'))) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z) (ι c')) := by
    intro c c' z
    rw [show ι (c + c') = ι c + ι c' from GlobalTheory.IsoMean.cplx_add V W B c c', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l2, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hχc : ∀ c, Continuous fun z => ψ (symplO V W (ι z) (ι c)) := by
    intro c
    have h := (GlobalTheory.FinTranslate.continuous_symplOH V W (ι c)).comp hιc
    have e : (fun z => ψ (symplO V W (ι z) (ι c))) = fun z => ψ (symplOH V W (ι z) (ι c) + symplOH V W (ι z) (ι c)) := by
      funext z; rw [GlobalTheory.IsoMean.symplO_eq_add]
    rw [e]
    exact hψ.1.1.comp (h.add h)
  have hint : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      IntegrableOn (fun z => ψ (symplO V W (ι z) (ι c)) * g G G' z) 𝓩 η := by
    intro c hc G G' hG hG'
    refine GlobalTheory.MixModel.covolOne_integrableOn hη _ ((hχc c).mul (hgc G G' hG hG')) fun γ hγ z => ?_
    rw [hchar, hχ1 γ hγ c hc, one_mul, hgp G G' hG hG' γ hγ z]
  have key := GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero (Mx D 1 k) (GlobalTheory.MixModel.ratMx D 1 k) K hK hKc (GlobalTheory.MixModel.ratMx D 1 k)
    (fun c z => ψ (symplO V W (ι z) (ι c))) (fun c => hχc c) (fun c z z' => hchar c z z')
    (fun c c' z => by exact hchar2 c c' z)
    (fun z => by
      show ψ (symplO V W (ι z) (ι 0)) = 1
      have h0 : symplOH V W (ι z) 0 = 0 := by
        have h := l2 (ι z) 0 0
        rw [add_zero] at h
        linear_combination -h
      rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B, GlobalTheory.IsoMean.symplO_eq_add, h0, add_zero,
        AddChar.map_zero_eq_one])
    (fun c z => hψ.1.2.1 _)
    (fun z => by rw [← hsep z]; exact Subtype.forall)
    η 𝓩 hη.1 hη.2.1 (fun z => g F₁ F₁' z - g F₂ F₂' z) ((hgc F₁ F₁' h₁ h₁').sub (hgc F₂ F₂' h₂ h₂'))
    (fun γ hγ z => by simp only [hgp F₁ F₁' h₁ h₁' γ hγ z, hgp F₂ F₂' h₂ h₂' γ hγ z])
    (fun c => by
      have e1 := hcoef c c.2 F₁ F₁' h₁ h₁'
      have e2 := hcoef c c.2 F₂ F₂' h₂ h₂'
      have e3 := H ν 𝓕 hν.1 hν2 (ι c) (horth c)
      rw [e1, e2] at e3
      have e4 := mul_left_cancel₀ hκ e3
      simp only [mul_sub]
      rw [integral_sub (hint c c.2 F₁ F₁' h₁ h₁') (hint c c.2 F₂ F₂' h₂ h₂')]
      exact sub_eq_zero.2 e4)
  have e := congrFun key 0
  simp only [Pi.zero_apply, hg] at e
  rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B] at e
  exact sub_eq_zero.1 e

end GlobalTheory.IsoMean

end
