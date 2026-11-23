import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.TranslateCoefInversion

variable {D : D7} {S T : HSp D}

theorem symplOH_neg_left' (x y : WO S T) : symplOH S T (-x) y = -symplOH S T x y := by
  obtain ⟨hl, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have h := hl x (-x) y
  rw [add_neg_cancel, GlobalTheory.ThetaSquare.symplOH_zero_left] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem symplOH_skew' (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  obtain ⟨hl, hr, hs, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have h := hs (x + y)
  rw [hl, hr, hr, hs, hs, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem symplOH_neg_right' (x y : WO S T) : symplOH S T x (-y) = -symplOH S T x y := by
  rw [symplOH_skew', symplOH_neg_left', symplOH_skew' y x, neg_neg]

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  rw [GlobalTheory.ThetaAllChar.star_char hn, AddChar.inv_apply]

theorem chi_neg_neg (ψ : AddChar (AF D.host.F) ℂ) (γ x : WO S T) :
    GlobalTheory.ThetaAllChar.chi ψ S T (-γ) (-x) = GlobalTheory.ThetaAllChar.chi ψ S T γ x := by
  simp only [GlobalTheory.ThetaAllChar.chi, symplOH_neg_left', symplOH_neg_right', neg_neg]

theorem star_chi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (γ z : WO S T) :
    star (GlobalTheory.ThetaAllChar.chi ψ S T γ z) = GlobalTheory.ThetaAllChar.chi ψ S T (-γ) z := by
  simp only [GlobalTheory.ThetaAllChar.chi, star_psi hn, symplOH_neg_right', neg_add]

theorem rat_eq_zero_of_fin {x : WO S T} (hx : x ∈ ratL T S) (h0 : ∀ i j, finPart D (x i j) = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ := hx
  ext i j
  have h : (1 : Af D.host.F) ⊗ₜ[D.host.F] m i j = 0 := h0 i j
  haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    let v : HeightOneSpectrum (𝓞 D.host.F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion D.host.F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 D.host.F) D.host.F => x v) h
    exact zero_ne_one h2
  have e : m i j = 0 := by
    apply Algebra.TensorProduct.includeRight_injective (R := D.host.F) (A := Af D.host.F) (B := D.host.E)
      (algebraMap D.host.F (Af D.host.F)).injective
    rw [map_zero]
    exact h
  show incA D (m i j) = 0
  rw [e, map_zero]

theorem rat_eq_zero_of_inf {x : WO S T} (hx : x ∈ ratL T S) (h0 : ∀ i j, infPart D (x i j) = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ := hx
  ext i j
  have h : (1 : Ainf D.host.F) ⊗ₜ[D.host.F] m i j = 0 := h0 i j
  have e : m i j = 0 := by
    apply Algebra.TensorProduct.includeRight_injective (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)
      (algebraMap D.host.F (Ainf D.host.F)).injective
    rw [map_zero]
    exact h
  show incA D (m i j) = 0
  rw [e, map_zero]

open GlobalTheory.ThetaAllChar in

theorem chiR_eq_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (γ : ratL T S)
    (h : ∀ x, chiR ψ S T γ x = 1) : γ = 0 := by
  have hall : ∀ c : AF D.host.F, (c • (γ : WO S T)) ∈ ratL T S := by
    intro c
    refine (chi_ker hψ _).1 fun δ => ?_
    have h1 := h ((-c) • (δ : WO S T))
    simp only [chiR, chi, GlobalTheory.FinTranslate.symplOH_smul_left] at h1 ⊢
    rw [symplOH_skew' (δ : WO S T) (γ : WO S T), mul_neg, ← neg_mul]
    exact h1
  have h1 : GlobalTheory.FinTranslate.eInf D • (γ : WO S T) = 0 :=
    rat_eq_zero_of_fin (hall _) fun i j => GlobalTheory.ThetaClosed.finPart_eInf_smul _
  have h2 : (1 - GlobalTheory.FinTranslate.eInf D) • (γ : WO S T) = 0 :=
    rat_eq_zero_of_inf (hall _) fun i j => GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul _
  have h3 : (γ : WO S T) = 0 := by
    rw [← one_smul (AF D.host.F) (γ : WO S T), ← add_sub_cancel (GlobalTheory.FinTranslate.eInf D) 1, add_smul, h1, h2, add_zero]
  exact Subtype.ext h3

open GlobalTheory.ThetaAllChar in

theorem sum_coef_mul_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∀ w x : WO S T, Summable (fun γ : ratL T S => ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖) → ∑' γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x = f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x := by
  intro D ψ hψ S T μ 𝓕 hc f f₀ hf hf₀ w x hs
  obtain ⟨hμ, h𝓕, h1⟩ := hc
  haveI := hμ
  obtain ⟨iG1, iG2, iG3, iG4, iG5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  obtain ⟨lc, lx, la, l0, ln, lker⟩ := chiR_laws (S := S) (T := T) hψ.1
  set g := heisO ψ S T w f₀ with hgdef
  have hg : IsThetaFunO ψ S T g := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 w f₀ hf₀

  have hb : ∀ γ : ratL T S, heisO ψ S T ((γ : WO S T) + w) f₀ =
      fun y => ψ (-(symplOH S T γ w)) * (chi ψ S T γ y * g y) := by
    intro γ
    have e1 := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1 γ w f₀
    rw [heisO_rat γ.2 hg] at e1
    funext y
    have e2 := congrFun e1 y
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e2
    rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  set F : WO S T → ℂ := fun z => f z * star (g z) with hFdef
  have hFc : Continuous F := hf.cont.mul hg.cont.star
  have hFp : ∀ γ ∈ ratL T S, ∀ z, F (γ + z) = F z :=
    GlobalTheory.ThetaAllChar.periodic_of_one (GlobalTheory.ThetaAllChar.isTheta_mul_star hn hf hg)
  have hχp : ∀ (a : ratL T S), ∀ γ ∈ ratL T S, ∀ z, chiR ψ S T a (γ + z) = chiR ψ S T a z := fun a =>
    GlobalTheory.ThetaAllChar.periodic_of_one (GlobalTheory.ThetaAllChar.isTheta_chi hψ.1 a.2)
  set Φ : WO S T → ℂ := fun z => F (z + x) with hΦdef
  set I : ratL T S → ℂ := fun γ => ∫ z in 𝓕, chiR ψ S T (-γ) z * F z ∂μ with hIdef
  set J : ratL T S → ℂ := fun a => ∫ z in 𝓕, chiR ψ S T a z * Φ z ∂μ with hJdef
  have hcoef : ∀ γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) = ψ (symplOH S T γ w) * I γ := by
    intro γ
    rw [thPair, hb γ, hIdef, ← integral_const_mul]
    congr 1
    funext z
    simp only [chiR, AddSubgroup.coe_neg, hFdef]
    rw [star_mul, star_mul, star_psi hn, neg_neg, star_chi hn]
    ring
  have hJ : ∀ γ : ratL T S, J (-γ) = chi ψ S T γ x * I γ := by
    intro γ
    have e := GlobalTheory.CompactQuotientFourier.setIntegral_translate (ratL T S) μ 𝓕 h𝓕
      (fun z => chiR ψ S T (-γ) (z + -x) * F z)
      (fun γ' hγ' z => by simp only [add_assoc, hχp _ γ' hγ', hFp γ' hγ']) x
    simp only [add_neg_cancel_right] at e
    simp only [hJdef, hΦdef, hIdef]
    rw [e, ← integral_const_mul]
    congr 1
    funext z
    rw [lx, show chiR ψ S T (-γ) (-x) = chi ψ S T γ x by simp only [chiR, AddSubgroup.coe_neg]; exact chi_neg_neg ψ _ _]
    ring
  have hkey : ∀ γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x =
      g x * J (-γ) := by
    intro γ
    have hp1 : ψ (symplOH S T γ w) * ψ (-(symplOH S T γ w)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hcoef, hb γ, hJ]
    linear_combination (I γ * chi ψ S T γ x * g x) * hp1
  have hnorm : ∀ γ : ratL T S, ‖J (-γ)‖ = ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖ := by
    intro γ
    rw [hJ, hcoef, norm_mul, norm_mul, hn, GlobalTheory.ThetaAllChar.norm_chi hn]
  have hsJ : Summable J := by
    have h2 : Summable fun γ : ratL T S => J (-γ) := by
      refine Summable.of_norm ?_
      simp only [hnorm]
      exact hs
    exact (Equiv.neg (ratL T S)).summable_iff.1 h2
  have hinv := GlobalTheory.SeparatingCharacters.tsum_coefficients_eq_value_zero (WO S T) (ratL T S) K hK hcov
    (ratL T S) (chiR ψ S T) lc lx la l0 ln lker (fun a ha => chiR_eq_zero hψ.1 a ha) μ 𝓕 hμ h𝓕 h1 Φ
    (hFc.comp (continuous_add_right x)) (fun γ hγ z => by simp only [hΦdef, add_assoc, hFp γ hγ]) hsJ
  simp only [hkey]
  have hre : ∑' γ : ratL T S, J (-γ) = ∑' a, J a := by
    have e := (Equiv.neg (ratL T S)).tsum_eq J
    simp only [Equiv.neg_apply] at e
    exact e
  rw [tsum_mul_left, hre, show (∑' a, J a) = Φ 0 from hinv]
  simp only [hΦdef, hFdef, zero_add]
  ring

end GlobalTheory.TranslateCoefInversion
