import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilatorStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaCoefficient

open GlobalTheory.FinTranslate

theorem exists_unit_smul {X : Type} (f f' : X → ℂ) (h : ∀ x y, f' y * star (f' x) = f y * star (f x)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  have hn : ∀ x, ‖f' x‖ = ‖f x‖ := fun x => by
    have := congrArg norm (h x x)
    rw [norm_mul, norm_mul, norm_star, norm_star] at this
    exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 this
  by_cases h0 : ∀ x, f x = 0
  · refine ⟨1, norm_one, funext fun x => ?_⟩
    have := hn x
    rw [h0, norm_zero, norm_eq_zero] at this
    simp [this, h0]
  · obtain ⟨x, hx⟩ := not_forall.1 h0
    have hx' : f' x ≠ 0 := fun e => hx (by rw [← norm_eq_zero, ← hn, e, norm_zero])
    refine ⟨star (f x) / star (f' x), ?_, funext fun y => ?_⟩
    · rw [norm_div, norm_star, norm_star, hn, div_self (norm_ne_zero_iff.2 hx)]
    · have hs : star (f' x) ≠ 0 := star_ne_zero.2 hx'
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h x y, mul_comm]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_eq (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold symplOH
  linear_combination (-symplO S T x y) * h2

theorem char_mul_heisO {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) {γ : WO S T} (hγ : γ ∈ ratL T S) (w x : WO S T) :
    ψ (symplO S T x γ) * heisO ψ S T w g x = ψ (symplOH S T γ w) * heisO ψ S T (γ + w) g x := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hg.quasi γ (x + w)
  show ψ (symplO S T x (ratW T S γ)) * (ψ (symplOH S T x w) * g (x + w)) =
    ψ (symplOH S T (ratW T S γ) w) * (ψ (symplOH S T x (ratW T S γ + w)) * g (x + (ratW T S γ + w)))
  rw [add_left_comm, h]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [symplO_eq, symplOH_add_right, symplOH_add_right, symplOH_skew S T x (ratW T S γ)]
  congr 2
  ring

theorem exists_unit_smul_of_coefficient_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f f' : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ w, ∫ x in 𝓕, heisO ψ S T w f' x * star (f' x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 f f' hf hf' h
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have hT := @GlobalTheory.ThetaClosed.isThetaFunO_heisO_all D ψ hψ S T
  refine exists_unit_smul f f' fun x y => ?_
  obtain ⟨w, rfl⟩ : ∃ w, y = x + w := ⟨y - x, by abel⟩
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      simp only [symplO_eq]
      exact hψ.1.1.comp ((continuous_symplOH S T _).add (continuous_symplOH S T _)))
    (fun γ x y => by
      simp only [symplO_eq, symplOH_add_left, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun γ γ' x => by
      show ψ (symplO S T x (γ + γ')) = ψ (symplO S T x γ) * ψ (symplO S T x γ')
      simp only [symplO_eq, symplOH_add_right, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun x => by
      show ψ (symplO S T x 0) = 1
      rw [symplO_eq, symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by rw [← GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x]; exact Subtype.forall)
    μ 𝓕 hμ h𝓕 (fun x => heisO ψ S T w f' x * star (f' x) - heisO ψ S T w f x * star (f x))
    (by
      have a := (hT hf' w).cont
      have b := (hT hf w).cont
      have a' := hf'.cont
      have b' := hf.cont
      generalize heisO ψ S T w f' = u at a
      generalize heisO ψ S T w f = v at b
      exact (a.mul a'.star).sub (b.mul b'.star))
    (fun γ hγ x => by
      have a := GlobalTheory.Size.mul_conj_periodic hψ (hT hf' w) hf' γ hγ x
      have b := GlobalTheory.Size.mul_conj_periodic hψ (hT hf w) hf γ hγ x
      simp only [starRingEnd_apply] at a b
      simp only [a, b])
    (fun γ => by
      have e : ∀ x, ψ (symplO S T x γ) * (heisO ψ S T w f' x * star (f' x) - heisO ψ S T w f x * star (f x)) =
          ψ (symplOH S T γ w) * (heisO ψ S T (γ + w) f' x * star (f' x) - heisO ψ S T (γ + w) f x * star (f x)) :=
        fun x => by
          linear_combination star (f' x) * char_mul_heisO hf' γ.2 w x - star (f x) * char_mul_heisO hf γ.2 w x
      simp only [e]
      have a := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 (hT hf' (γ + w)) hf'
      have b := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 (hT hf (γ + w)) hf
      rw [integral_const_mul]
      refine mul_eq_zero_of_right _ ((integral_sub a b).trans (sub_eq_zero.2 (h _))))
  have e := congrFun key x
  have hne : ψ (symplOH S T x w) ≠ 0 := fun e => by simpa [e] using hψ.1.2.1 (symplOH S T x w)
  simp only [heisO, Pi.zero_apply] at e
  refine mul_left_cancel₀ hne ?_
  linear_combination e

end GlobalTheory.ThetaCoefficient
