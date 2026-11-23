import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def NbFacts : Prop :=
  ∀ (D : D7) (n : ℕ) (nb : hermA D n → G D n), PositivityTheory.PfSWUS.IsNMap nb →
    Continuous nb ∧ (∀ b c, nb (b + c) = nb b * nb c) ∧ ∀ γ ∈ ratHerm D n, nb γ ∈ GF D n

def CharFacts : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : HermE D n,
    Continuous (fun b : hermA D n => ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧
    ∀ b : hermA D n, ‖ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1

def HermCocompact : Prop :=
  ∀ (D : D7) (r : ℕ), ∃ K : Set (hermA D r), IsCompact K ∧ ∀ x, ∃ l ∈ ratHerm D r, x - l ∈ K

theorem gLamBd_of (hNb : NbFacts) (hCh : CharFacts) (hCo : HermCocompact) : GLamBd := by
  intro D n ψ hψ L hL
  obtain ⟨nb, lam, 𝓖, β, g, ⟨hnb, hlam, hfd, hvol⟩, -, rfl⟩ := hL
  obtain ⟨hcont, hadd, hrat⟩ := hNb D n nb hnb
  obtain ⟨hχc, hχn⟩ := hCh D n ψ hψ β
  obtain ⟨K, hK, hKc⟩ := hCo D n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  set χ : hermA D n → ℂ := fun b => ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) with hχ
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun b : hermA D n => nb b * g := hcont.mul continuous_const

  have hper : ∀ (F : G D n → ℂ), (∀ γ ∈ GF D n, ∀ x, F (γ * x) = F x) → ∀ b, ∃ k ∈ K,
      F (nb b * g) = F (nb k * g) := by
    intro F hF b
    obtain ⟨l, hl, hbl⟩ := hKc b
    refine ⟨b - l, hbl, ?_⟩
    have e : nb b = nb l * nb (b - l) := by rw [← hadd, add_sub_cancel]
    rw [e, mul_assoc, hF _ (hrat l hl)]

  have hbd : ∀ (F : G D n → ℂ) (M : ℝ), (∀ γ ∈ GF D n, ∀ x, F (γ * x) = F x) →
      (∀ x ∈ (fun b => nb b * g) '' K, ‖F x‖ ≤ M) → ∀ b, ‖F (nb b * g) * χ b‖ ≤ M := by
    intro F M hF hM b
    obtain ⟨k, hk, e⟩ := hper F hF b
    rw [norm_mul, hχn b, mul_one, e]
    exact hM _ ⟨k, hk, rfl⟩
  have hint : ∀ (F : G D n → ℂ), Continuous F → (∀ γ ∈ GF D n, ∀ x, F (γ * x) = F x) →
      IntegrableOn (fun b => F (nb b * g) * χ b) 𝓖 lam := by
    intro F hFc hF
    obtain ⟨M, hM⟩ := (hK.image hcm).exists_bound_of_continuousOn hFc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_
    · exact ((hFc.comp hcm).mul hχc).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun b => hbd F M hF hM b
  refine ⟨fun a F F' hFc hF'c hF hF' => ?_, ⟨(fun b => nb b * g) '' K, hK.image hcm, fun F M hFc hF hM => ?_⟩⟩
  · simp only [PositivityTheory.PfSWUS.fc]
    have e : (fun b : hermA D n => (a • F + F') (nb b * g) *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) =
        fun b => a * (F (nb b * g) * χ b) + F' (nb b * g) * χ b := by
      funext b; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]; ring
    rw [e, integral_add ((hint F hFc hF).const_mul a) (hint F' hF'c hF'), integral_const_mul]
  · show ‖∫ b in 𝓖, F (nb b * g) * χ b ∂lam‖ ≤ M
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun b _ => hbd F M hF hM b)
    have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
    rwa [hr, mul_one] at h1

end PositivityTheory.Rg.Sw.Glob
