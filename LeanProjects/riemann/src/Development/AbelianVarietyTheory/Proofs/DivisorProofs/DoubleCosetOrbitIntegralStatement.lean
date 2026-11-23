import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOrbitIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_orbit_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ γ ∈ ratU σ W₂.J, ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), Function.Injective Y.mulVec →
      (∀ k l, form σ W.J (fun a => Y a k) (fun a => Y a l) = 0) →
      (∀ y : Fin d → E, (mat γ *ᵥ pairVec finSumFinEquiv 0 (incV F y) ∈ diagSub (AE F E) finSumFinEquiv ↔
        ∃ a : Fin j → E, y = Y *ᵥ a)) →
    ∀ n ∈ GlobalTheory.ThKLiftCusp.unipSp σ W Y, ∃ hp : γ * i (1, n) * γ⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype,
      aOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype ⟨_, hp⟩ = 1 := by
  first | exact @GlobalTheory.UnipConjSiegel.conj_mem_siegel | exact GlobalTheory.UnipConjSiegel.conj_mem_siegel | (intros; apply GlobalTheory.UnipConjSiegel.conj_mem_siegel <;> assumption)
