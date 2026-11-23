import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomain
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
theorem _root_.GlobalTheory.T.unipotent_fundamental_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s →
    ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), 1 ≤ j → Function.Injective Y.mulVec →
      (∀ k l, form σ W.J (fun a => Y a k) (fun a => Y a l) = 0) →
      ∃ (ν : Measure (GlobalTheory.ThKLiftCusp.unipSp σ W Y)) (𝓕 : Set (GlobalTheory.ThKLiftCusp.unipSp σ W Y)), ν.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (GlobalTheory.ThKLiftCusp.unipSp σ W Y)) 𝓕 ν ∧ ν 𝓕 = 1 := by
  first | exact @GlobalTheory.UnipSpMass.exists_haar_unipSp_mass_one | exact GlobalTheory.UnipSpMass.exists_haar_unipSp_mass_one | (intros; apply GlobalTheory.UnipSpMass.exists_haar_unipSp_mass_one <;> assumption)
