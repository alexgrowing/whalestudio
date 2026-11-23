import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicFrameDecompositionOfWittFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovolStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicLeviNormOneLastColumnProdEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTopStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.ResidueEisenstein

theorem finCovol_leviOne_last : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW π DM hπ hDM
  obtain ⟨m, Z, J₀, hF⟩ := GlobalTheory.T.exists_isotropicFrameDecomposition_of_wittFrame F E σ n J r X Y hcm hJ hW
  letI : MeasurableSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := ⟨rfl⟩
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  set A := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hA
  set G₁ := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker
  set ΓA := (ratPts σ J).subgroupOf A
  set ΓG := (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range.subgroupOf G₁
  obtain ⟨hlc, hsc, hdisc, hfinGL⟩ := GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume F E σ hcm (r + 1)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.standardParabolicLeviNormOne_lastColumn_prodEquiv F E σ n J r m X Y Z J₀ hF
  have hclA : IsClosed (A : Set (GAd σ J)) :=
    (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const).inter
      (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const)
  haveI : LocallyCompactSpace A := hclA.locallyCompactSpace
  haveI : LocallyCompactSpace (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) :=
    (GlobalTheory.StdPar.isClosed_levi _ hcm hJ hW).2.locallyCompactSpace
  haveI := hlc
  haveI := hsc
  haveI := hdisc
  haveI : DiscreteTopology ΓA := DiscreteTopology.of_continuous_injective
    (f := fun x : ΓA => (⟨(x.1 : GAd σ J), x.2⟩ : ratPts σ J))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun a b h => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun y : ratPts σ J => (y : GAd σ J)) h)
  haveI : Countable (ΓA.prod ΓG) := by
    haveI : Countable ΓA := inferInstance
    haveI : Countable ΓG := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact Function.Injective.countable (f := fun x : ΓA.prod ΓG => ((⟨x.1.1, x.2.1⟩ : ΓA), (⟨x.1.2, x.2.2⟩ : ΓG)))
      (fun a b h => Subtype.ext (Prod.ext (congrArg (fun q => (q.1 : A)) h) (congrArg (fun q => (q.2 : G₁)) h)))
  refine GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv (A × G₁) _ φ (ΓA.prod ΓG) _ (fun g => ?_)
    (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.measure_fundamentalDomain_prod_lt_infty A G₁ ΓA ΓG
      (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns F E σ n J (r + 1) m X Y Z J₀ hF μ 𝓕 hμ h𝓕) (fun μ hμ 𝓕 h𝓕 => hfinGL μ 𝓕 hμ h𝓕)
      μ hμ 𝓕 h𝓕) π DM hπ hDM
  rw [Subgroup.mem_prod, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hφ g]

end GlobalTheory.ResidueEisenstein
