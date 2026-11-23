import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionTargetFlagUnipotentHomEquivariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_action_target_flag_unipotent_hom_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T T₀ S : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (y : Mx D S.rank ρ), (∀ u ∈ UX D ρ, y ⬝ u.1 = y) → (∀ b c, cenT d S y (d.nB b * d.nC c) = d.qT S c y) ∧ (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ptT d S y (n * n') = ptT d S y n + ptT d S y n' ∧ cenT d S y (n * n') = cenT d S y n + cenT d S y n' + symplOH S T₀ (ptT d S y n) (ptT d S y n') ∧ ∀ f, jacT ψ d S y (n * n') f = jacT ψ d S y n (jacT ψ d S y n' f)) ∧ (∀ n ∈ flagN d, ∀ u ∈ UX D ρ, jacT ψ d S y (n * d.levi u) = jacT ψ d S y n) ∧ ∀ n g, ptT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S T₀ 1 g (ptT d S y n) ∧ cenT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = cenT d S y n := by
  first | exact @GlobalTheory.MixPer.jacT_hom | exact GlobalTheory.MixPer.jacT_hom | (intros; apply GlobalTheory.MixPer.jacT_hom <;> assumption)
