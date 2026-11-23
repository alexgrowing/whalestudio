import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Corev.EmbAGfC

variable {D : D7}

abbrev finfR (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GfC_iff' (V : HSp D) (g : GA D V) : g ∈ GfC V ↔ (Formalism.L2.Theta.mt V g).map (finfR D) = 1 := by
  show infHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand' {k n : ℕ} (x : Mx D k n) (m : Mx D n n) (y : Mx D n k) (hm : m.map (finfR D) = 1) :
    (x ⬝ m ⬝ y).map (finfR D) = (x ⬝ y).map (finfR D) := by
  have e1 : (x ⬝ m ⬝ y).map (finfR D) = x.map (finfR D) ⬝ m.map (finfR D) ⬝ y.map (finfR D) := by
    rw [Matrix.map_mul (f := finfR D), Matrix.map_mul (f := finfR D)]
  have e2 : (x ⬝ y).map (finfR D) = x.map (finfR D) ⬝ y.map (finfR D) := Matrix.map_mul (f := finfR D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GfC' {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GfC A) :
    o.emb (a, 1) ∈ GfC S := by
  rw [mem_GfC_iff'] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finfR D)), map_sand' _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one,
    ← Matrix.map_add _ (map_add (finfR D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem wittCoreEmbedding_mem_finiteAdelicUnitaryGroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {g : GA D S₀} (hg : g ∈ GfC S₀) :
    d.emb0 g ∈ GfC S := by
  rw [mem_GfC_iff'] at hg ⊢
  rw [HypDec.unitaryMatrix_wittCoreEmbedding, Matrix.map_add _ (map_add (finfR D)), Matrix.map_add _ (map_add (finfR D)), map_sand' _ _ _ hg,
    ← Matrix.map_add _ (map_add (finfR D)), ← Matrix.map_add _ (map_add (finfR D)), d.sum_eq_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem embA_mem_GfC_fin : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (κ : GA D A), κ ∈ GfC A → embA d o κ ∈ GfC S := by
  intro D S S₀ A L ρ d o κ hκ
  rw [embA_apply]
  exact wittCoreEmbedding_mem_finiteAdelicUnitaryGroup d (orth_emb_mem_GfC' o hκ)

end GlobalTheory.Corev.EmbAGfC
