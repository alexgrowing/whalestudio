import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVariety
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

open Set Filter Topology

namespace GlobalTheory.LogNormIntGen

theorem archIntegrable : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ}, IsArithVar p D → GenSmooth p D → ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ}
      (hr : IsRatSec N.B r), M.ArchIntegrable N D hr := by
  intro k _ X _ p D hX hs M N r hr σ
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hs σ
  have hσ : Function.Injective σ := ChernNull.injective_of_arithVar hX σ
  have key (ε : ℤˣ) : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr))
      ((M.φ σ).chernPart D ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm (N.φ σ) r)
        (offSupp p σ (N.div hr) ∩ O) ((M.φ σ).chernPart D ε) :=
      have ⟨_, hi⟩ := R.cover y
      LogNormInt.exists_integrableOn hσ (M.cInf σ) (N.cInf σ) hr ε _ hi
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
    obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.LogNormIntGen
