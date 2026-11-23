import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ShellP
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.TracePairSums.ShellConj

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem jtR_conj_inv (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : Fv F v → ℂ) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    [μv.IsAddHaarMeasure] (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (hΦ : IsSB Φv) :
    ∃ r > 0, ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r → ∀ b b' : HermR (Fv F v) σ n,
      (b' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = ((1 + x).map (sigR (Fv F v) σ))ᵀ * b * (1 + x) →
      jtR (Fv F v) σ J ψR μv Φv b' = jtR (Fv F v) σ J ψR μv Φv b :=
  SwSplit.jtR_conj_inv' v σ hcm J ψR μv Φv hΦ

end PositivityTheory.SiegelWeilFormula.SwLocFin
