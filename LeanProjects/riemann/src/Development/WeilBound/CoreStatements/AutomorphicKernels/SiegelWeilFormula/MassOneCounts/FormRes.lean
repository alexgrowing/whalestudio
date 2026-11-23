import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.ZOfSurj
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.FormRes

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_res (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) F)
    (hBt : ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin 1 → R ⊗[F] E),
      Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        (fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
          (B.map (algebraMap F R) *ᵥ fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (v : HeightOneSpectrum (𝓞 F))
    (hfix : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = x → ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c)
    (htr : ∀ a : Fv F v ⊗[F] E,
      (∀ y ∈ Rv b v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * y) ∈ v.adicCompletionIntegers F) ↔ a ∈ Rv b v)
    (hR1 : (1 : Fv F v ⊗[F] E) ∈ Rv b v)
    (hRmul : ∀ x ∈ Rv b v, ∀ y ∈ Rv b v, x * y ∈ Rv b v)
    (hRsig : ∀ x ∈ Rv b v, sigR (Fv F v) σ x ∈ Rv b v)
    (h2 : Valued.v (2 : Fv F v) = 1) (hj : inclR (Fv F v) (J 0 0) ∈ Rv b v)
    (ϖ : v.adicCompletionIntegers F) (hϖ0 : (ϖ : Fv F v) ≠ 0) (hϖ1 : ‖(ϖ : Fv F v)‖ < 1)
    (hϖd : ∀ x : v.adicCompletionIntegers F, ‖(x : Fv F v)‖ < 1 → ϖ ∣ x)
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) (s : v.adicCompletionIntegers F) :
    Valued.v ((2 : Fv F v)⁻¹ * ((fun p => (w p : Fv F v)) ⬝ᵥ
        (B.map (algebraMap F (Fv F v)) *ᵥ fun p => (w p : Fv F v))) - s) < 1 ↔
      ∃ y ∈ Rv b v, sigR (Fv F v) σ (zOf b v w) * inclR (Fv F v) (J 0 0) * zOf b v w -
        algebraMap (Fv F v) (Fv F v ⊗[F] E) s = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * y :=
  PositivityTheory.SiegelWeilFormula.Densx.form_res σ hCM J hJ d b B hBt v hfix htr hR1 hRmul hRsig h2 hj ϖ hϖ0 hϖ1 hϖd w s

end PositivityTheory.SiegelWeilFormula.MOne

end
