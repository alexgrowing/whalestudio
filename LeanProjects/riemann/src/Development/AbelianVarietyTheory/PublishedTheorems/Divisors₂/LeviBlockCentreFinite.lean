import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.Published

def LeviBlockCentreFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J) (Xb Yb : Matrix (Fin n) (Fin d) E),
      Xb = X.submatrix id (fun j => ⟨l + j.val, by omega⟩) → Yb = Y.submatrix id (fun j => ⟨l + j.val, by omega⟩) →
      (∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
        Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
        (∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z))) ∧
        ∀ g : GlobalTheory.CuspRep.GA E d, (matHom _ σ J (ι g)).1 =
          1 + adMat F Xb * (g.1.map Φ.symm - 1) * adMat F (cT (σ : E →+* E) Yb * J) +
            adMat F Yb * (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm) - 1) * adMat F (cT (σ : E →+* E) Xb * J)) →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (φ : GAd σ J → ℂ), GlobalTheory.StdPar.IsAutOn σ J X Y S K φ → ∀ g₀ : GAd σ J,
        ∀ f : GlobalTheory.CuspRep.Sm E d, (∀ x, f.1 x = φ (ι x * g₀)) →
          FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (GlobalTheory.CuspRep.Sm E d) => z f) '' GlobalTheory.CuspRep.Zalg E d))

end GlobalTheory.Published

end
