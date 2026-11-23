import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
      (v : HeightOneSpectrum (𝓞 F)), HasIwasawa σ Q (KFin σ Q L v) → ∀ g : GLoc σ J v,
      ∃ c : Fv F v, c ≠ 0 ∧ ‖c‖₊ ≤ 1 ∧ hgtFin σ Q L v (ioH (Fv F v) σ hQ (g, 1)) = ‖c‖₊ ∧
        ∀ m : ℕ, ‖(m : Fv F v)‖₊ ≤ ‖c‖₊ → ∀ y ∈ latLoc F L v,
          m • ((matHom (Fv F v) σ J g).1 *ᵥ y) ∈ latLoc F L v ∧ m • ((matHom (Fv F v) σ J g⁻¹).1 *ᵥ y) ∈ latLoc F L v := by
  first | exact @GlobalTheory.Doubling.HgtDenom.main | exact GlobalTheory.Doubling.HgtDenom.main | (intros; apply GlobalTheory.Doubling.HgtDenom.main <;> assumption)
