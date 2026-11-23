import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserSplitPlace
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.IwSplitLine

theorem iwasawa_line_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * y = 0 → cT (σ : E →+* E) x * J * y = 1 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ h n J hJ x y hxx hyy hxy hyx L hLat v hv hL g
  obtain ⟨P, P', hne, hP, hP'⟩ := hv
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq h (v := v) hne (IsDedekindDomain.HeightOneSpectrum.ext hP) (IsDedekindDomain.HeightOneSpectrum.ext hP')
  obtain ⟨k, i, qq, hn, hsum⟩ := GlobalTheory.IwSplitFrame.exists_compl x y (cT (σ : E →+* E) y * J) (cT (σ : E →+* E) x * J)
    hyx hyy hxx hxy
  obtain ⟨B, lv, hB⟩ := GlobalTheory.Core.Rk.IwFlagSplit.exists_flag_basis (v := v) τ hJ
    (e := x) (e' := y) (i := i) (p := cT (σ : E →+* E) y * J) (q := qq)
    (Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)) hsum hxy
  have hQ : ∀ z : GLoc σ J v, (B⁻¹ * splitHom σ J τ z * B).1.BlockTriangular lv →
      z ∈ GlobalTheory.IwSplitFrame.keepGrp (σ := σ) (J := J) (v := v) (x.map (inclR (F := F) (Fv F v))) :=
    fun z hz => by
      obtain ⟨⟨b, hb⟩, b', hb'⟩ := hB z hz
      exact GlobalTheory.IwSplitFrame.keeps_of_split h τ z hyx hb hb'
  obtain ⟨q, k', hq, hk, rfl⟩ := GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_of_triangular h hJ τ L hL _ B lv hQ g
  obtain ⟨β, hβ⟩ := hq
  exact ⟨q, k', hk, rfl, β, hβ⟩

end GlobalTheory.IwSplitLine
