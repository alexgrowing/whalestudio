import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLinearHomCoordinateLatticeFgStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHomGramFormIntegralCoordinateLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCmCoordinateLatticeOfIntegralGramPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSmulDifferentialMemEigenLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenLatticeLeSpanCmHomImagesStatement

set_option autoImplicit false

open NumberField

namespace GlobalTheory.FlatCM.HomLat

theorem exists_selfDual_lieSpan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ Λ : Submodule (𝓞 E) (Fin p → E), Λ.FG ∧ (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) ∧
      (∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
        ∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ = Submodule.span (𝓞 K)
            {w | ∃ c ∈ Λ, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG
  refine ⟨GlobalTheory.FlatCM.HomLat.lat X, GlobalTheory.T.cmLinearHomCoordinateLattice_fg E H hH K ρ σ₁ p X, GlobalTheory.FlatCM.HomLat.intl_mem X,
    fun barE hbar d => ⟨fun hd c hc => GlobalTheory.T.cmHomGramForm_integral_coordinateLattice E H hH K ρ σ₁ p X gP gQ hG barE hbar c hc d hd,
      GlobalTheory.T.mem_cmCoordinateLattice_of_integral_gramPairing E H hH K ρ σ₁ p X gP gQ hG barE hbar d⟩, ?_⟩
  intro FP FB MP hMP τ hτ τE hτE
  refine le_antisymm (GlobalTheory.T.lieEigenLattice_le_span_cmHom_images E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE) ?_
  refine Submodule.span_le.2 ?_
  rintro w ⟨c, hc, e, he, rfl⟩
  induction hc using Submodule.span_induction generalizing e with
  | mem c hc => exact GlobalTheory.T.sum_smul_differential_mem_eigenLattice E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE c hc e he
  | zero => simp
  | add c d _ _ hc hd =>
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    exact add_mem (hc e he) (hd e he)
  | smul s c _ hc =>
    have h1 : ∑ a, τE ((s • c) a) • MP a e = ∑ a, τE (c a) • MP a ((τ s : K) • e) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 : τE ((s • c) a) = (τ s : K) * τE (c a) := by
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        exact congrArg (· * τE (c a)) (hτE s)
      rw [h2, mul_smul, (MP a).map_smul, smul_comm]
    rw [h1]
    exact hc _ (by simpa [algebraMap_smul] using (FP.eigLat (X.A true).t.act τ).smul_mem (τ s) he)

end GlobalTheory.FlatCM.HomLat
