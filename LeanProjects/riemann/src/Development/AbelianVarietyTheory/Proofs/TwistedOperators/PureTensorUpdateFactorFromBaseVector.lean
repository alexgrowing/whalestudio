import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorFinitePlaceHeisenbergSumBaseVectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorRealPlaceEqHeisenbergIntegralBaseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorStep

theorem wAt_wAt_ne {D : D7} {m n : ℕ} {p q : Place D} (h : p ≠ q) (w : Mx D m n) : wAt p (wAt q w) = 0 := by
  have h0 : idem D p * idem D q = 0 := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q h
  funext i j
  show idem D p * (idem D q * w i j) = (0 : Mx D m n) i j
  rw [← mul_assoc, h0, zero_mul]
  rfl

theorem wAt_wAt_self {D : D7} {m n : ℕ} (p : Place D) (w : Mx D m n) : wAt p (wAt p w) = wAt p w := by
  have h1 : idem D p * idem D p = idem D p := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p
  funext i j
  show idem D p * (idem D p * w i j) = idem D p * w i j
  rw [← mul_assoc, h1]

theorem change_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (q : Place D), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → x q = f₀ → (∀ p, p ≠ q → x' p = x p) → IsLocal ψ θ S T sS sT ΛS ΛT q (x' q) → ∃ f', IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' f' ∧ ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → (∀ w : WO S T, ipO μ 𝓕 (heisO ψ S T (wAt q w) f) g = c * ipO μ 𝓕 (heisO ψ S T (wAt q w) f₀) g') → ipO μ 𝓕 f' g = c * ipO μ 𝓕 (x' q) g' := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x x' f q hf hxq hx' hloc

  have hop : IsLocOp ψ S T μ 𝓕 f₀ q (x' q) := by
    rcases q with v | τ
    · exact GlobalTheory.T.local_factor_finite_place_heisenberg_sum_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v _ hloc
    · exact GlobalTheory.T.localFactorRealPlace_eq_heisenbergIntegral_base D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ τ _ hloc
  obtain ⟨L, hL, himg, hx'L⟩ := hop
  have hfpure := hf
  obtain ⟨hres, hfth, hprod⟩ := hf

  obtain ⟨f', hf'th, hf'⟩ := himg f hfth
  have hstd := GlobalTheory.PlaceTensor.base_std hB
  have hlaws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T
  have hthw : ∀ u, IsThetaFunO ψ S T (heisO ψ S T u f₀) := fun u => hlaws.1 u f₀ (GlobalTheory.PlaceTensor.base_theta hB)
  refine ⟨f', ⟨⟨?_, ?_⟩, hf'th, ?_⟩, ?_⟩
  · intro p
    by_cases hp : p = q
    · subst hp; exact hloc
    · rw [hx' p hp]; exact hres.1 p
  · refine (hres.2.union (Set.finite_singleton q)).subset ?_
    intro p hp
    by_cases hpq : p = q
    · exact Or.inr hpq
    · left
      have hp' : x' p ≠ f₀ := hp
      rw [hx' p hpq] at hp'
      exact hp'
  · intro w
    have hfin := (hprod w).1
    have hsupp : (Function.mulSupport fun p => ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)).Finite := by
      refine (hfin.union (Set.finite_singleton q)).subset ?_
      intro p hp
      by_cases hpq : p = q
      · exact Or.inr hpq
      · left
        rw [Function.mem_mulSupport] at hp ⊢
        rw [hx' p hpq] at hp
        exact hp
    refine ⟨hsupp, ?_⟩

    have hrest : (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)) =
        ∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀) :=
      finprod_congr fun p => finprod_congr fun hp => by rw [hx' p hp]

    have key : ∀ u, ipO μ 𝓕 (heisO ψ S T (wAt q u) f) (heisO ψ S T w f₀) =
        (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) *
          ipO μ 𝓕 (heisO ψ S T (wAt q u) f₀) (heisO ψ S T (wAt q w) f₀) := by
      intro u
      obtain ⟨-, -, hpu⟩ := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hfpure (wAt q u)
      obtain ⟨hfinu, hequ⟩ := hpu w
      rw [hequ, ← mul_finprod_cond_ne q hfinu]
      dsimp only
      rw [hxq, wAt_wAt_self, mul_comm]
      congr 1
      exact finprod_congr fun p => finprod_congr fun hp => by rw [wAt_wAt_ne hp, WeilVacMove.heisO_zero]
    rw [← mul_finprod_cond_ne q hsupp, hrest, hf' _ (hthw w)]
    simp_rw [key]
    rw [hL, hx'L _ (hthw _), mul_comm]
  · intro g g' c hg hg' hcoef
    rw [hf' g hg, hx'L g' hg']
    simp_rw [hcoef]
    exact hL c _

end GlobalTheory.PlaceTensorStep

end
