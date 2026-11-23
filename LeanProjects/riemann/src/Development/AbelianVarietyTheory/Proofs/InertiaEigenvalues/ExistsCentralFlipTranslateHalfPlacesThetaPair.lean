import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralConjugateFlipScalarFiniteAdelicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdemSumConjugatePlacesSubsetEqFlipStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipVacuumEqMultipleOfTranslateMeanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MovedVacuumTranslateSumFlipScalarStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipMapsHalfTranslatesSpanStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem exists_central_flip_step : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ), ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ ∀ eT : AE D, IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ x : (AE D)ˣ, IsFlipDet V eT m x ∧ ∀ (M u : ℕ) (e e' : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ), M = m * u → (∀ PP ∈ T, ((u : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e P → T ⊆ P → IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) → zeta M ∈ O → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∃ F ∈ trSp ψ V W ΛV ΛW f₀ e' M O, om (z, 1) (flipScal χW V W T m x • F) = f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m
  by_cases h : ∃ eT : AE D, IsIdemSum eT T ∧ m ≠ 0
  · obtain ⟨eT₀, h0, hm0⟩ := h
    obtain ⟨z, hzG, hzOne, hzmt⟩ := GlobalTheory.T.exists_central_conjugateFlipScalar_finiteAdelic D V T m eT₀ h0 hm0
    refine ⟨z, hzG, hzOne, ?_⟩
    intro eT heT hodd hcop hmT
    have h1 : eT₀ * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset heT h0 subset_rfl
    have h2 : eT * eT₀ = eT₀ := GlobalTheory.Tow.idemSum_mul_of_subset h0 heT subset_rfl
    have hEq : eT = eT₀ := by rw [← h1, mul_comm, h2]
    subst hEq
    have hidem : eT * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset heT heT subset_rfl
    have hinv : incA D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
      rw [← map_natCast (incA D) m, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm0), map_one]
    have hpq : incA D ((m : D.host.E)⁻¹) ^ V.rank * (m : AE D) ^ V.rank = 1 := by
      rw [← mul_pow, hinv, one_pow]
    have hunit : (eT * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - eT)) * (eT * (m : AE D) ^ V.rank + (1 - eT)) = 1 := by
      linear_combination (eT * eT) * hpq + (2 - incA D ((m : D.host.E)⁻¹) ^ V.rank - (m : AE D) ^ V.rank) * hidem
    let x : (AE D)ˣ := Units.mkOfMulEqOne _ _ hunit
    have hx : IsFlipDet V eT m x := hunit
    refine ⟨x, hx, ?_⟩
    obtain ⟨lam, Y, hY, hYd, hYc, hom⟩ := GlobalTheory.T.centralFlip_vacuum_eq_multiple_of_translate_mean D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z heT hodd hcop hmT hzG hzmt
    have hlam := GlobalTheory.T.movedVacuum_translateSum_flipScalar D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z x lam Y heT hodd hcop hmT hzG hzmt hx hY hYd hYc hom
    subst hlam
    have hs : flipScal χW V W T m x ≠ 0 := by
      unfold flipScal
      refine mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero _)) (inv_ne_zero ?_)
      rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
      exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (flipIdx_ne_zero V W T hm0))
    intro M u e e' P O hM hu he hTP he' hz
    exact GlobalTheory.T.centralFlip_maps_halfTranslates_span D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z _ Y heT hodd hcop hmT hzmt hs hY hom M u e e' P O hM hu he hTP
      (GlobalTheory.T.isIdemSum_conjugatePlaces_subset_eq_flip D e eT e' P T he heT hTP he') hz
  · refine ⟨1, (GfC V).one_mem, fun l _ => oneAt_one V l, ?_⟩
    intro eT heT hodd
    exact absurd ⟨eT, heT, (Nat.pos_of_ne_zero (by rintro rfl; exact (Nat.not_odd_zero hodd))).ne'⟩ h

end GlobalTheory.LevelSeries

end
