import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealRationalPointActsHarmonicSubstitution
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_rational_point_acts_harmonic_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (lt : LtN Dw V.rank ≃ FVar D W.rank V.rank) (wa : (D.host.E →+* ℂ) × ℕ → ℕ), W.rank = Dw.p + Dw.q → (∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) → (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) Dw.p) → IsLetters Dw lt → ∀ l c : ℕ, ∃ c' : ℕ, ∀ (γ a : GA D V) (γ' : GL (Fin V.rank) D.host.E) (O : Subring ℂ), γ ∈ GQ V → GlobalTheory.Member.IsRat V γ γ' → a ∈ GinfC V → γ * a ∈ GfC V → (∀ (τ : D.host.E →+* ℂ) x y, (l : ℂ) ^ c * τ (γ'.val x y) ∈ O ∧ (l : ℂ) ^ c * τ (γ'⁻¹.val x y) ∈ O) → ∀ Q ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q.coeff mo ∈ O) → ∃ Q' ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q'.coeff mo ∈ O) ∧ ∀ (M : ℕ) (e : AE D) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁, ((l : ℂ) ^ c') • om (a, 1) (stdF ψ θ V W sW BW f (MvPolynomial.rename lt Q)) = stdF ψ θ V W sW BW f (MvPolynomial.rename lt Q') := by
  first | exact @GlobalTheory.LevelSeries.ArchAct.real_act_harm | exact GlobalTheory.LevelSeries.ArchAct.real_act_harm | (intros; apply GlobalTheory.LevelSeries.ArchAct.real_act_harm <;> assumption)
