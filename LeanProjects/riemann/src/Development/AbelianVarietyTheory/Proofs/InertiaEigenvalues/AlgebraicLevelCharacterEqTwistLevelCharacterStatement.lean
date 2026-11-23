import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicLevelCharacterEqTwistLevelCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicLevelCharacter_eq_twistLevelCharacter : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → Disjoint M.QP M.DP → ∀ (e₀ : FractionRing (D.ntw.O i) →+* ℂ) (ek : NX.Kk D i k →+* ℂ), (∀ x, ek (NX.toKk D i k x) = e₀ x) → NX.IsStdGeneric (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r (D.nexp.psiU i b) → (∀ (u : D.nexp.U) hu, ((B.G.P.chi ⟨eG u, hu⟩ : ℂˣ) : ℂ) = e₀ (D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ)) → (∀ kv (x : (ZMod (D.host.g kv.1))ˣ) (z : (kP (NX.pG D kv))ˣ), (z : kP (NX.pG D kv)) = iso kv x → ((B.G.muC (NX.pG D kv) z : ℂˣ) : ℂ) = e₀ (τ kv x : (FractionRing (D.ntw.O i))ˣ)) → (∀ PP ∈ M.QP, ∀ u : 𝓞 D.host.E, u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((t.resC PP z : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ PP e u).1)) → (∀ PP ∈ M.DP, ∀ u : 𝓞 D.host.E, u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((B.de.resC PP z : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) PP (if b then e else -e) u).1)) → ∀ g (h : g ∈ M.J) (h' : frameEquiv P g ∈ B.levJ t), ek ((M.χ ⟨g, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = ((B.levLam t ⟨frameEquiv P g, h'⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.LevChiRead.levChi_read | exact GlobalTheory.LevChiRead.levChi_read | (intros; apply GlobalTheory.LevChiRead.levChi_read <;> assumption)
