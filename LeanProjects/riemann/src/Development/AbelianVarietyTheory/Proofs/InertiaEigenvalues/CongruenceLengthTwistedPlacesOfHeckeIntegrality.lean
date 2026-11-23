import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaJEqZeroOfUntwisted
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RangeAdjointLeOfComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfRationalIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisationStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

theorem etaJ_join_closed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → ∀ (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → HeckeTied D M → HeckeRational D M → AVTied D M → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → ∀ (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)), m = D.R.m → (∀ (i : Fin m), ∀ y ∈ S0.Tw, ∀ x, D.what₂.thetaP (tup (S0.μ y)) ((i : ℕ) + 1) (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1) (eMt i (S0.μ y) x)) = jW i ((S0.θ i (S0.μ y)).mulVec ((lPrj D A P ψ Zs i (S0.μ y)).mulVec x))) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hStd Q hQ hLatInt hHT hHR hAV hCS jW hmR hθ
    hEig hIsot h42 hZ hGood
  have hLat : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w :=
    fun j w h1 h2 hne => GlobalTheory.T.heckeStableLocalLattice_of_rationalIntegrality D M Tn Q hQ hLatInt j w h1 h2 hne
  have hTC : ∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i) := by
    intro i
    have hne := D.nd.w_tw i
    have hy : D.plEq (D.nd.w i) ∈ S0.Tw := by
      refine (hTw _).2 fun e => hne ?_
      rw [hTup.muAt, ← hTup.mu0, e]
    have htw : D.what₂.muTw (D.nd.w i) = tup (S0.μ (D.plEq (D.nd.w i))) :=
      ((D.what₂.muAt_or _).resolve_left hne).symm.trans (hTup.muAt _)
    obtain ⟨hj1, hj2⟩ := D.nd.j_range i
    let i' : Fin m := ⟨D.nd.j i - 1, by omega⟩
    have hj : D.nd.j i = (i' : ℕ) + 1 := by simp only [i']; omega
    rw [D.nd.mu_w i, htw, hj]
    exact GlobalTheory.EtaJoin.thetaCut_of_tie D G Pl0 T m A P ψ Zs tup eMt s hOk S0 jW i' _
      (hMt i' _ hy).1 (hθ i' _ hy)
  have hSpec : ∀ i, SpecPr D i :=
    GlobalTheory.T.good_part_projector_spectral_at_every_localisation D M hHT hHR hAV Tn hStd hCS hTC hEig hIsot h42 hZ hGood
  exact GlobalTheory.etaJ_join D G Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hStd hLat hSpec

end GlobalTheory
