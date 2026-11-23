import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyConductorBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyResidualImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPlacesOverRealStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.AutPart.chiMu_unr_frob : ∀ (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (μ : D.naut.CG 1), D.naut.csd μ → (∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j) → ∀ w, SplitOut X.nd i w → D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) ∧ ∀ (B : ValuationSubring X.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om), IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)) = {(qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i)))} := by
  intro hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i μ _hcsd hμ w hw
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = X.nd.j i :=
    ⟨⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩, by have := X.nd.j_range i; simp; omega⟩
  have e : (A.chr.e1 (D.naut.tw μ D.naut.etaTinv)).1 = tp.tup (X.nd.mu i) j * cf.eta⁻¹ := by
    rw [A.chr.tw, hμ j hj, A.chr.etaTinv]
  have hU : (A.chr.e1 (D.naut.tw μ D.naut.etaTinv)).1.UnrAt w := by
    rw [e]; exact GlobalTheory.T.galois_family_conductor_bound D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j hj w hw
  have hu : D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := (A.chr.unr_iff _ w).2 hU
  refine ⟨hu, fun B σ hB hσ => ?_⟩
  rw [D.naut.frobEig_tw _ _ hu, A.chr.frob _ w hU, e, Multiset.map_singleton, Multiset.singleton_inj]
  exact (GlobalTheory.T.galois_family_places_over_real hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j hj (GlobalTheory.T.galois_family_residual_image D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i j hj) w hw B σ hB hσ).symm
