import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyConductorBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
theorem tupEtaInv_unrAt_splitOut_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → ∀ w, SplitOut X.nd i w → (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt w := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j _hj w hw
  obtain ⟨_hsplit, hl, hS, hQ⟩ := hw
  have hS' : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
      w ∈ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde))) := fun h =>
    hS ((X.nd.S_def i w).2 ⟨h, hl⟩)
  have hmu0 : (cf.mu0 j).UnrAt w := (cf.isMu0 j).unr w (fun k hk => by
    fin_cases k
    · exact hS' (Or.inl hk)
    · exact hS' (Or.inr (Or.inl hk)))
  have hmem : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQeq : X.nd.Q i = C.Q (X.nd.w i) := (Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)
  have hpsi : (tp.psi (X.nd.w i)).UnrAt w :=
    ((tp.psi_is (X.nd.w i) (X.nd.w_tw i)).ram w).2 (by rw [← hQeq]; exact hQ)
  have hdel : (cf.delAt (D.what₂.places.resChar (X.nd.w i))).UnrAt w := by
    rw [X.nd.w_l i]
    unfold CharFrame.delAt
    split_ifs with h
    · exact cf.isDel'.unr w (fun hp => hS' (Or.inr (Or.inr (by rw [if_pos h]; exact hp))))
    · exact cf.isDel.unr w (fun hp => hS' (Or.inr (Or.inr (by rw [if_neg h]; exact hp))))
  have hxi : (tp.xi (X.nd.mu i)).UnrAt w := by
    rw [X.nd.mu_w i, tp.xi_tw]
    exact HChar.UnrAt.mul hdel hpsi
  exact HChar.UnrAt.mul (HChar.UnrAt.mul hmu0 hxi) (HChar.UnrAt.inv (cf.isEta.unr w))
end GlobalTheory.HeightCounting
end
end
