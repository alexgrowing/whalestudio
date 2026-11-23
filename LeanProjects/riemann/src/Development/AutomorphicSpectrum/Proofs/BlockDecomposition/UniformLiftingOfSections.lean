import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformFirstCohomologyKernelsExistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVeryAmpleOpensExistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerAnnihilatesSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftVeryAmpleSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpensStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechCoverCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechRestrictionCommutesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsGenerateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningTwistedSectionTransitionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsNonvanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftClosedEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftProjectiveEmbeddingCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option maxHeartbeats 1000000 in

theorem exists_uniform_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (d : ℕ), 1 ≤ d → ∀ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))), VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ D : ℤ, D = d * t → ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D), SecMaps (pullPow (v e) D) σ (secPull σ' (β e)) := by
  intro R _ _ I Y β hβ hP N v hN d hd m s hs
  obtain ⟨g, ρ, hρ⟩ : ∃ (g : ℕ) (ρ : Fin g → R), Ideal.span (Set.range ρ) = I := by
    obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨S.card, fun k => (S.equivFin.symm k : R), ?_⟩
    rw [← hS]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    exact ⟨fun ⟨k, hk⟩ => hk ▸ (S.equivFin.symm k).2, fun hx => ⟨S.equivFin ⟨x, hx⟩, by simp⟩⟩
  subst hρ
  obtain ⟨D, hD0, hDβ, hDm, hDi, hDc, hDa⟩ :=
    GlobalTheory.T.thickening_very_ample_opens_exist R _ Y β hβ (pw (N 0) (d : ℤ)) m s (isLB_pw (hN 0).1 _) hs
  obtain ⟨sh, hsh0, hshp, hshu⟩ := GlobalTheory.T.formal_lift_very_ample_sections R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
  have hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R)
      (A := fun t => Tm _ Y N D (d : ℤ) e t S) fun j t => mulT _ Y N D (d : ℤ) e t S (sh e j S) :=
    fun e S i j t a => mulT_comm _ Y N D (d : ℤ) e t S (sh e i S) (sh e j S) a
  have hloc := GlobalTheory.T.formal_lift_sections_nonvanishing R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc
  have hDβ' : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S := fun e S => (hDβ e S).ge
  have h_pres : ∀ e t (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm _ Y N D (d : ℤ) (e + 1) t S),
      S.Nonempty → red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S' (resT _ Y N D (d : ℤ) hDm (e + 1) t h a) =
        resT _ Y N D (d : ℤ) hDm e t h (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S a) :=
    fun e t S S' h a _ => GlobalTheory.T.thickening_restriction_compatible_opens R _ Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S)
      (D (e + 1) S') (D e S) (D e S') (hDβ' e S) (hDβ' e S') (hDm (e + 1) S S' h)
      (hDm e S S' h) a
  have h_mp : ∀ j e t (S : Finset (Fin (m + 1))) (a : Tm _ Y N D (d : ℤ) (e + 1) t S), S.Nonempty →
      red _ Y N D β hβ v hN hDβ' ((d : ℤ) * (t + 1)) e S (mulT _ Y N D (d : ℤ) (e + 1) t S (sh (e + 1) j S) a) =
        mulT _ Y N D (d : ℤ) e t S (sh e j S) (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S a) := by
    intro j e t S a hS
    have h1 := GlobalTheory.T.thickening_cech_cover_compatible R _ Y β hβ N v hN (Fin (m + 1)) D hDβ' ((d : ℤ) * t)
      (d : ℤ) ((d : ℤ) * (t + 1)) (by ring) e S ((SecOnR.of _ _ _).symm a) (sh (e + 1) j S)
    rw [hshp e j S hS] at h1
    exact h1
  have h_mres : ∀ j e t (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm _ Y N D (d : ℤ) e t S), S.Nonempty →
      resT _ Y N D (d : ℤ) hDm e (t + 1) h (mulT _ Y N D (d : ℤ) e t S (sh e j S) a) -
        mulT _ Y N D (d : ℤ) e t S' (sh e j S') (resT _ Y N D (d : ℤ) hDm e t h a) ∈
          Ideal.span (Set.range ρ) • (⊤ : Submodule R (Tm _ Y N D (d : ℤ) e (t + 1) S')) :=
    fun j e t S S' h a hS => GlobalTheory.T.formal_lift_sections_generate R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
      sh hsh0 hshp hshu j e t S S' h a hS
  have h_G3 : ∀ e t (S : Finset (Fin (m + 1))), S.Nonempty →
      Function.Surjective (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S) ∧
        LinearMap.ker (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤ :=
    fun e t S hS => GlobalTheory.T.thickening_affine_preimage R _ Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1) S hS)
  have h_kill : ∀ e t (S : Finset (Fin (m + 1))), S.Nonempty →
      Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (Tm _ Y N D (d : ℤ) e t S)) = ⊥ :=
    fun e t S _ => GlobalTheory.T.ideal_power_annihilates_sections R _ Y e _ _
  have h_bij : ∀ i e t (S : Finset (Fin (m + 1))), i ∈ S → Function.Bijective (mulT _ Y N D (d : ℤ) e t S (sh e i S)) := by
    intro i e t S hi
    obtain ⟨y, hy⟩ := hshu e i S hi
    exact GlobalTheory.T.thickening_twisted_section_transition R _ Y β hβ N v hN (d : ℤ) (Fin (m + 1)) D e t S (sh e i S) y hy
  have h_one : ∀ e (i : Fin (m + 1)), red _ Y N D β hβ v hN hDβ' ((d : ℤ) * 0) e {i} (oneT _ Y N D (d : ℤ) (e + 1) {i}) =
      oneT _ Y N D (d : ℤ) e {i} :=
    fun e i => GlobalTheory.T.thickening_cech_restriction_commutes R _ Y β hβ N v hN (Fin (m + 1)) D hDβ' ((d : ℤ) * 0) (mul_zero _) e {i}
  have h_fin := GlobalTheory.T.formal_lift_closed_embedding R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.uniform_first_cohomology_kernels_exist (Fin (m + 1)) R g ρ (Tm _ Y N D (d : ℤ))
    (fun e t S S' h => resT _ Y N D (d : ℤ) hDm e t h)
    (fun e t S => red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S)
    (fun j e t S => mulT _ Y N D (d : ℤ) e t S (sh e j S))
    (fun e i => oneT _ Y N D (d : ℤ) e {i}) hc
    (fun e t S h a => SecOnR.restrict_self _ _ _)
    (fun e t S S' S'' h h' a => SecOnR.restrict_restrict _ _ _ _)
    h_pres h_mp h_mres (fun e t S hS => (h_G3 e t S hS).1) (fun e t S hS => (h_G3 e t S hS).2)
    h_kill h_bij hloc.1 hloc.2 h_one h_fin
  refine ⟨t₀.toNat, fun t ht D' hD' e σ => ?_⟩
  subst hD'
  exact GlobalTheory.T.formal_lift_projective_embedding_compatible R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa (t : ℤ) e
    (fun c hc0 hcoc => ht₀ t (by omega) e c hc0 hcoc) σ

end GlobalTheory.CompanionTheory.FormalAlg.Lift
