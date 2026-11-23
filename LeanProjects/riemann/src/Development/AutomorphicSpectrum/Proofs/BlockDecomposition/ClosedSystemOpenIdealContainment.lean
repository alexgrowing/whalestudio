import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsetOfClosedFibre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionsEqUnivOffBadSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfBadSetClosedFibre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSubsetSupportProper
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsQuasicoherentOfSecsImage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSupportedInPreimage

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.PSupp

theorem propSupp_of_closed_image : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ (Sb : Subobject P) (T : (O : Scheme.{0}).IdealSheafData), IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) → (∀ V : X.Opens, Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs Sb V = Set.univ) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → Bb ⊔ powSub I P 1 = Sb → ∀ B : Subobject E, (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → PropSupp A B := by
  intro A _ _ I hI X _ _ O
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf Sb T hTc hSb Bb hBq hBS B hB
  have hC : IsClosed (badSet Bb) := isClosed_badSet Bb
  have hCO : badSet Bb ⊆ (O : Set X) := subset_of_closedFibre I hI O (badSet Bb) hC
    (fun x hx hIx => by
      obtain ⟨y, _, rfl⟩ := mem_of_badSet_closedFibre I hP Bb hBq _ hTc
        (fun V hV => by rw [hBS]; exact hSb V hV) x hx hIx
      rw [← Scheme.Opens.range_ι O]
      exact ⟨y, rfl⟩)
  obtain ⟨T', hT'supp, hT'prop⟩ := ClosedSub.closed_subset_support_proper (A := A) O (badSet Bb) hC hCO
  have hBqc := isQuasicoherent_of_secs_image O hP.1 hE.1 f Bb hBq B hB
  refine ⟨T', hT'prop, ?_⟩
  rw [hT'supp]
  exact cokernel_supportedIn_preimage O hP.1 hE.1 f hf Bb B hBqc hB (badSet Bb)
    (fun U hU hd => GlobalTheory.T.sections_eq_univ_off_bad_support hP.1 Bb hBq U hU hd)

end GlobalTheory.CompanionTheory.GE.PSupp
