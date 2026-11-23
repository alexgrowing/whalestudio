import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMixedTsub
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PrismaticFilteredAtOfIntegersAt

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem existsUnique_padic_of_eigen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O,
      WittVector.frobenius a = WittVector.frobenius (xi ε) * a →
        ∃! c : ℤ_[p], ofPadic p O c * Sandwich.mu ε = a := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha
  have h1 : IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p := by
    simpa [zeta] using hε 1
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsDomain (Ainf p O) := GlobalTheory.Sandwich.Model.isDomain_Ainf hv
  have hμ : Sandwich.mu ε ≠ 0 := GlobalTheory.Sandwich.Model.mu_ne_zero (hε := h1) hv
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.Ar.Prism.exists_padic_of_eigen h1 ha
  have hinj : Function.Injective (ofPadic p O) :=
    (WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective
  exact ⟨c, hc, fun c' hc' => hinj (mul_right_cancel₀ hμ (hc'.trans hc.symm))⟩

end GlobalTheory.PDivLat
