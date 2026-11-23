import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRestrictedProductEqProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerRestrictedProductIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalTermEqFinprodLocalTermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermDoubleCosetInvariStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermOneUnramifiedStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

theorem twOrb_restr_eq_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v, {q : DoubleCoset.Quotient (twCent (θv v) (pf v δ) : Set (Y v)) (K v : Set (Y v)) | ∃ k ∈ K v, fv v ((Quotient.out q * k)⁻¹ * pf v δ * θv v (Quotient.out q * k)) ≠ 0}.Finite) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v ∧ ∀ y, y⁻¹ * pf v δ * θv v y ∈ K v → ∃ t ∈ twCent (θv v) (pf v δ), ∃ k ∈ K v, y = t * k) → twOrb θ (⨅ v, (K v).comap (pf v)) δ f = ∏ᶠ v, twOrb (θv v) (K v) (pf v δ) (fv v) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX θ θv hθ hθK δ f fv hf hcomm hidx hfin hcpt hev
  rw [GlobalTheory.EulerAbs.twOrb_eq_finsum_twTerm]
  simp only [GlobalTheory.EulerAbs.twOrb_eq_finsum_twTerm]
  exact GlobalTheory.T.finsum_doubleCoset_restrictedProduct_eq_prod pf K hX (twCent θ δ) (fun v => twCent (θv v) (pf v δ)) (GlobalTheory.T.mem_twistedCentralizer_restrictedProduct_iff pf K hX θ θv hθ δ) _ _
    (GlobalTheory.T.twistedOrbitalTerm_eq_finprod_localTerms pf K hX θ θv hθ hθK δ f fv hf hcomm hidx hcpt (hev.mono fun v h => ⟨h.1, h.2.1, h.2.2.1⟩))
    (fun v t ht y k hk => GlobalTheory.T.twistedOrbitalIntegralPointTerm_doubleCoset_invariant _ _ _ _ (hcomm v) (hidx v) t ht y k hk)
    (fun v => (hfin v).subset fun q hq => GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero _ _ _ _ _ hq)
    (hev.mono fun v h => ⟨by rw [h.1]; exact GlobalTheory.T.twistedOrbitalIntegralPointTerm_one_unramified _ _ _ (hθK v) h.2.1 h.2.2.1, fun y hy => by
        obtain ⟨k, hk, hne⟩ := GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero _ _ _ _ _ hy
        rw [h.1] at hne
        have hm : (y * k)⁻¹ * pf v δ * θv v (y * k) ∈ K v := by
          by_contra hc; exact hne (Set.indicator_of_notMem hc _)
        obtain ⟨t, ht, k', hk', he⟩ := h.2.2.2 (y * k) hm
        exact ⟨t, ht, k' * k⁻¹, mul_mem hk' (inv_mem hk), by rw [← mul_assoc, ← he, mul_inv_cancel_right]⟩⟩)

end GlobalTheory.EulerAbs
