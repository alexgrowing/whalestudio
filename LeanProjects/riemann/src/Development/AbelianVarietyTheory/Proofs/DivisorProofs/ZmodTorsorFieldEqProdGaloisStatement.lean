import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorFieldEqProdGalois
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_field_eq_prod_galois : ∀ (K M : Type) [Field K] [CommRing M] [Algebra K M] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)), 0 < q →
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)),
      (∀ i, FiniteDimensional K (L i)) ∧ (∀ i, IsGalois K (L i)) ∧
      (∀ i, Module.finrank K (L i) ∣ q) ∧ Nonempty (M ≃ₐ[K] ∀ i, L i) := by
  first | (exact @GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (exact GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (intros; apply GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois  <;> assumption)
