import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitution
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_polynomial_substitution : ∀ {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : A) (f : A →+* R) (n : N → R) {d : ℕ} (e : Fin (d + 1) ≃ Option N), (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t)).Etale → Function.Bijective (MvPolynomial.eval₂Hom f n) → (MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n)).Etale := by
  first | exact @GlobalTheory.etale_eval₂Hom_option_of_bijective | exact GlobalTheory.etale_eval₂Hom_option_of_bijective | (intros; apply GlobalTheory.etale_eval₂Hom_option_of_bijective <;> assumption)
