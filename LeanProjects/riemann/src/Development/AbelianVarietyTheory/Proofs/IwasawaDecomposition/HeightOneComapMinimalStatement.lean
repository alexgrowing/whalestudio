import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightOneComapMinimal
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_comap_minimal : ∀ {A B R : Type} [CommRing A] [IsDomain A] [CommRing B] [IsNoetherianRing B] [CommRing R] [IsNoetherianRing R] (ι : A →+* B) (ψ : B →+* R), ι.Flat → ψ.Flat → ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap (ψ.comp ι) ≠ ⊥ → ∀ P : Ideal B, P.IsPrime → (Q.comap (ψ.comp ι)).map ι ≤ P → P ≤ Q.comap ψ → P = Q.comap ψ := by
  first | exact @GlobalTheory.comap_eq_of_height_one_of_flat | exact GlobalTheory.comap_eq_of_height_one_of_flat | (intros; apply GlobalTheory.comap_eq_of_height_one_of_flat <;> assumption)
