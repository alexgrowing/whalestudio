import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomConnectedFactorThroughPart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEt
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearHom_connected_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  first | exact @GlobalTheory.PDivGroup.semiHom_app_eq_conn_part | exact GlobalTheory.PDivGroup.semiHom_app_eq_conn_part | (intros; apply GlobalTheory.PDivGroup.semiHom_app_eq_conn_part <;> assumption)
