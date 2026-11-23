import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAevalPadicRootsCharpolyEqDet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpolyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_aeval_padicRoots_charpoly_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  first | exact @GlobalTheory.prod_aeval_aroots_padic_eq_det | exact GlobalTheory.prod_aeval_aroots_padic_eq_det | (intros; apply GlobalTheory.prod_aeval_aroots_padic_eq_det <;> assumption)
