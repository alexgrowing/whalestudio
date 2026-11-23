import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_quot_kerIdeal_succ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G Q : PDivGroup p k)
    (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (h : q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G) (hmn : m ≤ n) :
    Module.finrank k (G.A (n + 1) ⧸ kerIdeal (q.app (n + 1))) =
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) := by
  have h1 : Hom.app (q ≫ q') (n + 1) = mulBy k (G.A (n + 1)) (p ^ m) := by
    rw [h, ← Nat.cast_pow, natCast_smul_id_app]
  have h2 : torsionIdeal k (G.A (n + 1)) (p ^ m) ≤ kerIdeal (q.app (n + 1)) := by
    rw [torsionIdeal, ← h1, comp_app, kerIdeal_comp]
    refine Ideal.map_mono ((kerIdeal_le_ker_iff _ (counitAlgHom k _)).2 fun c => ?_)
    simp
  have h3 : RingHom.ker (G.res n : G.A (n + 1) →ₐ[k] G.A n) ≤ kerIdeal (q.app (n + 1)) :=
    (G.ker_res n).le.trans ((torsionIdeal_le_of_dvd (pow_dvd_pow p hmn)).trans h2)
  have h4 : Ideal.map (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app (n + 1))) =
      kerIdeal (q.app n) := by
    rw [← kerIdeal_comp, q.comm n, kerIdeal_comp_of_surjective _ (Q.res_surjective n)]
  have hs : Function.Surjective (G.res n : G.A (n + 1) →ₐ[k] G.A n) := G.res_surjective n
  have hc : Ideal.comap (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app n)) =
      kerIdeal (q.app (n + 1)) := by
    rw [← h4, Ideal.comap_map_of_surjective _ hs, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 h3
  let e := Ideal.quotientMapₐ (kerIdeal (q.app n)) (G.res n : G.A (n + 1) →ₐ[k] G.A n) hc.ge
  have he : Function.Bijective e :=
    ⟨Ideal.quotientMap_injective' (H := hc.ge) hc.le, Ideal.quotientMap_surjective (H := hc.ge) hs⟩
  exact (AlgEquiv.ofBijective e he).toLinearEquiv.finrank_eq

theorem finrank_quot_kerIdeal_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q : PDivGroup p k) (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → m ≤ n →
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) = Module.finrank k (G.A m ⧸ kerIdeal (q.app m)) := by
  intro p _ k _ _ G Q m n q q' h hmn
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih => exact (finrank_quot_kerIdeal_succ p k G Q m n q q' h hmn).trans ih

end GlobalTheory.Dieu
