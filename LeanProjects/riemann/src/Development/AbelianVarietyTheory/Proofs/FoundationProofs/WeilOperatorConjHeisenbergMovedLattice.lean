import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelicStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.WeilEquiv

theorem exists_common_den {R : Type} [CommRing R] (O : Subring R)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, (n : R) * A i j ∈ O := by
  choose f hf hfO using hO
  refine ⟨∏ p : Fin a × Fin b, f (A p.1 p.2), Finset.prod_pos fun p _ => hf _, fun i j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
  exact O.mul_mem (natCast_mem O _) (hfO _)

theorem exists_close {R E : Type} [CommRing R] (ι : E → R) (O : Subring R) (I : AddSubgroup R)
    (hA : ∀ (y : R) (m : ℕ), 0 < m → ∃ e : E, ∃ t ∈ I, ι e - y = (m : R) * t)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) (hI : ∀ s ∈ O, ∀ t ∈ I, s * t ∈ I)
    {a b : ℕ} (X : Matrix (Fin a) (Fin b) R) (P : Matrix (Fin a) (Fin a) R) (Q : Matrix (Fin b) (Fin b) R)
    (hX : ∀ i j, (P * X * Q) i j ∈ I) (m : ℕ) (hm : 0 < m) :
    ∃ z : Matrix (Fin a) (Fin b) E, (∀ i j, ∃ y ∈ I, (z.map ι - X) i j = (m : R) * y) ∧
      ∀ i j, (P * z.map ι * Q) i j ∈ I := by
  obtain ⟨n, hn, hP⟩ := exists_common_den O hO P
  obtain ⟨n', hn', hQ⟩ := exists_common_den O hO Q
  choose e t ht he using fun i j => hA (X i j) (m * n * n') (by positivity)
  refine ⟨Matrix.of e, fun i j => ⟨((n * n' : ℕ) : R) * t i j, hI _ (natCast_mem O _) _ (ht i j), ?_⟩, fun i j => ?_⟩
  · simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, he]
    push_cast; ring
  · have h1 : (Matrix.of e).map ι = X + Matrix.of fun i j => ((m * n * n' : ℕ) : R) * t i j := by
      ext i j
      simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, ← he]
      ring
    rw [h1, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    refine I.add_mem (hX i j) ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    refine sum_mem fun l _ => sum_mem fun r _ => ?_
    have : P i r * (((m * n * n' : ℕ) : R) * t r l) * Q l j =
        ((m : R) * ((n : R) * P i r) * ((n' : R) * Q l j)) * t r l := by
      push_cast; ring
    rw [this]
    exact hI _ (O.mul_mem (O.mul_mem (natCast_mem O _) (hP i r)) (hQ l j)) _ (ht r l)

theorem om_wd_moved : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (k : GL (Fin N) (AE D)) L₁ → Moves D (k' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ x' ∈ La D (tor0 D cc δ) L₂ L₂', W.Om h h' (Wd D (tor0 D cc δ) x F) = Wd D (tor0 D cc δ) x' (W.Om h h' F) := by
  intro D hD cc δ hcc N N' e0 W h k h' k' L₁ L₂ L₁' L₂' h1 h1' h2 h2' x hx F hF
  obtain ⟨z, rfl, hz⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hD cc δ hcc N N' k k' L₁ L₁' h1 h1' x hx
  obtain ⟨m, hm, hl⟩ := W.lift h h' z F hF
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  obtain ⟨z', hc, hz'⟩ := exists_close (inc D) (OhE D) (IhE D cc) hA hO hI
    (((h' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (((h : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)))
    (((((h' * k' : GA D N') : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)))
    (((h * k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    (by
      intro i j
      refine Set.mem_of_eq_of_mem (congrFun (congrFun ?_ i) j) (hz i j)
      simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((h' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)),
        ← Matrix.mul_assoc (((h : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)),
        Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.one_mul]) m hm
  exact ⟨_, GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D hD cc δ hcc N N' (h * k) (h' * k') L₂ L₂' h2 h2' z' hz', hl z' hc⟩

end GlobalTheory.WeilEquiv
