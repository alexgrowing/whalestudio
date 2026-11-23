import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem inChart_flagCoord_ratios : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (p' : Cpt ξ') (c₁ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), InChart ξ' (flagCoord κ x φ c) ((c₁, J) : FlagIx κ n r) p' → algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 ∧ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p' ∧ ∀ q : Σ s, Fin (r s), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 ∧ ∀ l j, ((flagMat φ c q.1).submatrix (Function.update (J q) l j) (Fin.castLE q.2.2)).det / ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ∈ regAt ξ' p' := by
  intro Ω _ E _ _ κ x S _ r n φ c X' ξ' p' c₁ J h
  classical
  simp only [InChart] at h ⊢
  obtain ⟨hne, hreg⟩ := h
  have hF : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      flagCoord κ x φ c ((k, J') : FlagIx κ n r) = algebraMap Ω (GenField Ω r) (x k) *
        ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J' q) (Fin.castLE q.2.2)).det :=
    fun _ _ => rfl
  rw [hF] at hne
  have hx : algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 := left_ne_zero_of_mul hne
  have hP : ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 :=
    right_ne_zero_of_mul hne
  refine ⟨hx, ⟨hx, fun k => ?_⟩, fun q => ⟨?_, fun l j => ?_⟩⟩
  · have hq := hreg ((k, J) : FlagIx κ n r)
    rw [hF, hF] at hq
    rwa [mul_div_mul_right _ _ hP] at hq
  · exact (Finset.prod_ne_zero_iff.mp hP) q (Finset.mem_univ q)
  · have hsplit : ∀ J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1),
        ∏ q' : (Σ s, Fin (r s)), ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det =
        ((flagMat φ c q.1).submatrix (J' q) (Fin.castLE q.2.2)).det *
          ∏ q' ∈ Finset.univ.erase q, ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det := by
      intro J'
      rw [← Finset.mul_prod_erase Finset.univ
        (fun q' : (Σ s, Fin (r s)) => ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det)
        (Finset.mem_univ q)]
    have hrest : ∏ q' ∈ Finset.univ.erase q,
          ((flagMat φ c q'.1).submatrix (Function.update J q (Function.update (J q) l j) q')
            (Fin.castLE q'.2.2)).det =
        ∏ q' ∈ Finset.univ.erase q, ((flagMat φ c q'.1).submatrix (J q') (Fin.castLE q'.2.2)).det :=
      Finset.prod_congr rfl fun q' hq' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')]
    have hR : ∏ q' ∈ Finset.univ.erase q,
        ((flagMat φ c q'.1).submatrix (J q') (Fin.castLE q'.2.2)).det ≠ 0 := by
      intro h0
      apply hP
      rw [hsplit J, h0, mul_zero]
    have hq := hreg ((c₁, Function.update J q (Function.update (J q) l j)) : FlagIx κ n r)
    rw [hF, hF, hsplit (Function.update J q (Function.update (J q) l j)), hsplit J, hrest,
      Function.update_self] at hq
    rwa [mul_div_mul_left _ _ hx, mul_div_mul_right _ _ hR] at hq

end GlobalTheory.CompanionTheory.Ar.FlagBun
