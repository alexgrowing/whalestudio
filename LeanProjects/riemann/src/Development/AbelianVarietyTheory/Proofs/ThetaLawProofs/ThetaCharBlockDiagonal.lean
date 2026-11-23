import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix

noncomputable section

open Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaPow

variable {j g G : ℕ}

theorem dotProduct_blocks {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G) (x y : Fin G → R) :
    x ⬝ᵥ y = ∑ i : Fin j, (fun k => x (e (i, k))) ⬝ᵥ (fun k => y (e (i, k))) := by
  unfold dotProduct
  rw [← e.sum_comp, Fintype.sum_prod_type]

theorem mulVec_blocks {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) (y : Fin G → R) (i : Fin j) :
    (fun k => ((Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) *ᵥ y) (e (i, k))) =
      M *ᵥ fun k => y (e (i, k)) := by
  funext k
  simp only [mulVec, dotProduct, of_apply]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

theorem posDef_blocks (e : Fin j × Fin g ≃ Fin G) {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.PosDef) :
    (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) ℝ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
  · ext p q
    have h := hM.1.apply (e.symm p).2 (e.symm q).2
    simp only [conjTranspose_apply, of_apply, star_trivial] at h ⊢
    by_cases hpq : (e.symm p).1 = (e.symm q).1
    · rw [if_pos hpq, if_pos hpq.symm, h]
    · rw [if_neg hpq, if_neg (Ne.symm hpq)]
  · rw [dotProduct_blocks e]
    simp only [mulVec_blocks]
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun i _ => ?_) ⟨(e.symm p).1, Finset.mem_univ _, ?_⟩
    · exact hM.posSemidef.dotProduct_mulVec_nonneg _
    · refine (posDef_iff_dotProduct_mulVec.1 hM).2 (x := fun k => x (e ((e.symm p).1, k))) ?_
      refine Function.ne_iff.2 ⟨(e.symm p).2, ?_⟩
      simpa using hp

def blockEquiv (e : Fin j × Fin g ≃ Fin G) : (Fin G → ℤ) ≃ (Fin j → Fin g → ℤ) :=
  (Equiv.arrowCongr e.symm (Equiv.refl ℤ)).trans (Equiv.curry _ _ _)

theorem blockEquiv_apply (e : Fin j × Fin g ≃ Fin G) (m : Fin G → ℤ) (i : Fin j) (k : Fin g) :
    blockEquiv e m i k = m (e (i, k)) := rfl

theorem thTerm_blocks (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin G → ℂ) (m : Fin G → ℤ) :
    CanTh.thTerm (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        τ (e.symm p).2 (e.symm q).2 else 0) (fun p => a (e.symm p).2) (fun p => b (e.symm p).2) z m =
      ∏ i : Fin j, CanTh.thTerm τ a b (fun k => z (e (i, k))) (blockEquiv e m i) := by
  unfold CanTh.thTerm
  rw [← Complex.exp_sum, dotProduct_blocks e, dotProduct_blocks e (y := z + _), Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_blocks]
  simp only [Pi.add_def, Equiv.symm_apply_apply, blockEquiv_apply]

end GlobalTheory.ThetaPow

namespace GlobalTheory

open ThetaPow in

theorem thetaChar_blockDiagonal (j g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (G : ℕ)
    (e : Fin j × Fin g ≃ Fin G) (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    let τ' : Matrix (Fin G) (Fin G) ℂ := Matrix.of fun p q =>
      if (e.symm p).1 = (e.symm q).1 then τ (e.symm p).2 (e.symm q).2 else 0
    τ'.IsSymm ∧ (τ'.map Complex.im).PosDef ∧ ∀ z : Fin G → ℂ,
      thetaChar τ' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) z =
        ∏ i : Fin j, thetaChar τ (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) (fun k => z (e (i, k))) := by
  intro τ'
  refine ⟨?_, ?_, fun z => ?_⟩
  · ext p q
    simp only [τ', transpose_apply, of_apply]
    by_cases hpq : (e.symm p).1 = (e.symm q).1
    · rw [if_pos hpq, if_pos hpq.symm, hs.apply]
    · rw [if_neg hpq, if_neg (Ne.symm hpq)]
  · convert posDef_blocks e hp using 1
    ext p q
    simp only [τ', map_apply, of_apply]
    split_ifs <;> simp
  · rw [CanTh.thetaChar_eq_tsum τ' (fun p => a (e.symm p).2) (fun p => b (e.symm p).2) z]
    simp only [τ', thTerm_blocks]
    rw [(blockEquiv e).tsum_eq
      (fun m => ∏ i : Fin j, CanTh.thTerm τ a b (fun k => z (e (i, k))) (m i))]
    exact (CanTh.hasSum_prod_thTerm (τ := fun _ : Fin j => τ) (fun _ => CanTh.mem_thetaDomain hp)
      (fun _ => a) (fun _ => b) (fun i k => z (e (i, k)))).tsum_eq

end GlobalTheory
