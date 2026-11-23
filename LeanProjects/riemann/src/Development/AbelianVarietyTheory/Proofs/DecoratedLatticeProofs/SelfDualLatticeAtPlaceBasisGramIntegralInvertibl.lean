import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.IwaPlace.GramBasis

variable {D : D7} {S : HSp D}

def cv {n : ℕ} (y : Fin n → AE D) : Fin n → AE D := fun i => cA D (y i)

theorem hermAt_eq (x y : Fin S.rank → AE D) : hermAt S x y = cv y ⬝ᵥ (gA S *ᵥ x) := by
  unfold hermAt cv
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cv_mulVec {m : ℕ} (N : Matrix (Fin S.rank) (Fin m) (AE D)) (b : Fin m → AE D) :
    cv (N *ᵥ b) = vecMul (cv b) (adj N) := by
  funext i
  simp only [cv, mulVec, vecMul, dotProduct, map_sum, map_mul, adj, transpose_apply, map_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem hermAt_mulVec {m n : ℕ} (M : Matrix (Fin S.rank) (Fin m) (AE D)) (a : Fin m → AE D)
    (N : Matrix (Fin S.rank) (Fin n) (AE D)) (b : Fin n → AE D) :
    hermAt S (M *ᵥ a) (N *ᵥ b) = cv b ⬝ᵥ ((adj N * (gA S * M)) *ᵥ a) := by
  rw [hermAt_eq, cv_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem cv_single {n : ℕ} (i : Fin n) : cv (Pi.single i (1 : AE D)) = Pi.single i 1 := by
  funext k
  by_cases h : k = i
  · subst h; simp [cv]
  · simp [cv, Pi.single_eq_of_ne h]

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (i : Fin m) (j : Fin n) :
    (M *ᵥ Pi.single j (1 : AE D)) i = M i j := by
  rw [mulVec_single_one]; rfl

theorem gram_basis : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D)), ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → (∀ i j, β i j ∈ idAt D (· = v)) → (∀ i j, β' i j ∈ idAt D (· = v)) → β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) → (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v ε Λ β β' hεε hcε hε hact hΛ hβ hβ' h1 h2 hmem
  have h0 : (0 : AE D) ∈ intAt D (· = v) := ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
  have hcs : ∀ j k, (β *ᵥ Pi.single j (1 : AE D)) k ∈ idAt D (· = v) := fun j k => by
    rw [mulVec_single_apply]; exact hβ k j
  have hcol : ∀ j, β *ᵥ Pi.single j (1 : AE D) ∈ Λ := fun j => (hmem _ (hcs j)).2 fun i => by
    rw [mulVec_mulVec, mulVec_single_apply, h2, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs
    · rw [mul_one]; exact hε
    · rw [mul_zero]; exact h0
  have hadj : adj β * adj β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [← adj_mul, h2, adj_smul, adj_one, hcε]
  have hz : adj β * (gA S * (giA S * adj β')) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [gA_giA_cancel, hadj]
  refine ⟨fun i j => ?_, fun i j => ?_, β' * (giA S * adj β'), fun i j => ?_, ?_⟩
  · have h := (hΛ.2.2 _ (hcs j)).1 (hcol j) _ (hcol i)
    rwa [hermAt_mulVec, cv_single, single_dotProduct, one_mul, mulVec_single_apply] at h
  · have h : adj (adj β * (gA S * β)) = adj β * (gA S * β) := by
      rw [adj_mul, adj_mul, adj_gA, adj_adj, Matrix.mul_assoc]
    exact congrFun (congrFun h j) i
  · have hs : ∀ k, ((giA S * adj β') *ᵥ Pi.single j (1 : AE D)) k ∈ idAt D (· = v) := fun k => by
      rw [← mulVec_mulVec]
      refine mulVec_mem_idAt _ (fun l => ?_) k
      rw [mulVec_single_apply]
      change cA D (β' j l) ∈ _
      rw [← (hact _).1 (hβ' j l), RingHom.map_mul, hcε]
      exact Ideal.mul_mem_right _ _ hε.1
    have hin : (giA S * adj β') *ᵥ Pi.single j (1 : AE D) ∈ Λ := (hΛ.2.2 _ hs).2 fun x hx => by
      refine ⟨LocSD.hermAt_mem_idAt hs x, ?_⟩
      have hw := (hmem x (hΛ.1 x hx)).1 hx j
      have e : x = β *ᵥ (β' *ᵥ x) := by
        rw [mulVec_mulVec, h1, smul_mulVec, one_mulVec]
        funext k
        exact ((hact _).1 (hΛ.1 x hx k)).symm
      rw [e, hermAt_mulVec, hz, smul_mulVec, one_mulVec, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul,
        RingHom.map_mul]
      exact FrameLat.mul_mem_intAE hε.2 ((FrameLat.cA_int_iff _).2 hw.2)
    have h := (hmem _ hs).1 hin i
    rwa [mulVec_mulVec, mulVec_single_apply] at h
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc β, h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_smul, hz, smul_smul, hεε]

end GlobalTheory.IwaPlace.GramBasis

end
