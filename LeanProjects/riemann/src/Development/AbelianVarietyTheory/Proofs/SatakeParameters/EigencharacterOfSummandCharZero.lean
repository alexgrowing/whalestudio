import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.EigTwist

open scoped Matrix

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

def sumL (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) : Σ m : ℕ, Γ →* GL (Fin m) K :=
  L.foldr (fun p s => ⟨p.1 + s.1, Formalism.MainNotions.SumRepresentations.At.sumRep p.2 s.2⟩) ⟨0, 1⟩

theorem isSSRep_sumL : ∀ L : List (Σ m : ℕ, Γ →* GL (Fin m) K), (∀ p ∈ L, IsSSRep p.2) →
    IsSSRep (sumL L).2
  | [], _ => GlobalTheory.BCGal.ss_zero _
  | p :: L, h => GlobalTheory.BCGal.ss_sumRep _ _ (h p List.mem_cons_self)
      (isSSRep_sumL L fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem charpoly_sumRep {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K).charpoly =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K).charpoly *
        ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K).charpoly := by
  rw [GlobalTheory.BCGal.sumRep_val, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]

theorem charpoly_sumL : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ),
    (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly =
      (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod
  | [], g => by
    rw [List.map_nil, List.prod_nil]
    exact Polynomial.eq_one_of_monic_natDegree_zero (Matrix.charpoly_monic _)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; rfl)
  | p :: L, g => by
    rw [List.map_cons, List.prod_cons, ← charpoly_sumL L g]
    exact charpoly_sumRep p.2 (sumL L).2 g

theorem sumRep_mulVec_inl {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (i : Fin a) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inl i)) =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inl)) i := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem sumRep_mulVec_inr {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (j : Fin b) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inr j)) =
      (((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inr)) j := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem eigen_pair (χ : Γ →* Kˣ) {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K)
    (w : Fin (a + b) → K) (hw : w ≠ 0)
    (he : ∀ g, ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) :
    (∃ v : Fin a → K, v ≠ 0 ∧ ∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ v = ((χ g : Kˣ) : K) • v) ∨
    (∃ v : Fin b → K, v ≠ 0 ∧ ∀ g, ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ v = ((χ g : Kˣ) : K) • v) := by
  by_cases h1 : w ∘ finSumFinEquiv ∘ Sum.inl = 0
  · right
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inr, fun h2 => hw ?_, fun g => ?_⟩
    · funext j
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
      rcases s with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
    · funext j
      have h3 := congrFun (he g) (finSumFinEquiv (Sum.inr j))
      rw [sumRep_mulVec_inr] at h3
      rw [h3]
      simp
  · left
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inl, h1, fun g => ?_⟩
    funext i
    have h3 := congrFun (he g) (finSumFinEquiv (Sum.inl i))
    rw [sumRep_mulVec_inl] at h3
    rw [h3]
    simp

theorem eigen_sumL (χ : Γ →* Kˣ) : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (w : Fin (sumL L).1 → K),
    w ≠ 0 → (∀ g, (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) →
    ∃ p ∈ L, ∃ v : Fin p.1 → K, v ≠ 0 ∧
      ∀ g, ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K) *ᵥ v = ((χ g : Kˣ) : K) • v
  | [], w, hw, _ => (hw (funext fun i => (Nat.not_lt_zero _ i.2).elim)).elim
  | p :: L, w, hw, he => by
    rcases eigen_pair χ p.2 (sumL L).2 w hw he with ⟨v, hv0, hv⟩ | ⟨v, hv0, hv⟩
    · exact ⟨p, List.mem_cons_self, v, hv0, hv⟩
    · obtain ⟨q, hq, u, hu0, hu⟩ := eigen_sumL χ L v hv0 hv
      exact ⟨q, List.mem_cons_of_mem _ hq, u, hu0, hu⟩

theorem eigen_transfer {n m : ℕ} (ρ : Γ →* GL (Fin n) K) (σ : Γ →* GL (Fin m) K) (hρ : IsSSRep ρ)
    (hσ : IsSSRep σ)
    (hc : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly)
    (χ : Γ →* Kˣ) (v : Fin n → K) (hv0 : v ≠ 0)
    (hv : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v = ((χ g : Kˣ) : K) • v) :
    ∃ w : Fin m → K, w ≠ 0 ∧ ∀ g, ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K) *ᵥ w = ((χ g : Kˣ) : K) • w := by
  have hnm : n = m := by
    have h1 := congrArg Polynomial.natDegree (hc 1)
    rwa [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Fintype.card_fin] at h1
  subst hnm
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ σ hρ hσ hc
  refine ⟨((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v, fun h0 => hv0 ?_, fun g => ?_⟩
  · have h1 := congrArg (fun u => ((P : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ u) h0
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
  · rw [Matrix.mulVec_mulVec, hP g]
    have e : ((P⁻¹ * ρ g * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) =
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) * ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [e, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]

end GlobalTheory.EigTwist

open GlobalTheory.EigTwist in

theorem GlobalTheory.eigenCharTwist_holds : EigenCharTwist := by
  intro K _ _ Γ _ n ρ L χ hρ hL hc hv
  obtain ⟨v, hv0, hv⟩ := hv
  have hS := isSSRep_sumL L hL
  have hcS : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly :=
    fun g => (hc g).trans (charpoly_sumL L g).symm
  obtain ⟨w, hw0, hw⟩ := eigen_transfer ρ (sumL L).2 hρ hS hcS χ v hv0 hv
  exact eigen_sumL χ L w hw0 hw
