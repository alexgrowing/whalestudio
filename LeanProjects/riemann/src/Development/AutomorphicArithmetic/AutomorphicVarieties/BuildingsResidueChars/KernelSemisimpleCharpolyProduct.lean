import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
open Formalism.MainNotions.N

open scoped Matrix in
private theorem ker_pair {Γ K : Type} [Group Γ] [Field K] {a b : ℕ} (ρ : Γ →* GL (Fin a) K)
    (ρ' : Γ →* GL (Fin b) K) (s : Γ) (h : Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' s = 1) : ρ s = 1 ∧ ρ' s = 1 := by
  constructor
  · apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => funext fun i => ?_
    have h1 := GlobalTheory.EigTwist.sumRep_mulVec_inl ρ ρ' s (Sum.elim v 0 ∘ finSumFinEquiv.symm) i
    have e : (Sum.elim v (0 : Fin b → K) ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv ∘ Sum.inl = v := by
      funext j; simp
    rw [h, e, Units.val_one, Matrix.one_mulVec] at h1
    simpa using h1.symm
  · apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => funext fun i => ?_
    have h1 := GlobalTheory.EigTwist.sumRep_mulVec_inr ρ ρ' s (Sum.elim 0 v ∘ finSumFinEquiv.symm) i
    have e : (Sum.elim (0 : Fin a → K) v ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv ∘ Sum.inr = v := by
      funext j; simp
    rw [h, e, Units.val_one, Matrix.one_mulVec] at h1
    simpa using h1.symm

private theorem ker_sumL {Γ K : Type} [Group Γ] [Field K] (s : Γ) :
    ∀ L : List (Σ m : ℕ, Γ →* GL (Fin m) K), (GlobalTheory.EigTwist.sumL L).2 s = 1 → ∀ p ∈ L, p.2 s = 1
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: L, h, p, hp => by
    obtain ⟨h1, h2⟩ := ker_pair q.2 (GlobalTheory.EigTwist.sumL L).2 s h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h1
    · exact ker_sumL s L h2 p hp

private theorem ker_transfer {Γ K : Type} [Group Γ] [Field K] {n m : ℕ} (ρ : Γ →* GL (Fin n) K)
    (σ : Γ →* GL (Fin m) K) (hρ : IsSSRep ρ) (hσ : IsSSRep σ)
    (hc : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly) (s : Γ) (h : ρ s = 1) : σ s = 1 := by
  have hnm : n = m := by
    have h1 := congrArg Polynomial.natDegree (hc 1)
    rwa [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Fintype.card_fin] at h1
  subst hnm
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ σ hρ hσ hc
  have h1 := hP s
  rw [h] at h1
  simpa using h1

theorem UpperTheory.kernel_semisimple_charpoly_product :
    ∀ (Γ k : Type) [Group Γ] [Field k] (n c : ℕ) (a : Fin c → ℕ) (ρ : Γ →* GL (Fin n) k) (r : ∀ i, Γ →* GL (Fin (a i)) k), IsSSRep ρ → (∀ i, IsSSRep (r i)) → (∀ g, (ρ g : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (r i g : Matrix (Fin (a i)) (Fin (a i)) k).charpoly) → ∀ s, ρ s = 1 → ∀ i, r i s = 1 := by
  intro Γ k _ _ n c a ρ r hρ hr hc s hs i
  let L : List (Σ m : ℕ, Γ →* GL (Fin m) k) := List.ofFn fun j => ⟨a j, r j⟩
  have hL : ∀ p ∈ L, IsSSRep p.2 := by
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hp
    exact hr j
  have hS := GlobalTheory.EigTwist.isSSRep_sumL L hL
  have h1 := ker_transfer ρ (GlobalTheory.EigTwist.sumL L).2 hρ hS (fun g => by
    rw [hc g, GlobalTheory.EigTwist.charpoly_sumL L g, List.map_ofFn, List.prod_ofFn]; rfl) s hs
  exact ker_sumL s L h1 ⟨a i, r i⟩ (List.mem_ofFn.2 ⟨i, rfl⟩)
