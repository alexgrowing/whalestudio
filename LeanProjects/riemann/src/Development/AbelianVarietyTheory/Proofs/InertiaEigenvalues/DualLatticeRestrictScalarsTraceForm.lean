import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualLatDescent

theorem dualLat_resQ : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')),
    (∀ v, v ∈ LZ.T ↔ v ∈ L.T) → (∀ v, v ∈ LZ'.T ↔ v ∈ L'.T) →
    ∀ (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x y, PQ x y = lam (Pr x y)) → IsDualLat1 (P.PD K) L L' Pr →
    IsDualLat1 (P.PD K) LZ LZ' PQ := by
  intro l _ P K LL _ _ O _ _ V _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ _ _ lam n e f h1 h2 h3 ρ ρ' L L' LZ LZ' hT hT' Pr PQ hPQ hP
  obtain ⟨⟨hg, hl, hr, hrk⟩, hlat⟩ := hP

  have key : ∀ z : LL, (∀ a : LL, lam (a * z) = 0) → z = 0 := by
    intro z hz
    rw [h3 z]
    simp [hz]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g x y
    rw [hPQ, GlobalTheory.PstCoeff.resQ_apply, GlobalTheory.PstCoeff.resQ_apply, hg, hPQ]
    have : ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap ℚ_[l] LL ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) := by
      simp [cycLL]
    rw [this, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro x hx
    apply hl
    intro y
    apply key
    intro a
    rw [← smul_eq_mul, ← map_smul, ← hPQ]
    exact hx _
  · intro y hy
    apply hr
    intro x
    apply key
    intro a
    rw [← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, ← hPQ]
    exact hy _
  · rw [← Module.finrank_mul_finrank ℚ_[l] LL V, ← Module.finrank_mul_finrank ℚ_[l] LL V', hrk]
  · intro y
    rw [hT', hlat]
    constructor
    · intro H x hx
      obtain ⟨a, ha⟩ := H x ((hT x).1 hx)
      obtain ⟨z, hz⟩ := h2 a
      exact ⟨z, by rw [hPQ, ha, hz]; rfl⟩
    · intro H x hx
      have hi : ∀ i, ∃ z : ℤ_[l], lam (algebraMap O LL (f i) * Pr x y) = (z : ℚ_[l]) := by
        intro i
        have hm : f i • x ∈ L.T := L.T.smul_mem _ hx
        obtain ⟨z, hz⟩ := H _ ((hT _).2 hm)
        refine ⟨z, ?_⟩
        rw [hPQ, ← algebraMap_smul LL (f i) x, map_smul, LinearMap.smul_apply, smul_eq_mul] at hz
        rw [hz]; rfl
      choose z hz using hi
      have ho : ∀ i, ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z i : ℚ_[l]) := fun i => h1 (z i)
      choose o ho using ho
      refine ⟨∑ i, o i * e i, ?_⟩
      rw [h3 (Pr x y), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i, map_mul, ho i, Algebra.smul_def]

end GlobalTheory.DualLatDescent
