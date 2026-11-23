import Development.EtaleCohomology.TateTwists.CupGradedCommOfFlip

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def CupflipSteen (h : ∀ N, Pr N →₀ ℤ) : Prop :=
  (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧
    ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1)

def cupflip_steen : Prop := ∃ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h

def cupflip_homotopy : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (hk' : m + n = k)
      (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → ν.IsAW hk' β.1 α.1 γ'.1 →
        ∃ η : Cochain ((chains R).obj E) K (k - 1), δ (k - 1) k η = γ.1 - (n * m).negOnePow • γ'.1

theorem cupflip_aw_flip_of (hst : cupflip_steen) (hho : cupflip_homotopy) : cupflip_aw_flip := by
  intro R _ I J K μ ν hflip E n m k h h' α β γ γ' hγ hγ'
  obtain ⟨s, hs⟩ := hst
  obtain ⟨η, hη⟩ := hho s hs R μ ν hflip E h h' α β γ γ' hγ hγ'
  rcases Int.units_eq_one_or ((n * m).negOnePow) with he | he
  · rw [he, one_smul] at hη ⊢
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (k - 1) (by omega)]
    exact ⟨η, hη⟩
  · rw [he, Units.neg_smul, one_smul] at hη ⊢
    rw [← sub_eq_zero, sub_neg_eq_add, ← CohomologyClass.mk_add, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (k - 1) (by omega)]
    exact ⟨η, by rw [hη, sub_neg_eq_add]; rfl⟩

end LateralTheory.EtaleFoundations
