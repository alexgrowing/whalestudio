import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem exists_equiv_sigma_blk_lt_iff_lt {N : ℕ} {β : Type} [LinearOrder β] (κ : Fin N → β) :
    ∃ (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N), ∀ p q, blk f p < blk f q ↔ κ p < κ q := by
  classical
  let S : Finset β := Finset.univ.image κ
  let o : Fin S.card ≃o S := S.orderIsoOfFin rfl
  have hS : ∀ p, κ p ∈ S := fun p => Finset.mem_image_of_mem κ (Finset.mem_univ p)
  let g : Fin N → Fin S.card := fun p => o.symm ⟨κ p, hS p⟩
  refine ⟨S.card, fun a => Fintype.card {p // g p = a},
    (Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {p // g p = a}).symm)).trans
      (Equiv.sigmaFiberEquiv g), ?_⟩
  intro p q
  have hb : ∀ x, blk ((Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {p // g p = a}).symm)).trans
      (Equiv.sigmaFiberEquiv g)) x = g x := by
    intro x
    rfl
  rw [hb, hb]
  show o.symm ⟨κ p, hS p⟩ < o.symm ⟨κ q, hS q⟩ ↔ κ p < κ q
  rw [OrderIso.lt_iff_lt]
  exact Subtype.mk_lt_mk

theorem UpperTheory.exists_refinement_block_order :
    ∀ (N : ℕ) (r s : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (j : Fin r) (d' : Fin s → ℕ) (e' : (Σ b, Fin (d' b)) ≃ Fin (d j)),
    ∃ (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N), ∀ p q, blk f p < blk f q ↔ (blk e p < blk e q ∨ ∃ p' q', p = e ⟨j, p'⟩ ∧ q = e ⟨j, q'⟩ ∧ blk e' p' < blk e' q') := by
  intro N r s d e j d' e'
  classical
  obtain ⟨K, hK⟩ : ∃ K : (Σ a, Fin (d a)) → Lex (ℕ × ℕ), ∀ x y, K x < K y ↔
      (x.1 < y.1 ∨ ∃ p' q', x = ⟨j, p'⟩ ∧ y = ⟨j, q'⟩ ∧ blk e' p' < blk e' q') := by
    refine ⟨fun x => toLex ((x.1 : ℕ), if h : x.1 = j then ((blk e' (h ▸ x.2) : Fin s) : ℕ) else 0), ?_⟩
    rintro ⟨a, u⟩ ⟨b, w⟩
    show toLex ((a : ℕ), if h : a = j then ((blk e' (h ▸ u) : Fin s) : ℕ) else 0) <
        toLex ((b : ℕ), if h : b = j then ((blk e' (h ▸ w) : Fin s) : ℕ) else 0) ↔ _
    rw [Prod.Lex.toLex_lt_toLex]
    by_cases ha : a = j <;> by_cases hb : b = j
    · subst ha
      subst hb
      rw [dif_pos rfl, dif_pos rfl]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h (lt_irrefl _)
        · exact Or.inr ⟨u, w, rfl, rfl, Fin.lt_iff_val_lt_val.mpr h⟩
      · rintro (h | ⟨p', q', h1, h2, h3⟩)
        · exact absurd h (lt_irrefl _)
        · refine Or.inr ⟨rfl, ?_⟩
          rw [Sigma.mk.inj_iff] at h1 h2
          rw [eq_of_heq h1.2, eq_of_heq h2.2]
          exact Fin.lt_iff_val_lt_val.mp h3
    · subst ha
      rw [dif_pos rfl, dif_neg hb]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mpr h)
        · exact absurd h (Nat.not_lt_zero _)
      · rintro (h | ⟨p', q', -, h2, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mp h)
        · exact absurd (congrArg Sigma.fst h2) hb
    · subst hb
      rw [dif_neg ha, dif_pos rfl]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mpr h)
        · exact absurd (Fin.ext h) ha
      · rintro (h | ⟨p', q', h1, -, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mp h)
        · exact absurd (congrArg Sigma.fst h1) ha
    · rw [dif_neg ha, dif_neg hb]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mpr h)
        · exact absurd h (lt_irrefl 0)
      · rintro (h | ⟨p', q', h1, -, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mp h)
        · exact absurd (congrArg Sigma.fst h1) ha
  obtain ⟨t, c, f, hf⟩ := exists_equiv_sigma_blk_lt_iff_lt (fun p : Fin N => K (e.symm p))
  refine ⟨t, c, f, fun p q => ?_⟩
  rw [hf, hK]
  simp only [Equiv.symm_apply_eq]
  rfl
