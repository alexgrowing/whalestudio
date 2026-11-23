import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThetaRad

theorem mem_unipRad_iff_entries {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, blk e j ≤ blk e i → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨hp, hd⟩ i j hij
    obtain ⟨⟨c, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨d, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    rcases hij.lt_or_eq with hlt | rfl
    · rw [mem_parab_iff.1 hp c d i j hlt, Matrix.one_apply_ne]
      intro hh
      have := congrArg Sigma.fst (e.injective hh)
      exact hlt.ne' this
    · rw [hd]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun c i j => ?_⟩
    · rw [h i j hij.le, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]

theorem blk_stdBlocks_two {a b n : ℕ} (h : ∑ i, ![a, b] i = n) (p : Fin n) :
    blk (stdBlocks ![a, b] h) p = if (p : ℕ) < a then 0 else 1 := by
  obtain ⟨⟨c, i⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
  rw [blk_apply, stdBlocks_val]
  fin_cases c
  · simpa using i.2
  · simp

theorem longElt_conj_apply {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) (i j : Fin n) :
    ((longElt n R * g * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      (g : Matrix (Fin n) (Fin n) R) i.rev j.rev := by
  simp only [longElt, Units.val_mul, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev (fun x _ hx => by rw [if_neg (fun hh => hx (by rw [hh, Fin.rev_rev])), mul_zero]) (by simp)]
  simp

end GlobalTheory.ThetaRad

theorem GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad : ∀ (R : Type) [CommRing R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n) (h' : ∑ i, ![b, a] i = n) (u : GL (Fin n) R), u ∈ unipRad R (stdBlocks ![a, b] h) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipRad R (stdBlocks ![b, a] h') := by
  intro R _ n a b h h' u hu
  have hn : a + b = n := by simpa [Fin.sum_univ_two] using h
  have hv := GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 (inv_mem hu)
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.2 fun i j hij => ?_
  rw [GlobalTheory.ThetaRad.longElt_conj_apply]
  change ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ i.rev j.rev = _
  rw [Matrix.transpose_apply]
  rw [hv j.rev i.rev ?_]
  · simp [Matrix.one_apply, Fin.rev_inj, eq_comm]
  · rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two] at *
    have hi := i.2; have hj := j.2
    simp only [Fin.val_rev] at *
    split_ifs at hij ⊢ <;> first | exact le_refl _ | decide | (exfalso; omega) | (exfalso; revert hij; decide)
