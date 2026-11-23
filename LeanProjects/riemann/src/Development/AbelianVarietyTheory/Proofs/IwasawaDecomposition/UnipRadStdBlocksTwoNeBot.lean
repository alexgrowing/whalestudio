import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open GlobalTheory.SmGL in

theorem unipRad_stdBlocks_two_ne_bot : ∀ (R : Type) [CommRing R] [Nontrivial R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n), 0 < a → 0 < b → unipRad R (stdBlocks ![a, b] h) ≠ ⊥ := by
  intro R _ _ n a b h ha hb
  set e := stdBlocks ![a, b] h with he
  let i : Fin n := e ⟨0, ⟨0, by simpa using ha⟩⟩
  let j : Fin n := e ⟨1, ⟨0, by simpa using hb⟩⟩
  have hij : i ≠ j := by
    intro hh
    have := congrArg Sigma.fst (e.injective hh)
    simp at this
  let g : GL (Fin n) R :=
    ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by
        show Matrix.transvection i j (1 : R) * Matrix.transvection i j (-1) = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp,
      by
        show Matrix.transvection i j (-1 : R) * Matrix.transvection i j 1 = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp⟩
  have hg : (g : Matrix (Fin n) (Fin n) R) = 1 + Matrix.single i j 1 := rfl
  have hmem : g ∈ unipRad R e := by
    rw [mem_unipRad]
    refine ⟨?_, ?_⟩
    · rw [mem_parab]
      intro p q hpq
      have hne : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
      rw [hg, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
      by_cases hp : p = i
      · by_cases hq : q = j
        · subst hp; subst hq
          rw [blk_apply, blk_apply] at hpq
          exact absurd hpq (by decide)
        · rw [Matrix.single_apply, if_neg]
          rintro ⟨_, h'⟩; exact hq h'.symm
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h', _⟩; exact hp h'.symm
    · intro c x y
      rw [hg, Matrix.add_apply]
      have h1 : (1 : Matrix (Fin n) (Fin n) R) (e ⟨c, x⟩) (e ⟨c, y⟩) = (1 : Matrix _ _ R) x y := by
        by_cases hxy : x = y
        · subst hxy; simp
        · rw [Matrix.one_apply_ne, Matrix.one_apply_ne hxy]
          intro hh
          have := e.injective hh
          simp at this
          exact hxy this
      rw [h1]
      have h2 : Matrix.single i j (1 : R) (e ⟨c, x⟩) (e ⟨c, y⟩) = 0 := by
        rw [Matrix.single_apply]
        split_ifs with hh
        · obtain ⟨h3, h4⟩ := hh
          have e3 := congrArg Sigma.fst (e.injective h3)
          have e4 := congrArg Sigma.fst (e.injective h4)
          simp only at e3 e4
          rw [← e3] at e4
          exact absurd e4 (by decide)
        · rfl
      rw [h2, add_zero]
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg (fun u : GL (Fin n) R => (u : Matrix (Fin n) (Fin n) R) i j) hmem
  simp [hg, Matrix.one_apply_ne hij] at this

end GlobalTheory
