import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.MinorGen

theorem sum_castLE {M : Type*} [AddCommMonoid M] {n i : ℕ} (h : i ≤ n) (F : Fin n → M)
    (hF : ∀ b : Fin n, i ≤ (b : ℕ) → F b = 0) : ∑ b, F b = ∑ j : Fin i, F (Fin.castLE h j) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb h))), Finset.sum_map]
  · rfl
  · intro b _ hb
    apply hF
    by_contra hlt
    push_neg at hlt
    exact hb (Finset.mem_map.2 ⟨⟨b, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem prod_castLE {M : Type*} [CommMonoid M] {n i : ℕ} (h : i ≤ n) (F : Fin n → M) :
    ∏ b : Fin n, (if (b : ℕ) < i then F b else 1) = ∏ j : Fin i, F (Fin.castLE h j) := by
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb h))), Finset.prod_map]
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp [Fin.castLEEmb, j.2]
  · intro b _ hb
    rw [if_neg]
    intro hlt
    exact hb (Finset.mem_map.2 ⟨⟨b, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem isEqn_sum_ite {X : Scheme.{0}} [IsIntegral X] (y : X) {n : ℕ} (i : ℕ) (Δ : Fin n → CartierDiv X)
    (t : Fin n → X.functionFieldˣ) (hΔ : ∀ a, (Δ a).IsEqn y (t a)) (s : Finset (Fin n)) :
    (∑ a ∈ s, if (a : ℕ) < i then Δ a else 0).IsEqn y (∏ a ∈ s, if (a : ℕ) < i then t a else 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine CartierDiv.IsEqn.add ?_ ih
    split_ifs
    · exact hΔ a
    · exact CartierDiv.isEqn_zero y

theorem exists_minor_generatesAt : ∀ (X : Scheme.{0}) [IsIntegral X] (y : X) (n : ℕ) (i : Fin n) (Δ : Fin n → GlobalTheory.Cartier.CartierDiv X) (t : Fin n → X.functionFieldˣ) (T : Matrix (Fin n) (Fin n) X.functionField) (By : Matrix (Fin n) (Fin n) (X.presheaf.stalk y)), (∀ a, (Δ a).IsEqn y (t a)) → (∀ a, T a a = t a) → (∀ a b, a < b → T a b = 0) → IsUnit By → ∃ q, (-∑ a : Fin n, if (a : ℕ) < (i : ℕ) then Δ a else 0).GeneratesAt y (GlobalTheory.FlagEmb.plk (GlobalTheory.FlagAmple.PlkLoc.what₂ (T * By.map (algebraMap (X.presheaf.stalk y) X.functionField)) i) id q) := by
  intro X _ y n i Δ t T By hΔ hdiag htri hB
  classical
  have hi : (i : ℕ) ≤ n := i.2.le
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel (Fin.pos i)

  let ρ := IsLocalRing.residue (X.presheaf.stalk y)
  have hBk : IsUnit (By.map ρ) := by simpa using hB.map ρ.mapMatrix
  have hli : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) (FlagAmple.PlkLoc.what₂ (By.map ρ) i) := by
    have h1 := (Matrix.linearIndependent_rows_of_isUnit hBk).comp _ (Fin.castLE_injective hi)
    have hs : Function.Surjective (Fin.cast hn) := fun c => ⟨Fin.cast hn.symm c, Fin.ext rfl⟩
    have h2 := h1.map' (LinearMap.funLeft (IsLocalRing.ResidueField (X.presheaf.stalk y))
      (IsLocalRing.ResidueField (X.presheaf.stalk y)) (Fin.cast hn))
      (LinearMap.ker_eq_bot.2 (LinearMap.funLeft_injective_of_surjective _ _ _ hs))
    exact h2
  obtain ⟨q, hq⟩ := Function.ne_iff.1 (FlagEmb.PlkSpan.plk_ne_zero_of_indep _ (n - 1) i _ hli)
  have hu : IsUnit (FlagEmb.plk (FlagAmple.PlkLoc.what₂ By i) id q) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have := congrFun (FlagEmb.map_plk ρ (FlagAmple.PlkLoc.what₂ By i) id) q
    simp only [Function.comp_apply] at this
    rw [this]
    exact hq
  refine ⟨q, ?_⟩
  rw [((isEqn_sum_ite y i Δ t hΔ Finset.univ).neg).generatesAt_iff]
  refine ⟨_, hu, ?_⟩
  let L : Matrix (Fin i) (Fin i) X.functionField := fun l j => T (Fin.castLE hi l) (Fin.castLE hi j)
  have hrows : FlagAmple.PlkLoc.what₂ (T * By.map (algebraMap (X.presheaf.stalk y) X.functionField)) i =
      fun l => ∑ j, L l j • FlagAmple.PlkLoc.what₂ (By.map (algebraMap (X.presheaf.stalk y) X.functionField)) i j := by
    funext l c
    simp only [FlagAmple.PlkLoc.what₂, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, L]
    apply sum_castLE hi
    intro b hb
    rw [htri _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]
  have hcomb := FlagEmb.PlkSpan.plk_comb X.functionField (n - 1) i
    (FlagAmple.PlkLoc.what₂ (By.map (algebraMap (X.presheaf.stalk y) X.functionField)) i) L
  have hdet : L.det = ∏ j : Fin i, (t (Fin.castLE hi j) : X.functionField) := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [L, hdiag]
    · intro a b hab
      have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
      exact htri _ _ (Fin.lt_def.2 (Fin.lt_def.1 hab'))
  have hg : ((∏ a : Fin n, if (a : ℕ) < (i : ℕ) then t a else 1 : X.functionFieldˣ) : X.functionField) =
      ∏ j : Fin i, (t (Fin.castLE hi j) : X.functionField) := by
    rw [Units.coe_prod, ← prod_castLE hi (fun b => (t b : X.functionField))]
    refine Finset.prod_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have hm := congrFun (FlagEmb.map_plk (algebraMap (X.presheaf.stalk y) X.functionField) (FlagAmple.PlkLoc.what₂ By i) id) q
  simp only [Function.comp_apply] at hm
  rw [hm, hrows, hcomb, Units.val_inv_eq_inv_val, hdet, ← hg, Pi.smul_apply, smul_eq_mul, mul_comm,
    ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  rfl

end GlobalTheory.MinorGen
