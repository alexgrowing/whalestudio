import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagAmple.PlkLoc

open GlobalTheory.Cartier.CartierDiv

theorem prod_ite_lt {M : Type} [CommMonoid M] {n : ℕ} (i : Fin n) (f : Fin n → M) :
    (∏ a : Fin n, if (a : ℕ) < (i : ℕ) then f a else 1) =
      ∏ a : Fin (i : ℕ), f (Fin.castLE i.2.le a) := by
  rw [← Finset.prod_filter]
  have e : (Finset.univ.filter fun a : Fin n => (a : ℕ) < (i : ℕ)) =
      Finset.univ.map (Fin.castLEEmb i.2.le) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro h
      exact ⟨⟨a, h⟩, Fin.ext rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.2
  rw [e, Finset.prod_map]
  rfl

theorem det_rows_mul {K : Type} [CommRing K] {n : ℕ} (T B : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (hu : ∀ a b, a < b → T a b = 0) (e : Fin (i : ℕ) → Fin (n - 1 + 1)) :
    (Matrix.of fun l l' => what₂ (T * B) i l (e l')).det =
      (∏ a : Fin (i : ℕ), T (Fin.castLE i.2.le a) (Fin.castLE i.2.le a)) *
        (Matrix.of fun l l' => what₂ B i l (e l')).det := by
  have hT : (T.submatrix (Fin.castLE i.2.le) (Fin.castLE i.2.le)).det =
      ∏ a : Fin (i : ℕ), T (Fin.castLE i.2.le a) (Fin.castLE i.2.le a) := by
    refine (Matrix.det_of_lowerTriangular _ ?_).trans rfl
    intro a b hab
    exact hu _ _ ((Fin.castLE_lt_castLE_iff _).2 hab)
  rw [← hT, ← Matrix.det_mul]
  congr 1
  ext l l'
  simp only [Matrix.of_apply, what₂, Matrix.mul_apply, Matrix.submatrix_apply]
  have := Finset.sum_map (Finset.univ : Finset (Fin (i : ℕ))) (Fin.castLEEmb i.2.le)
    (fun b => T (Fin.castLE i.2.le l) b * B b (Fin.cast (Nat.sub_add_cancel (Fin.pos i)) (e l')))
  simp only [Fin.castLEEmb_apply] at this
  rw [← this]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_
  have hlt : ¬ (b : ℕ) < (i : ℕ) := fun h => hb (Finset.mem_map.2 ⟨⟨b, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hu _ _ (Fin.lt_def.2 (lt_of_lt_of_le l.2 (not_lt.1 hlt))), zero_mul]

theorem isEqn_sum_ite {X : Scheme.{0}} [IsIntegral X] (y : X) {n : ℕ} (i : Fin n)
    (Δ : Fin n → GlobalTheory.Cartier.CartierDiv X) (t : Fin n → X.functionFieldˣ) (h : ∀ a, (Δ a).IsEqn y (t a))
    (s : Finset (Fin n)) :
    (∑ a ∈ s, if (a : ℕ) < (i : ℕ) then Δ a else 0).IsEqn y
      (∏ a ∈ s, if (a : ℕ) < (i : ℕ) then t a else 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.Cartier.CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine IsEqn.add ?_ ih
    split_ifs
    · exact h a
    · exact GlobalTheory.Cartier.CartierDiv.isEqn_zero y

theorem regularAt_plk_rows : ∀ (X : Scheme.{0}) [IsIntegral X] (y : X) (n : ℕ) (i : Fin n) (Δ : Fin n → GlobalTheory.Cartier.CartierDiv X) (t : Fin n → X.functionFieldˣ) (T : Matrix (Fin n) (Fin n) X.functionField) (By : Matrix (Fin n) (Fin n) (X.presheaf.stalk y)), (∀ a, (Δ a).IsEqn y (t a)) → (∀ a, T a a = t a) → (∀ a b, a < b → T a b = 0) → ∀ q, (-∑ a : Fin n, if (a : ℕ) < (i : ℕ) then Δ a else 0).RegularAt y (GlobalTheory.FlagEmb.plk (GlobalTheory.FlagAmple.PlkLoc.what₂ (T * By.map (algebraMap (X.presheaf.stalk y) X.functionField)) i) id q) := by
  intro X _ y n i Δ t T By ht hd hu q
  have hE := (isEqn_sum_ite y i Δ t ht Finset.univ).neg
  refine hE.regularAt_iff.2 ?_
  have hprod : (((∏ a : Fin n, if (a : ℕ) < (i : ℕ) then t a else 1 : X.functionFieldˣ)⁻¹ :
      X.functionFieldˣ) : X.functionField) =
      (∏ a : Fin (i : ℕ), T (Fin.castLE i.2.le a) (Fin.castLE i.2.le a))⁻¹ := by
    rw [prod_ite_lt i t, Units.val_inv_eq_inv_val, Units.coe_prod]
    simp only [hd]
  have hne : (∏ a : Fin (i : ℕ), T (Fin.castLE i.2.le a) (Fin.castLE i.2.le a)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => by rw [hd]; exact (t _).ne_zero
  rw [hprod]
  have hdet := det_rows_mul T (By.map (algebraMap (X.presheaf.stalk y) X.functionField)) i hu
    (GlobalTheory.FlagEmb.plE (n - 1) (i : ℕ) q)
  have hplk : GlobalTheory.FlagEmb.plk (what₂ (T * By.map (algebraMap (X.presheaf.stalk y) X.functionField)) i) id q =
      (Matrix.of fun l l' => what₂ (T * By.map (algebraMap (X.presheaf.stalk y) X.functionField)) i l
        (GlobalTheory.FlagEmb.plE (n - 1) (i : ℕ) q l')).det := rfl
  rw [hplk, hdet, mul_comm, inv_mul_cancel_left₀ hne]
  refine ⟨(Matrix.of fun l l' => what₂ By i l (GlobalTheory.FlagEmb.plE (n - 1) (i : ℕ) q l')).det, ?_⟩
  rw [RingHom.map_det]
  rfl

end GlobalTheory.FlagAmple.PlkLoc
