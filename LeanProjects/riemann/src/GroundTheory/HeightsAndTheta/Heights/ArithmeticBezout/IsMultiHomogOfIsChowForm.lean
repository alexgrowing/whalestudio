import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)

def blk (n : ℕ) : Fin n → (Σ _ : Unit, PBlk n ()) := fun i => ⟨(), i⟩

def genericIdeal {n : ℕ} (P : Ideal (MRing (PBlk n))) : Ideal (MvPolynomial (Fin n) ℚ) :=
  (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (MvPolynomial.map (Int.castRingHom ℚ))

variable {n : ℕ}

theorem rename_linForm (u : Fin n → ℤ) :
    rename (blk n) (linForm u) = IndefiniteRowSideFullHecke.ArithBezout.linForm u := by
  simp [linForm, IndefiniteRowSideFullHecke.ArithBezout.linForm, map_sum, blk, Xc]

theorem linForm_mem_finIdeal (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ) :
    linForm u ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P ↔ IndefiniteRowSideFullHecke.ArithBezout.linForm u ∈ P := by
  rw [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, ← rename_linForm]
  rfl

theorem specFirst_eq {R : Type*} [CommRing R] {e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R)
    (u : Fin n → R) : specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f := by
  rw [specFirst, IndefiniteRowSideFullHecke.ArithBezout.specFirst, aeval_eq_bind₁]
  rfl

theorem map_specFirst {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {e : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R) :
    map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f) := by
  have h : (fun ij => map φ (specFirstVar u ij)) =
      (specFirstVar (φ ∘ u) : Fin (e + 1) × Fin n → MvPolynomial (Fin e × Fin n) S) := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [specFirstVar]
  rw [← specFirst_eq, ← specFirst_eq, specFirst, specFirst, map_bind₁, h]

theorem weight_groupWeight {k : ℕ} (m : Fin k × Fin n →₀ ℕ) :
    Finsupp.weight (groupWeight k n) m = fun i => ∑ j, m (i, j) := by
  funext i
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; exact zero_smul _ _), Finset.sum_apply,
    Fintype.sum_prod_type]
  simp [groupWeight, Pi.single_apply]

theorem isMultiHomog_iff {R : Type*} [CommSemiring R] {e δ : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) : IsMultiHomog δ f ↔ IsMultihomog f δ := by
  simp only [IsMultiHomog, IsWeightedHomogeneous, IsMultihomog, mem_support_iff, weight_groupWeight,
    funext_iff]

theorem isMultihomog_map_iff {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) {e δ : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R) :
    IsMultihomog (map φ f) δ ↔ IsMultihomog f δ := by
  simp only [IsMultihomog, support_map_of_injective _ hφ]

theorem isMultiHomog_of_isChowForm {e δ : ℕ} {P : Ideal (MRing (PBlk n))}
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f)) : IsMultiHomog δ f :=
  (isMultiHomog_iff f).mpr ((isMultihomog_map_iff (Rat.castHom ℂ).injective f).mp hf.1)

theorem isRelevant_finIdeal_iff (W : Ideal (MRing (PBlk n))) :
    IsRelevant (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
  simp only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap,
    rename_X]
  exact ⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩

theorem isChowFormCycle_iff {F : Type*} [Field F] {k : ℕ} (Z : ProjCycle F n)
    (f : MvPolynomial (Fin k × Fin n) F) :
    IsChowFormCycle Z k f ↔ ∃ c : F, c ≠ 0 ∧ ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
      (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z g :=
  Iff.rfl

theorem isChowForm_C_mul {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by
  have hu : IsUnit (C c : MvPolynomial (Fin k × Fin n) F) := (isUnit_iff_ne_zero.mpr hc).map C
  refine ⟨mul_ne_zero (hu.ne_zero) hf.1, fun g => (hf.2 g).trans ?_⟩
  exact (hu.mul_left_dvd).symm

theorem chowDegree_eq {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k δ : ℕ}
    (hk : 0 < k) {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f)
    (hδ : IsMultiHomog δ f) : chowDegree I k = δ := by
  have key : ∀ δ', (∃ g, IsChowForm I k g ∧ IsMultiHomog δ' g) → δ' = δ := by
    rintro δ' ⟨g, hg, hδ'⟩
    obtain ⟨a, rfl⟩ : f ∣ g := (hf.2 g).mp ((hg.2 g).mpr dvd_rfl)
    obtain ⟨b, hb⟩ : f * a ∣ f := (hg.2 f).mp ((hf.2 f).mpr dvd_rfl)
    have hab : a * b = 1 := by
      apply mul_left_cancel₀ hf.1
      rw [mul_one, ← mul_assoc, ← hb]
    obtain ⟨r, hr, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (isUnit_iff_exists_inv.mpr ⟨b, hab⟩)
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hf.1
    have h1 := hδ hd
    have h2 := hδ' (show coeff d (f * C r) ≠ 0 by rw [mul_comm, coeff_C_mul]; exact mul_ne_zero hr.ne_zero hd)
    exact congrFun (h2.symm.trans h1) ⟨0, hk⟩
  exact le_antisymm (Nat.sInf_le ⟨f, hf, hδ⟩) (le_csInf ⟨δ, f, hf, hδ⟩ fun δ' h => (key δ' h).ge)

theorem equiv :
    (∀ (n : ℕ) (u : Fin n → ℤ), rename (blk n) (linForm u) = IndefiniteRowSideFullHecke.ArithBezout.linForm u) ∧
    (∀ (n : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
      linForm u ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P ↔ IndefiniteRowSideFullHecke.ArithBezout.linForm u ∈ P) ∧
    (∀ (R : Type) [CommRing R] (n e : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) R)
      (u : Fin n → R), specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) ∧
    (∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (n e : ℕ)
      (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R),
      map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f)) ∧
    (∀ (R : Type) [CommSemiring R] (n e δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) R),
      IsMultiHomog δ f ↔ IsMultihomog f δ) ∧
    (∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
        (map (Rat.castHom ℂ) f) → IsMultiHomog δ f) ∧
    (∀ (n : ℕ) (W : Ideal (MRing (PBlk n))),
      IsRelevant (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W) ∧
    (∀ (F : Type) [Field F] (n k : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
      IsChowFormCycle Z k f ↔ ∃ c : F, c ≠ 0 ∧
        ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
          (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z g) ∧
    (∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
      (f : MvPolynomial (Fin k × Fin n) F) (c : F),
      IsChowForm I k f → c ≠ 0 → IsChowForm I k (C c * f)) ∧
    (∀ (F : Type) [Field F] (n k δ : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
      (f : MvPolynomial (Fin k × Fin n) F),
      0 < k → IsChowForm I k f → IsMultiHomog δ f → chowDegree I k = δ) :=
  ⟨fun _ => rename_linForm, fun _ => linForm_mem_finIdeal, fun _ _ _ _ => specFirst_eq,
    fun _ _ _ _ φ _ _ => map_specFirst φ, fun _ _ _ _ _ => isMultiHomog_iff,
    fun _ _ _ _ _ => isMultiHomog_of_isChowForm, fun _ => isRelevant_finIdeal_iff,
    fun _ _ _ _ => isChowFormCycle_iff, fun _ _ _ _ _ _ _ hf hc => isChowForm_C_mul hf hc,
    fun _ _ _ _ _ _ _ hk hf hδ => chowDegree_eq hk hf hδ⟩

end ObjectsChow

end GroundTheory.Heights₂.Heights
