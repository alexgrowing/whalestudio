import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_add_l (a b y : Fin n → E) : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub_l (a b y : Fin n → E) : hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul_l (c : E) (a y : Fin n → E) : hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_r (a b y : Fin n → E) : hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_sub_r (a b y : Fin n → E) : hf L Hm y (a - b) = hf L Hm y a - hf L Hm y b := by
  simp [hf, mul_sub, Finset.sum_sub_distrib]

theorem hf_neg_r (a y : Fin n → E) : hf L Hm y (-a) = - hf L Hm y a := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_neg_l (a y : Fin n → E) : hf L Hm (-a) y = - hf L Hm a y := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_smul_r (c : E) (a y : Fin n → E) : hf L Hm y (c • a) = L.cj c * hf L Hm y a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_cj {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x y : Fin n → E) :
    L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j
  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def eichL (x u : Fin n → E) (s : E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun := eich L Hm x u s
  map_add' a b := by
    simp only [eich, hf_add_l]; module
  map_smul' c a := by
    simp only [eich, hf_smul_l, RingHom.id_apply]; module

theorem eich_inv {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x u : Fin n → E) (s : E)
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u) (v : Fin n → E) :
    eich L Hm x (-u) (L.cj s) (eich L Hm x u s v) = v := by
  have hu' : hf L Hm x u = 0 := by rw [← hf_cj L h, hu, map_zero]
  simp only [eich, hf_add_l, hf_sub_l, hf_smul_l, hf_neg_r, hx, hu, hu', ← hs]
  module

theorem eich_isom {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x u : Fin n → E) (s : E)
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u) (v w : Fin n → E) :
    hf L Hm (eich L Hm x u s v) (eich L Hm x u s w) = hf L Hm v w := by
  have hu' : hf L Hm x u = 0 := by rw [← hf_cj L h, hu, map_zero]
  simp only [eich, hf_add_l, hf_sub_l, hf_smul_l, hf_add_r, hf_sub_r, hf_smul_r, hx, hu, hu', ← hs,
    hf_cj L h]
  ring

end

theorem eichler_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (x u : Fin n → E) (s : E), hf L Hm x x = 0 → hf L Hm u x = 0 → s + L.cj s = hf L Hm u u → ∃ g ∈ isomG L Hm, (∀ v, g v = eich L Hm x u s v) ∧ ∀ v, g⁻¹ v = eich L Hm x (-u) (L.cj s) v := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH x u s hx hu hs
  have h1 := eich_inv L hH.1 x u s hx hu hs
  have h2 := eich_inv L hH.1 x (-u) (L.cj s) hx (by rw [hf_neg_l, hu, neg_zero])
    (by rw [L.cj_cj, hf_neg_l, hf_neg_r, neg_neg, add_comm, hs])
  simp only [neg_neg, L.cj_cj] at h2
  refine ⟨{ eichL L Hm x u s with
      invFun := eich L Hm x (-u) (L.cj s)
      left_inv := h1
      right_inv := h2 }, ?_, fun _ => rfl, fun _ => rfl⟩
  exact fun v w => eich_isom L hH.1 x u s hx hu hs v w

end GlobalTheory.HL.Eichler
