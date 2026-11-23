import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField Matrix Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodGenericInv

theorem typeSum_inv_eq {K G : Type} [Field K] [Group G] (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) (χ : G → K)
    (hχ : ∀ g h, χ (g * h * g⁻¹) = χ h) (t : G) (ht : ∀ h ∈ P, t * h * t⁻¹ ∈ P)
    (hψ : ∀ (h : G) (hh : h ∈ P), ψ ⟨t * h * t⁻¹, ht h hh⟩ = (ψ ⟨h, hh⟩)⁻¹) :
    ∑ h : P, χ (h : G) * ((((ψ⁻¹) h)⁻¹ : Kˣ) : K) = ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  have hinj : Function.Injective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) := by
    intro a b e
    apply Subtype.ext
    have := congrArg Subtype.val e
    simpa using this
  have hbij : Function.Bijective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) :=
    (Finite.injective_iff_bijective).1 hinj
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Equiv.ofBijective_apply, MonoidHom.inv_apply, inv_inv]
  rw [hχ, hψ h h.2]

def sgnDiag (κ : Type) [CommRing κ] (r : ℕ) : GL (Fin r) κ where
  val := Matrix.diagonal fun i => (-1) ^ i.val
  inv := Matrix.diagonal fun i => (-1) ^ i.val
  val_inv := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem sgnDiag_conj_apply {κ : Type} [CommRing κ] {r : ℕ} (u : GL (Fin r) κ) (i j : Fin r) :
    ((sgnDiag κ r * u * (sgnDiag κ r)⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (-1) ^ i.val * (-1) ^ j.val * (u : Matrix (Fin r) (Fin r) κ) i j := by
  show (Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val) * (u : Matrix (Fin r) (Fin r) κ) *
    Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {κ : Type} [CommRing κ] {r : ℕ}

theorem sgnDiag_conj_mem_unip {u : GL (Fin r) κ} (hu : u ∈ unip κ r) :
    sgnDiag κ r * u * (sgnDiag κ r)⁻¹ ∈ unip κ r := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j h
    rw [sgnDiag_conj_apply, unip_lower hu (show j < i from h), mul_zero]
  · rw [sgnDiag_conj_apply, unip_diag hu i, ← pow_add, ← two_mul, pow_mul]
    simp

theorem edgeSum_sup_conj (u : GL (Fin r) κ) :
    edgeSum supEdge (sgnDiag κ r * u * (sgnDiag κ r)⁻¹) = - edgeSum supEdge u := by
  unfold edgeSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [sgnDiag_conj_apply]
    unfold supEdge at h
    have hs : ((-1 : κ)) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by rw [← mul_pow]; simp
    rw [h, pow_succ]
    linear_combination (-(u : Matrix (Fin r) (Fin r) κ) i j) * hs
  · simp

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}

def alternatingSignDiagonalLevelGroup (Pg : Finset (Pl E)) (r : ℕ) : G0 Pg r := fun PP => sgnDiag (kP PP.1) r

theorem alternatingSignDiagonal_conj_mem_genericLevel (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹ ∈ (P0 Pg r ψ).H := by
  intro PP _
  exact sgnDiag_conj_mem_unip (hx PP (Set.mem_univ _))

theorem genericLevelCharacter_alternatingSign_conj_inv (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    (P0 Pg r ψ).chi ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ = ((P0 Pg r ψ).chi ⟨x, hx⟩)⁻¹ := by
  show (∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP))
      ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ =
    ((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hx⟩)⁻¹
  rw [MonoidHom.finset_prod_apply, MonoidHom.finset_prod_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun PP _ => ?_
  apply Units.ext
  simp only [MonoidHom.comp_apply, addCharHom, MonoidHom.coe_toHomUnits, Units.val_inv_eq_inv_val]
  show ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (sgnDiag (kP PP.1) r * x PP * (sgnDiag (kP PP.1) r)⁻¹)))) =
    (ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (x PP)))))⁻¹
  rw [toAdd_ofAdd, toAdd_ofAdd, edgeSum_sup_conj, AddChar.map_neg_eq_inv]

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

theorem level_character_eq_of_eq {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    {L L' : LevelP Pg r LL} (h : L = L') (x : G0 Pg r) (hx : x ∈ L.H) (hx' : x ∈ L'.H) :
    L.chi ⟨x, hx⟩ = L'.chi ⟨x, hx'⟩ := by
  subst h; rfl

end GlobalTheory.GoodGenericInv
