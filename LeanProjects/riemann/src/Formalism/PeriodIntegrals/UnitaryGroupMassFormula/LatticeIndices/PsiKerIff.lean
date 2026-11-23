import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondSplitTensorVector

noncomputable section

namespace MassDataIdxCore

open Matrix

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]

def toO (M : Matrix n n K) (hM : IntM O M) : Matrix n n O := fun i j => ⟨M i j, hM i j⟩

theorem toO_map (M : Matrix n n K) (hM : IntM O M) : (toO O M hM).map (algebraMap O K) = M := by
  ext i j
  rfl

theorem map_inj : Function.Injective fun M : Matrix n n O => M.map (algebraMap O K) := by
  intro M N h
  ext i j
  have h1 := congrFun (congrFun h i) j
  exact h1

variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K) {H : Type} [Group H] (m : H →* GL n T)
  (hK : ∀ h x, x ∈ Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P)

include hK in
theorem int_of (h : H) : IntM O (conjPrime₂ θ P (m h)) :=
  conjP_int O θ J P (m h) fun x hx => (hK h x).mp hx

def psiU (h : H) : GL n O :=
  ⟨toO O _ (int_of O θ J P m hK h), toO O _ (int_of O θ J P m hK h⁻¹), by
    apply map_inj O
    simp only [Matrix.map_mul, toO_map, ← conjP_mul, ← map_mul, mul_inv_cancel, map_one, conjP_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm, by
    apply map_inj O
    simp only [Matrix.map_mul, toO_map, ← conjP_mul, ← map_mul, inv_mul_cancel, map_one, conjP_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm⟩

theorem psiU_map (h : H) : ((psiU O θ J P m hK h : GL n O) : Matrix n n O).map (algebraMap O K) =
    conjPrime₂ θ P (m h) :=
  toO_map O _ (int_of O θ J P m hK h)

def psi : H →* GL n O where
  toFun := psiU O θ J P m hK
  map_one' := by
    apply Units.ext
    apply map_inj O
    simp only [psiU_map, map_one, conjP_one, Units.val_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  map_mul' _ _ := by
    apply Units.ext
    apply map_inj O
    simp only [Units.val_mul, Matrix.map_mul, psiU_map, map_mul, conjP_mul]

theorem psi_map (h : H) : ((psi O θ J P m hK h : GL n O) : Matrix n n O).map (algebraMap O K) =
    conjPrime₂ θ P (m h) :=
  psiU_map O θ J P m hK h

theorem psi_ker_iff (c : O) (h : H) :
    (∀ i j, (((psi O θ J P m hK h : GL n O) : Matrix n n O) - 1) i j ∈ Ideal.span {c}) ↔
      ∀ i j, ∃ w ∈ O, (conjPrime₂ θ P (m h) - 1) i j = (c : K) * w := by
  have key : ∀ i j, ((((psi O θ J P m hK h : GL n O) : Matrix n n O) - 1) i j : K) =
      (conjPrime₂ θ P (m h) - 1) i j := by
    intro i j
    rw [← psi_map O θ J P m hK h]
    simp [Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro H1 i j
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (H1 i j)
    refine ⟨b, b.2, ?_⟩
    rw [← key, ← hb]
    push_cast
    ring
  · intro H1 i j
    obtain ⟨w, hw, hwe⟩ := H1 i j
    refine Ideal.mem_span_singleton'.mpr ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    rw [key]
    rw [hwe]
    push_cast
    ring

end MassDataIdxCore
