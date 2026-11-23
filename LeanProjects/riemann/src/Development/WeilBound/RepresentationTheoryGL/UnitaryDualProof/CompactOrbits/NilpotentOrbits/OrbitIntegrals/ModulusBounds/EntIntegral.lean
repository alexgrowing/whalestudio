import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.RelIndexEq
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetEqOfSurj
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.IsClosedGz

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def lat (V : Submodule k (Matrix (Fin n) (Fin n) k)) (γ : ValueGroupWithZero k) :
    AddSubgroup (Matrix (Fin n) (Fin n) k) where
  carrier := {y | y ∈ V ∧ ∀ i j, valuation k (y i j) ≤ γ}
  add_mem' {a b} ha hb := ⟨V.add_mem ha.1 hb.1, fun i j => by
    simp only [Matrix.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (ha.2 i j) (hb.2 i j))⟩
  zero_mem' := ⟨V.zero_mem, fun i j => by simp⟩
  neg_mem' {a} ha := ⟨V.neg_mem ha.1, fun i j => by
    simp only [Matrix.neg_apply, Valuation.map_neg]
    exact ha.2 i j⟩

theorem mem_lat {V : Submodule k (Matrix (Fin n) (Fin n) k)} {γ : ValueGroupWithZero k}
    {y : Matrix (Fin n) (Fin n) k} : y ∈ lat V γ ↔ y ∈ V ∧ ∀ i j, valuation k (y i j) ≤ γ := Iff.rfl

def cj (g : GL (Fin n) k) (X : AddSubgroup (Matrix (Fin n) (Fin n) k)) : AddSubgroup (Matrix (Fin n) (Fin n) k) :=
  X.comap (adL g⁻¹).toAddMonoidHom

theorem mem_cj {g : GL (Fin n) k} {X : AddSubgroup (Matrix (Fin n) (Fin n) k)} {y : Matrix (Fin n) (Fin n) k} :
    y ∈ cj g X ↔ g⁻¹.val * y * g.val ∈ X := by
  simp [cj, adL_apply]

theorem adL_inv_adL (g : GL (Fin n) k) (y : Matrix (Fin n) (Fin n) k) : g⁻¹.val * (g.val * y * g⁻¹.val) * g.val = y := by
  simp [← mul_assoc]

theorem adL_adL_inv (g : GL (Fin n) k) (y : Matrix (Fin n) (Fin n) k) : g.val * (g⁻¹.val * y * g.val) * g⁻¹.val = y := by
  simp [← mul_assoc]

theorem ent_mul {γ : ValueGroupWithZero k} {a b : Matrix (Fin n) (Fin n) k} (ha : ∀ i j, valuation k (a i j) ≤ 1)
    (hb : ∀ i j, valuation k (b i j) ≤ γ) : ∀ i j, valuation k ((a * b) i j) ≤ γ := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul]
  calc valuation k (a i l) * valuation k (b l j) ≤ 1 * γ := mul_le_mul' (ha i l) (hb l j)
    _ = γ := one_mul γ

theorem ent_integral {u : GL (Fin n) k} (hu : u ∈ integralGL k n) : ∀ i j, valuation k (u.val i j) ≤ 1 :=
  fun i j => ((mem_integralGL_iff k n).1 hu).1 i j

theorem mem_C_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (y : Matrix (Fin n) (Fin n) k) :
    y ∈ (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule ↔ y ∈ Bz Z := by
  rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
  rfl

theorem mem_Gz_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (u : GL (Fin n) k) :
    u ∈ Gz Z ↔ u.val - 1 ∈ Bz Z := by
  constructor
  · intro h a ha
    rw [mul_sub, sub_mul, h a ha, mul_one, one_mul]
  · intro h a ha
    have := h a ha
    rw [mul_sub, sub_mul, mul_one, one_mul] at this
    exact sub_left_inj.1 this

theorem Bz_mul (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {a b : Matrix (Fin n) (Fin n) k} (ha : a ∈ Bz Z)
    (hb : b ∈ Bz Z) : a * b ∈ Bz Z := fun z hz => by
  rw [← mul_assoc, ha z hz, mul_assoc, hb z hz, mul_assoc]

theorem Bz_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    {a : Matrix (Fin n) (Fin n) k} (ha : a ∈ Bz Z) : g.val * a * g⁻¹.val ∈ Bz Z := by
  have := cC_inv Z g hg a ((mem_C_iff Z a).2 ha)
  rw [adL_apply] at this
  exact (mem_C_iff Z _).1 this

theorem Gz_inv (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Gz Z) : g⁻¹ ∈ Gz Z :=
  (GzS Z).inv_mem hg

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
