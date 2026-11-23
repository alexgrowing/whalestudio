import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVan
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import GroundTheory.AutomorphicForms.GLnLocal
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.CommutingInverses.InvCommOfComm

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def GzS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Subgroup (GL (Fin n) k) where
  carrier := Gz Z
  one_mem' a _ := by simp
  mul_mem' {g h} hg hh a ha := by
    simp only [Units.val_mul]
    rw [← mul_assoc, hg a ha, mul_assoc, hh a ha, mul_assoc]
  inv_mem' {g} hg a ha := by
    have h1 := hg a ha
    calc a * (g⁻¹).val = (g⁻¹).val * (g.val * a) * (g⁻¹).val := by simp [← mul_assoc]
      _ = (g⁻¹).val * (a * g.val) * (g⁻¹).val := by rw [h1]
      _ = (g⁻¹).val * a := by simp [mul_assoc]

theorem isClosed_GzS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (GzS Z : Set (GL (Fin n) k)) := by
  have hset : (GzS Z : Set (GL (Fin n) k)) = ⋂ a ∈ Z, {g : GL (Fin n) k | a * g.val = g.val * a} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [hset]
  exact isClosed_biInter fun a _ =>
    isClosed_eq (continuous_const.mul Units.continuous_val) (Units.continuous_val.mul continuous_const)

instance gzs_lc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : LocallyCompactSpace (GzS Z) :=
  (isClosed_GzS Z).isClosedEmbedding_subtypeVal.locallyCompactSpace

def conjB (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (hg : g ∈ Gz Z) :
    Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) →ₗ[k]
      Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) where
  toFun x := ⟨g.val * x.1 * g⁻¹.val, (Subalgebra.mem_centralizer_iff k).2 fun a ha => by
    have hx := (Subalgebra.mem_centralizer_iff k).1 x.2 a ha
    have h1 := hg a ha
    have h2 : a * g⁻¹.val = g⁻¹.val * a := (GzS Z).inv_mem (x := g) hg a ha
    calc a * (g.val * x.1 * g⁻¹.val) = (a * g.val) * x.1 * g⁻¹.val := by simp only [mul_assoc]
      _ = g.val * (a * x.1) * g⁻¹.val := by rw [h1]; simp only [mul_assoc]
      _ = g.val * x.1 * (a * g⁻¹.val) := by rw [hx]; simp only [mul_assoc]
      _ = g.val * x.1 * g⁻¹.val * a := by rw [h2]; simp only [mul_assoc]⟩
  map_add' x y := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c x := Subtype.ext (by simp)

def DetConj : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ (g : GL (Fin n) k) (hg : g ∈ Gz Z),
    LinearMap.det (conjB Z g hg) = 1

def Unimod : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → PositivityTheory.PfBern.Frob.IsUnimod (GzS Z)

end PositivityTheory.RgUd.T.Desc.SLF
