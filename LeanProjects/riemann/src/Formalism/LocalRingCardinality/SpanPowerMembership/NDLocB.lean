import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  (j : Ω →+* PadicAlgCl l)

def jE : E →+* PadicAlgCl l := j.comp (algebraMap E Ω)

def KwF : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => jE (E := E) j (Module.finBasis ℚ E i))

instance KwF_fin : FiniteDimensional ℚ_[l] (KwF (E := E) j) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem jE_mem (x : E) : jE j x ∈ KwF (E := E) j := by
  rw [← (Module.finBasis ℚ E).sum_repr x, map_sum]
  refine IntermediateField.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin ℚ_[l] _ ⟨i, rfl⟩)

def clE : Subfield (PadicAlgCl l) := (jE (E := E) j).fieldRange.topologicalClosure

theorem algebraMap_mem_clE (x : ℚ_[l]) : algebraMap ℚ_[l] (PadicAlgCl l) x ∈ clE (E := E) j := by
  have hcont : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (PadicAlgCl l))
      (PadicAlgCl.norm_extends l)).continuous
  have hclosed : IsClosed {y : ℚ_[l] | algebraMap ℚ_[l] (PadicAlgCl l) y ∈ clE (E := E) j} := by
    have hc : IsClosed ((clE (E := E) j : Subfield (PadicAlgCl l)) : Set (PadicAlgCl l)) := by
      first
      | exact Subfield.isClosed_topologicalClosure _
      | exact isClosed_closure
    exact hc.preimage hcont
  have hQ : ∀ q : ℚ, algebraMap ℚ_[l] (PadicAlgCl l) (q : ℚ_[l]) ∈ clE (E := E) j := by
    intro q
    rw [map_ratCast]
    exact Subfield.le_topologicalClosure _ (SubfieldClass.ratCast_mem _ q)
  exact (Padic.denseRange_ratCast l).induction_on x hclosed hQ

theorem KwF_le_clE : (KwF (E := E) j : Set (PadicAlgCl l)) ⊆
    closure (Set.range fun x : E => j (algebraMap E Ω x)) := by
  let F : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    Subfield.toIntermediateField (clE (E := E) j) (algebraMap_mem_clE j)
  have hle : KwF (E := E) j ≤ F := by
    rw [KwF, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact Subfield.le_topologicalClosure _ (RingHom.mem_fieldRange.mpr ⟨_, rfl⟩)
  intro x hx
  have h1 : x ∈ ((clE (E := E) j : Subfield (PadicAlgCl l)) : Set (PadicAlgCl l)) := hle hx
  have h2 : ((clE (E := E) j : Subfield (PadicAlgCl l)) : Set (PadicAlgCl l)) =
      closure (Set.range fun x : E => j (algebraMap E Ω x)) := by
    show closure ((jE (E := E) j).fieldRange : Set (PadicAlgCl l)) = _
    rw [RingHom.coe_fieldRange]
    rfl
  rwa [h2] at h1

theorem mem_GK_of_fix (σ : GQ l) (h : ∀ x : E, σ (jE j x) = jE j x) :
    σ ∈ (KwF (E := E) j).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have hle : KwF (E := E) j ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [KwF, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : Subgroup.zpowers σ ≤
        MulAction.stabilizer (GQ l) (jE (E := E) j (Module.finBasis ℚ E i)) :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (h _))
    exact MulAction.mem_stabilizer_iff.mp (hst hf)
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) σ (Subgroup.mem_zpowers σ)

theorem norm_aut (σ : GQ l) (x : PadicAlgCl l) : ‖σ x‖ = ‖x‖ := by
  have h1 : ∀ y : PadicAlgCl l, ‖y‖ = spectralNorm ℚ_[l] (PadicAlgCl l) y := fun y => rfl
  rw [h1, h1, ← spectralNorm_eq_of_equiv]

end Formalism.BasicNotions.Examples₂.LB
