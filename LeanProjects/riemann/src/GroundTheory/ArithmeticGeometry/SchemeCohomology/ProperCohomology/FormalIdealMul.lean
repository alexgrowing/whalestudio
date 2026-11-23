import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}} {A : Type u} [CommRing A] [IsNoetherianRing A] [X.Over (Spec (.of A))]

attribute [local instance] algebraOfOver

variable (I : Ideal A) (F : X.Modules)

lemma exists_smulHom_eq_comp_idealSumMap (J : Ideal A) {a : A} (ha : a ∈ J) :
    ∃ h : F ⟶ (⨁ fun _ : Fin (idealGenNum J) => F),
      smulHom F (algebraMap A Γ(X, ⊤) a) = h ≫ idealSumMap F J := by
  rw [← span_idealGen J] at ha
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 ha
  refine ⟨biproduct.lift fun j => smulHom F (algebraMap A Γ(X, ⊤) (c j)), ?_⟩
  simp only [idealSumMap, biproduct.lift_desc, smulHom_comp_smulHom, ← map_mul, ← smulHom_sum,
    ← map_sum]
  rw [hc]

def idealPowOfMem {k : ℕ} (a : A) (ha : a ∈ I ^ k) : F ⟶ idealPow I F k :=
  kernel.lift _ (smulHom F (algebraMap A Γ(X, ⊤) a)) (by
    obtain ⟨h, hh⟩ := exists_smulHom_eq_comp_idealSumMap F (I ^ k) ha
    rw [hh, Category.assoc, cokernel.condition, comp_zero])

@[reassoc (attr := simp)]
lemma idealPowOfMem_ι {k : ℕ} (a : A) (ha : a ∈ I ^ k) :
    idealPowOfMem I F a ha ≫ idealPowι I F k = smulHom F (algebraMap A Γ(X, ⊤) a) :=
  kernel.lift_ι _ _ _

end

end GroundTheory.Arith.SchemeCoh
