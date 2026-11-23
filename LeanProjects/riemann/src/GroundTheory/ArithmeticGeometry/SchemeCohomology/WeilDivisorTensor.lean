import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorSheafIso
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MonoidalCategory

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

lemma isBasisOn_localBasis (D : WeilDivisor X) (U : X.Opens) (g : (X.functionField)ˣ)
    (hg : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z) :
    IsBasisOn ((preMod X).obj (divisorSheaf D)) U (localBasis D U g hg) :=
  fun V h => localBasis_bijective D U g hg V h

theorem isInvertibleSheaf_divisorSheaf (D : WeilDivisor X) :
    IsInvertibleSheaf (divisorSheaf D) := by
  intro x
  obtain ⟨U, g, hxU, hg⟩ := WeilDivisor.exists_local_equation D x
  have hg' : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g Z).symm.trans (hg Z hZ)
  exact ⟨U, hxU, localBasis D U g hg', isBasisOn_localBasis D U g hg'⟩

lemma mul_mem_divisorSections_add {D E : WeilDivisor X} {V : X.Opens}
    {f g : V → X.functionField} (hf : f ∈ divisorSections D V) (hg : g ∈ divisorSections E V) :
    (fun y => f y * g y) ∈ divisorSections (D + E) V := by
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨W₁, hy₁, h₁⟩ := hf.1 y
    obtain ⟨W₂, hy₂, h₂⟩ := hg.1 y
    exact ⟨W₁ ⊓ W₂, ⟨hy₁, hy₂⟩, fun z hz => by simp only [h₁ z hz.1, h₂ z hz.2]⟩
  · simp only [map_mul, Finsupp.coe_add, Pi.add_apply, WithZero.exp_add]
    exact mul_le_mul' (hf.2 y hy) (hg.2 y hy)

noncomputable def divisorSectionsMul {D E : WeilDivisor X} {V : X.Opens} (f : divisorSections D V)
    (g : divisorSections E V) : divisorSections (D + E) V :=
  ⟨fun y => f.1 y * g.1 y, mul_mem_divisorSections_add f.2 g.2⟩

noncomputable def divisorTensorMul (D E : WeilDivisor X) :
    (preMod X).obj (divisorSheaf D) ⊗ (preMod X).obj (divisorSheaf E) ⟶
      (preMod X).obj (divisorSheaf (D + E)) where
  app V := ModuleCat.MonoidalCategory.tensorLift
    (M₁ := ((preMod X).obj (divisorSheaf D)).obj V)
    (M₂ := ((preMod X).obj (divisorSheaf E)).obj V)
    (M₃ := ((preMod X).obj (divisorSheaf (D + E))).obj V)
    (fun f g => divisorSectionsMul (V := V.unop) f g)
    (fun f₁ f₂ g => Subtype.ext (funext fun y => add_mul _ _ _))
    (fun r f g => Subtype.ext (funext fun y => mul_assoc _ _ _))
    (fun f g₁ g₂ => Subtype.ext (funext fun y => mul_add _ _ _))
    (fun r f g => Subtype.ext (funext fun y => by
      change f.1 y * (sectionValue V.unop y r * g.1 y) = sectionValue V.unop y r * (f.1 y * g.1 y)
      ring))
  naturality {V W} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro f g
    apply Subtype.ext
    funext y
    rfl

noncomputable def divisorTensorHom (D E : WeilDivisor X) :
    divisorSheaf D ⊗ divisorSheaf E ⟶ divisorSheaf (D + E) :=
  tensorLift (divisorTensorMul D E)

lemma ord_mul_units (Z : PrimeDivisor X) (g h : (X.functionField)ˣ) :
    Z.ord ((g * h : (X.functionField)ˣ) : X.functionField) =
      Z.ord (g : X.functionField) + Z.ord (h : X.functionField) := by
  rw [Units.val_mul, Z.ord_mul (Units.ne_zero g) (Units.ne_zero h)]

instance (D E : WeilDivisor X) : IsIso (divisorTensorHom D E) := by
  apply isIso_of_isBasisOn
  intro x
  obtain ⟨U₁, g₁, hx₁, hg₁⟩ := WeilDivisor.exists_local_equation D x
  obtain ⟨U₂, g₂, hx₂, hg₂⟩ := WeilDivisor.exists_local_equation E x
  set U := U₁ ⊓ U₂
  have h₁ : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g₁ : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g₁ Z).symm.trans (hg₁ Z hZ.1)
  have h₂ : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g₂ : X.functionField) = E Z :=
    fun Z hZ => (principalDivisor_apply g₂ Z).symm.trans (hg₂ Z hZ.2)
  have h₁₂ : ∀ Z : PrimeDivisor X, Z.point ∈ U →
      Z.ord ((g₁ * g₂ : (X.functionField)ˣ) : X.functionField) = (D + E) Z := by
    intro Z hZ
    rw [ord_mul_units, h₁ Z hZ, h₂ Z hZ, Finsupp.coe_add, Pi.add_apply]
  set s := localBasis D U g₁ h₁
  set t := localBasis E U g₂ h₂
  have hst := ((isBasisOn_localBasis D U g₁ h₁).tmul (isBasisOn_localBasis E U g₂ h₂)).map_of_alt
    (tensorToSheaf (divisorSheaf D) (divisorSheaf E))
    (W_tensorToSheaf (divisorSheaf D) (divisorSheaf E))
  refine ⟨U, ⟨hx₁, hx₂⟩, _, hst, ?_⟩
  have himg : ((preMod X).map (divisorTensorHom D E)).app (op U)
      ((tensorToSheaf (divisorSheaf D) (divisorSheaf E)).app (op U)
        (s ⊗ₜ t : ((preMod X).obj (divisorSheaf D) ⊗ (preMod X).obj (divisorSheaf E)).obj (op U))) =
      localBasis (D + E) U (g₁ * g₂) h₁₂ := by
    have := congrArg (fun φ => φ.app (op U) (s ⊗ₜ t :
      ((preMod X).obj (divisorSheaf D) ⊗ (preMod X).obj (divisorSheaf E)).obj (op U)))
      (tensorToSheaf_tensorLift (divisorTensorMul D E))
    refine this.trans ?_
    apply Subtype.ext
    funext y
    change ((g₁⁻¹ : (X.functionField)ˣ) : X.functionField) * ((g₂⁻¹ : (X.functionField)ˣ) :
      X.functionField) = (((g₁ * g₂)⁻¹ : (X.functionField)ˣ) : X.functionField)
    rw [← Units.val_mul, mul_inv_rev, mul_comm]
  rw [himg]
  exact isBasisOn_localBasis (D + E) U (g₁ * g₂) h₁₂

noncomputable def divisorTensorIso (D E : WeilDivisor X) :
    divisorSheaf D ⊗ divisorSheaf E ≅ divisorSheaf (D + E) :=
  asIso (divisorTensorHom D E)

end GroundTheory.Arith.SchemeCoh
