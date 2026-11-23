import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

section PullbackHom

variable {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}

def pullbackHomAlong (e : g ≫ h = k) {F G : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G) :
    (Scheme.Modules.pullback k).obj F ⟶ (Scheme.Modules.pullback k).obj G :=
  (pullbackCompIso e (Iso.refl _)).hom ≫ (Scheme.Modules.pullback g).map ψ ≫
    (pullbackCompIso e (Iso.refl _)).inv

lemma pullbackIsoAlong_hom (e : g ≫ h = k) {F G : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    (pullbackIsoAlong e ψ).hom = pullbackHomAlong e ψ.hom := by
  simp [pullbackIsoAlong, pullbackHomAlong]

lemma pullbackHomAlong_comp (e : g ≫ h = k) {F G H : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G)
    (ψ' : (Scheme.Modules.pullback h).obj G ⟶ (Scheme.Modules.pullback h).obj H) :
    pullbackHomAlong e (ψ ≫ ψ') = pullbackHomAlong e ψ ≫ pullbackHomAlong e ψ' := by
  simp [pullbackHomAlong]

lemma pullbackHomAlong_id (e : g ≫ h = k) (F : Z.Modules) :
    pullbackHomAlong e (𝟙 ((Scheme.Modules.pullback h).obj F)) = 𝟙 _ := by
  simp [pullbackHomAlong]

end PullbackHom

section Spread

def SpreadHom.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G,
    ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (hn : 0 < n), m ∣ n →
      ∃ ψ : (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G,
        pullbackHomAlong (toInvOpen_homOfLE f ℚ
          (isUnit_intCast_rat ((a : ℤ) * n) (by positivity))
          (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a n)) ψ = φ

def SpreadHomInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (hn : 0 < n), m ∣ n →
      ∀ ψ₁ ψ₂ : (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G,
        pullbackHomAlong (toInvOpen_homOfLE f ℚ
          (isUnit_intCast_rat ((a : ℤ) * n) (by positivity))
          (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a n)) ψ₁ =
        pullbackHomAlong (toInvOpen_homOfLE f ℚ
          (isUnit_intCast_rat ((a : ℤ) * n) (by positivity))
          (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a n)) ψ₂ →
        ψ₁ = ψ₂

end Spread

end

end GroundTheory.Heights₂.Heights.Model
