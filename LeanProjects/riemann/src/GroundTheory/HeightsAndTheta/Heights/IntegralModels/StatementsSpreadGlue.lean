import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadLocal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadIsoLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

@[simp]
lemma pullbackIsoAlong_refl {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) (F : Z.Modules) :
    pullbackIsoAlong e (Iso.refl ((Scheme.Modules.pullback h).obj F)) = Iso.refl _ := by
  ext1
  simp [pullbackIsoAlong]

def restrictSpread (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    {V W : X.Opens} (h : V ≤ W) {E' : (W : Scheme.{0}).Modules}
    (α : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj E' ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj E) :
    (Scheme.Modules.pullback (baseChangeMap f R ∣_ V)).obj
        ((Scheme.Modules.pullback (X.homOfLE h)).obj E') ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ V).ι).obj E :=
  (Scheme.Modules.pullbackComp (baseChangeMap f R ∣_ V) (X.homOfLE h)).app E' ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_homOfLE (baseChangeMap f R) V W h)).app E' ≪≫
    ((Scheme.Modules.pullbackComp (Scheme.homOfLE _ ((baseChangeMap f R).preimage_mono h))
      (baseChangeMap f R ∣_ W)).app E').symm ≪≫
    (Scheme.Modules.pullback (Scheme.homOfLE _ ((baseChangeMap f R).preimage_mono h))).mapIso α ≪≫
    (Scheme.Modules.pullbackComp (Scheme.homOfLE _ ((baseChangeMap f R).preimage_mono h))
      (baseChangeMap f R ⁻¹ᵁ W).ι).app E ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι _ ((baseChangeMap f R).preimage_mono h))).app E

def overlapIso (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    {W₁ W₂ : X.Opens} {E₁ : (W₁ : Scheme.{0}).Modules} {E₂ : (W₂ : Scheme.{0}).Modules}
    (α₁ : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W₁)).obj E₁ ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W₁).ι).obj E)
    (α₂ : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W₂)).obj E₂ ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W₂).ι).obj E) :
    (Scheme.Modules.pullback (baseChangeMap f R ∣_ (W₁ ⊓ W₂))).obj
        ((Scheme.Modules.pullback (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁))).obj E₁) ≅
      (Scheme.Modules.pullback (baseChangeMap f R ∣_ (W₁ ⊓ W₂))).obj
        ((Scheme.Modules.pullback (X.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂))).obj E₂) :=
  restrictSpread f R E inf_le_left α₁ ≪≫ (restrictSpread f R E inf_le_right α₂).symm

def SpreadGlue.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    (W₁ W₂ : X.Opens) (E₁ : (W₁ : Scheme.{0}).Modules) (E₂ : (W₂ : Scheme.{0}).Modules),
    IsVectorBundle E₁ → IsVectorBundle E₂ →
    ∀ (α₁ : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W₁)).obj E₁ ≅
        (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W₁).ι).obj E)
      (α₂ : (Scheme.Modules.pullback (baseChangeMap f R ∣_ W₂)).obj E₂ ≅
        (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W₂).ι).obj E)
      (V : X.Opens), Set.range (baseChangeMap f R) ⊆ Set.range V.ι →
    ∀ θ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ W₂))).obj
        ((Scheme.Modules.pullback (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁))).obj E₁) ≅
      (Scheme.Modules.pullback (X.homOfLE (inf_le_left : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ W₂))).obj
        ((Scheme.Modules.pullback (X.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂))).obj E₂),
    pullbackIsoAlong (rfl : (baseChangeMap f R ∣_ (W₁ ⊓ W₂ ⊓ V)) ≫
        X.homOfLE (inf_le_left : W₁ ⊓ W₂ ⊓ V ≤ W₁ ⊓ W₂) = _) θ =
      pullbackIsoAlong (morphismRestrict_homOfLE (baseChangeMap f R) (W₁ ⊓ W₂ ⊓ V) (W₁ ⊓ W₂)
        inf_le_left).symm (overlapIso f R E α₁ α₂) →
    SpreadsOn f R E ((W₁ ⊔ W₂) ⊓ V)

def structureSpreadIso (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens) :
    (Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj (structureModule (W : Scheme.{0})) ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj (structureModule (baseChange f R)) :=
  pullbackStructureIso _ ≪≫ (pullbackStructureIso _).symm

end

end GroundTheory.Heights₂.Heights.Model
