import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def GlueModulesStar.Statement : Prop :=
  ∀ (X : Scheme.{0}) (V : X.Opens) (ι : Type) (U : ι → X.Opens),
    V ⊔ ⨆ i, U i = ⊤ → (∀ i j, i ≠ j → U i ⊓ U j ≤ V) →
    ∀ (G : (V : Scheme.{0}).Modules) (F : ∀ i, (U i : Scheme.{0}).Modules)
      (ψ : ∀ i, (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U i ⊓ V ≤ U i))).obj (F i) ≅
        (Scheme.Modules.pullback (X.homOfLE (inf_le_right : U i ⊓ V ≤ V))).obj G),
    ∃ (E : X.Modules) (e₀ : (Scheme.Modules.pullback V.ι).obj E ≅ G)
      (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj E ≅ F i),
      ∀ i, pullbackCompIso (X.homOfLE_ι (inf_le_right : U i ⊓ V ≤ V)) e₀ =
        pullbackCompIso (X.homOfLE_ι (inf_le_left : U i ⊓ V ≤ U i)) (e i) ≪≫ ψ i

def VectorBundleRestrict.Statement : Prop :=
  ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsOpenImmersion f] (E : Y.Modules), IsVectorBundle E →
    IsVectorBundle ((Scheme.Modules.pullback f).obj E)

def VectorBundleLocal.Statement : Prop :=
  ∀ (X : Scheme.{0}) (ι : Type) (U : ι → X.Opens), ⨆ i, U i = ⊤ → ∀ E : X.Modules,
    (∀ i, IsVectorBundle ((Scheme.Modules.pullback (U i).ι).obj E)) → IsVectorBundle E

section Inhabitants

def halfThirdOpens : Bool → SpecZ.Opens := fun b =>
  if b then invOpen (𝟙 SpecZ) 2 else invOpen (𝟙 SpecZ) 3

lemma mem_invOpen_id (m : ℤ) (x : SpecZ) : x ∈ invOpen (𝟙 SpecZ) m ↔ m ∉ x.asIdeal := Iff.rfl

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Model
