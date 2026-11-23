import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelSubbundleIsVB
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.FlagLocal (Same)
open GlobalTheory.LineQuot (cmp cmp_hom_app cmp_naturality cmp_assoc cmp_naturality_assoc cmp_assoc_assoc)

namespace GlobalTheory.GrBundle

variable {R S T G B : Scheme.{0}} {E : B.Modules}

def pl (h : S ⟶ T) {g : T ⟶ B} {k : S ⟶ B} (w : h ≫ g = k) {A : T.Modules}
    (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    (Scheme.Modules.pullback h).obj A ⟶ (Scheme.Modules.pullback k).obj E :=
  (Scheme.Modules.pullback h).map u ≫ (cmp h g w).hom.app E

def IsGr (γ : G ⟶ B) (E : B.Modules) (m : ℕ) {P : G.Modules} (j : P ⟶ (Scheme.Modules.pullback γ).obj E) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ B) (P' : T.Modules) (j' : P' ⟶ (Scheme.Modules.pullback g).obj E),
    IsSubbundle j' → IsVB P' m → ∃! g' : T ⟶ G, ∃ w : g' ≫ γ = g, Same (pl g' w j) j'

variable {g : T ⟶ B} {k : S ⟶ B} {A A' : T.Modules}

theorem isSubbundle_comp_isIso {X : Scheme.{0}} {F F' H : X.Modules} {i : H ⟶ F} (hi : IsSubbundle i) (e : F ⟶ F')
    [IsIso e] : IsSubbundle (i ≫ e) :=
  have ⟨_, s, hs⟩ := hi
  ⟨inferInstance, s, hs.of_iso (cokernelCompIsIso i e).symm⟩

end GlobalTheory.GrBundle

end
