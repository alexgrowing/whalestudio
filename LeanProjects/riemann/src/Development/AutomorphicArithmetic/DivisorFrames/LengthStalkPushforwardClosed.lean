import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

theorem UpperTheory.length_stalk_pushforward_closed :
    ∀ (X Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules) (z : Z), Module.length (X.presheaf.stalk (i z)) (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i z) :) = Module.length (Z.presheaf.stalk z) (G.presheaf.stalk z :) := by
  intro X Z i _ F z
  let G := (Scheme.Modules.pushforward i).obj F
  let φ := i.stalkMap z
  letI : Algebra (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) := φ.hom.toAlgebra
  letI : Module (X.presheaf.stalk (i z)) (F.presheaf.stalk z :) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk (i z)) (Z.presheaf.stalk z))
  haveI : IsScalarTower (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) (F.presheaf.stalk z :) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Ψ : (G.presheaf.stalk (i z) :) →+ (F.presheaf.stalk z :) :=
    (F.presheaf.stalkPushforward _ i.base z).hom
  have hΨ (U : X.Opens) (hU : i z ∈ U) (s : Γ(G, U)) :
      Ψ (G.presheaf.germ U _ hU s) = F.presheaf.germ (i ⁻¹ᵁ U) z hU s := by
    have e' := TopCat.Presheaf.stalkPushforward_germ _ i.base F.presheaf U z hU
    exact congr($(e').hom s)
  have hbij : Function.Bijective Ψ := by
    have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
      i.isClosedEmbedding.isInducing F.presheaf z
    exact ConcreteCategory.bijective_of_isIso (F.presheaf.stalkPushforward _ i.base z)
  have hsmul (a : X.presheaf.stalk (i z)) (m : (G.presheaf.stalk (i z) :)) :
      Ψ (a • m) = φ.hom a • Ψ m := by
    obtain ⟨U₁, hU₁, r, rfl⟩ := X.presheaf.germ_exist a
    obtain ⟨U₂, hU₂, s, rfl⟩ := G.presheaf.germ_exist m
    have hU : i z ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) _ hU,
      ← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) _ hU]
    generalize X.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r = r'
    generalize G.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op s = s'
    rw [← GlobalTheory.QCoh.germ_smul G, hΨ, hΨ]
    refine (GlobalTheory.QCoh.germ_smul F (U := i ⁻¹ᵁ (U₁ ⊓ U₂)) _ _ (i.app _ r') s').trans ?_
    congr 1
    have e₂ := Scheme.Hom.germ_stalkMap i (U₁ ⊓ U₂) z hU
    exact congr($(e₂).hom r').symm
  let e : (G.presheaf.stalk (i z) :) ≃ₗ[X.presheaf.stalk (i z)] (F.presheaf.stalk z :) :=
    { AddEquiv.ofBijective Ψ hbij with map_smul' := hsmul }
  exact e.length_eq.trans (Module.length_eq_of_surjective (i.stalkMap_surjective z))
