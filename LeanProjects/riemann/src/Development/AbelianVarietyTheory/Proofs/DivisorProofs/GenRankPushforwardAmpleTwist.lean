import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFiniteCompDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointPreimageGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRankPushforwardStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushGenRank

theorem isIso_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    IsIso (X.presheaf.stalkSpecializes h) := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

theorem isClosedMap_of_surface (k : Type) [Field k] (T T' : Scheme.{0}) [Algebra k Γ(T, ⊤)]
    [Algebra k Γ(T', ⊤)] [IsIntegral T] [IsIntegral T'] (hT : IsProjSurface k T)
    (hT' : IsProjSurface k T') (ρ : T' ⟶ T) (hρ : ρ ≫ strHom k T = strHom k T') :
    IsClosedMap ρ.base := by
  have hP : ∀ (S : Scheme.{0}) (f : S ⟶ Sp k), IsProjOver f → IsProper f := by
    rintro S f ⟨N, i, hi, rfl⟩
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
    infer_instance
  haveI := hP _ _ hT.isProjOver
  haveI : IsProper (ρ ≫ strHom k T) := hρ ▸ hP _ _ hT'.isProjOver
  haveI : IsProper ρ := IsProper.of_comp ρ (strHom k T)
  exact ρ.isClosedMap

theorem genRank_pushforward_twist : ∀ (k : Type) [Field k] (T T' : Scheme.{0}) [Algebra k Γ(T, ⊤)] [Algebra k Γ(T', ⊤)] [IsIntegral T] [IsIntegral T'], IsProjSurface k T → IsProjSurface k T' → ∀ (ρ : T' ⟶ T), ρ ≫ strHom k T = strHom k T' → ∀ (d : ℕ), IsGenFinite ρ d → ∀ (M : LB T'), M.IsLB → genRank ((Scheme.Modules.pushforward ρ).obj (twist (structureModule T') M)) = d := by
  intro k _ T T' _ _ _ _ hT hT' ρ hρ d hG M hM
  haveI := hG.isDominant
  have hg := GlobalTheory.GenFiniteComp.apply_genericPoint ρ
  have hcl := isClosedMap_of_surface k T T' hT hT' ρ hρ
  have hfib := GlobalTheory.T.generic_point_preimage_generic T T' ρ d hG
  have hnbhd : ∀ V : T'.Opens, genericPoint T' ∈ V →
      ∃ U : T.Opens, genericPoint T ∈ U ∧ ρ ⁻¹ᵁ U ≤ V := by
    intro V hV
    have hZ := hcl _ V.isOpen.isClosed_compl
    refine ⟨⟨_, hZ.isOpen_compl⟩, ?_, ?_⟩
    · rintro ⟨x, hx, hxη⟩
      exact hx ((hfib x hxη) ▸ hV)
    · intro y hy
      by_contra hyV
      exact hy ⟨y, hyV, rfl⟩
  have hs : ρ (genericPoint T') ⤳ genericPoint T := by rw [hg]
  rw [GlobalTheory.T.generic_rank_pushforward T T' ρ hs hnbhd, ((isVB_structureModule T').twist hM).genRank_eq, mul_one]
  haveI := isIso_stalkSpecializes hs hg
  have key := GlobalTheory.GenFiniteComp.finrank_comp (T.presheaf.stalkSpecializes hs)
    (ρ.stalkMap (genericPoint T')) (Field.toIsField T.functionField)
    (GlobalTheory.GenFiniteComp.isField_stalk_apply ρ)
  refine key.trans ?_
  rw [hG.finrank_eq]
  refine (congrArg (· * d) ?_).trans (one_mul d)
  letI := (T.presheaf.stalkSpecializes hs).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap
    (ConcreteCategory.bijective_of_isIso (T.presheaf.stalkSpecializes hs))

end GlobalTheory.PushGenRank
