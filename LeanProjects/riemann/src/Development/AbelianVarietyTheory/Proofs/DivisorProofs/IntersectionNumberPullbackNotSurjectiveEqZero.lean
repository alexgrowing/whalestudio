import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrHomEqAndIsProjOver
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem hom_genericPoint_ne {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIntegral A.X.left]
    [IsIntegral B.X.left] (hns : ¬ Surjective f.hom.left) :
    f.hom.left (genericPoint A.X.left) ≠ genericPoint B.X.left := by
  intro h
  apply hns
  have : IsProper A.X.hom := A.ab.proper
  have : IsProper B.X.hom := B.ab.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : IsProper f.hom.left := IsProper.of_comp _ B.X.hom
  have hcl : IsClosed (Set.range f.hom.left) := by
    rw [← Set.image_univ]; exact f.hom.left.isClosedMap _ isClosed_univ
  have hsub : closure ({genericPoint B.X.left} : Set B.X.left) ⊆ Set.range f.hom.left :=
    hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 ⟨_, h⟩)
  rw [(genericPoint_spec B.X.left).def] at hsub
  exact ⟨fun y => hsub (Set.mem_univ y)⟩

theorem inter_pull_eq_zero_of_not_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ¬ Surjective f.hom.left → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = 0 := by
  intro K _ A B f hdim hns J _ hJ c
  haveI := (GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K A).1
  haveI := (GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K B).1
  letI := A.algΓ
  obtain ⟨hs, hp⟩ := GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A
  choose L hL hc using fun j => cls_surj (c j)
  have hne := hom_genericPoint_ne f hns
  have hη : genericPoint B.X.left ∈ (closure ({f.hom.left (genericPoint A.X.left)} : Set B.X.left))ᶜ :=
    fun h => hne (((specializes_iff_mem_closure.2 h).antisymm (genericPoint_specializes _)).eq)
  have h1 := GlobalTheory.PullVanish.dim_closure_add_one_le (genericPoint_specializes (f.hom.left (genericPoint A.X.left)))
    isClosed_closure.isOpen_compl hη (fun h => h (subset_closure rfl))
  have h2 : topologicalKrullDim (closure ({genericPoint B.X.left} : Set B.X.left)) = topologicalKrullDim B.X.left := by
    rw [(genericPoint_spec B.X.left).def]
    exact (Homeomorph.Set.univ B.X.left).isHomeomorph.topologicalKrullDim_eq
  have hB : topologicalKrullDim B.X.left ≤ (A.dim : ℕ) := by
    rw [GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K B, hdim]
  have h3 := GlobalTheory.PullVanish.withBot_lt_of_add_one_le_nat (h1.trans (h2.trans_le hB))
  have hA : topologicalKrullDim A.X.left ≤ ((0 + A.dim : ℕ) : WithBot ℕ∞) := by
    rw [Nat.zero_add, GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A]
  let e : Fin 0 ⊕ Fin A.dim ≃ J := (Equiv.emptySum (Fin 0) (Fin A.dim)).trans (Fintype.equivFinOfCardEq hJ).symm
  have h := GlobalTheory.PullVanish.interNum_pull_eq_zero K 0 A.dim A.X.left B.X.left (hs ▸ hp) hA f.hom.left h3
    (fun i => i.elim0) (fun i => i.elim0) (fun a => L (e (.inr a))) (fun a => hL _)
  have hL' : ∀ j, ((L j).pull f.hom.left).IsLB := fun j => pull_isLB (hL j) _
  have hcl : (fun j => CechPic.pull f.hom.left (c j)) = fun j => cls ((L j).pull f.hom.left) (hL' j) := by
    funext j; rw [← hc j]; rfl
  rw [inter, hcl, ← interNum_eq_multiDiff K _ hL', ← interNum_comp_equiv K _ hL' e, ← h]
  congr 1
  funext x
  rcases x with i | a
  · exact i.elim0
  · rfl

end GlobalTheory.AV.AbVar
