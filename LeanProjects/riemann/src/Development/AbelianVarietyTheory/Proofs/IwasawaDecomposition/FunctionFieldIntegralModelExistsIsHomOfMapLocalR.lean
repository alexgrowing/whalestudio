import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G GlobalTheory.Points
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def constHom (M : RatModel o Ω) (U : M.Z.Opens) : o →+* Γ(M.Z, U) :=
  (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom

theorem finiteType_constHom (M : RatModel o Ω) {U : M.Z.Opens} (hU : IsAffineOpen U) :
    (M.constHom U).FiniteType := by
  have := M.lft
  have h1 : (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
    M.s.finiteType_appLE (isAffineOpen_top _) hU _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

variable {Ω' : Type} [Field Ω'] [Algebra o Ω']

theorem exists_nbhd_of_map_O (M : RatModel o Ω) (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω') {z' : M'.Z} {z : M.Z}
    (hz : ∀ a ∈ M.O z, φ a ∈ M'.O z') :
    ∃ (V : M'.Z.Opens) (U : M.Z.Opens), z' ∈ V ∧ IsAffineOpen U ∧ (U : Set M.Z).Nonempty ∧
      ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M.Z.Opens)) (x := z) trivial
  have hUne : (U : Set M.Z).Nonempty := ⟨z, hzU⟩
  letI := (M.constHom U).toAlgebra
  obtain ⟨s, hs⟩ := (M.finiteType_constHom hU).out
  let V : M'.Z.Opens := ⟨⋂ f ∈ s, {w | φ (valF M.pt U f) ∈ M'.O w},
    isOpen_biInter_finset fun f _ => M'.isOpen_setOf_mem_O _⟩
  have hzV : z' ∈ V := Set.mem_iInter₂.2 fun f _ => hz _ (valF_mem_O hzU f)
  have hsV : ∀ f ∈ s, φ (valF M.pt U f) ∈ M'.ringOn V := fun f hf =>
    mem_ringOn.2 fun w hw => Set.mem_iInter₂.1 hw f hf
  have key : ∀ f : Γ(M.Z, U), φ (valF M.pt U f) ∈ M'.ringOn V := by
    intro f
    have hf : f ∈ Algebra.adjoin o (s : Set Γ(M.Z, U)) := hs ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact hsV x hx
    | algebraMap r =>
      have e : valF M.pt U (algebraMap o Γ(M.Z, U) r) = algebraMap o Ω r := M.valF_constFn hUne r
      rw [e, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_add, map_add, res_apply, res_apply]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_mul, map_mul, res_apply, res_apply]
      exact mul_mem hx hy
  refine ⟨V, U, hzV, hU, hUne, fun x hx => ?_⟩
  obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
  exact key f

theorem exists_isHom_of_map_O :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω']
      (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') →
        ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  intro o Ω _ _ _ M Ω' _ _ M' φ h
  refine exists_isHom_of_local fun z' => ?_
  obtain ⟨z, hz⟩ := h z'
  exact exists_nbhd_of_map_O M M' φ hz

end GlobalTheory.ZH.RatModel
end
