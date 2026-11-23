import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts

namespace GlobalTheory.ChainParts.PartVB

theorem isIso_of_retract {C : Type*} [Category C] {A A' X X' : C} (f : A' ⟶ A) (g : X' ⟶ X) [IsIso g]
    (i' : A' ⟶ X') (q' : X' ⟶ A') (i : A ⟶ X) (q : X ⟶ A) (h' : i' ≫ q' = 𝟙 _) (h : i ≫ q = 𝟙 _)
    (hi : f ≫ i = i' ≫ g) (hq : g ≫ q = q' ≫ f) : IsIso f := by
  refine ⟨i ≫ inv g ≫ q', ?_, ?_⟩
  · rw [← Category.assoc, hi, Category.assoc, IsIso.hom_inv_id_assoc, h']
  · rw [Category.assoc, Category.assoc, ← hq, IsIso.inv_hom_id_assoc, h]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]
  {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ)

noncomputable def proj (M : AM B Λ) (h : eA M c a ≫ eA M c a = eA M c a) : M.V ⟶ (partF c a).obj M :=
  kernel.lift (𝟙 M.V - eA M c a) (eA M c a) (by rw [Preadditive.comp_sub, Category.comp_id, h, sub_self])

theorem mono_partι (M : AM B Λ) : Mono (partι c a M) :=
  inferInstanceAs (Mono (kernel.ι (𝟙 M.V - eA M c a)))

theorem proj_ι (M : AM B Λ) (h : eA M c a ≫ eA M c a = eA M c a) : proj c a M h ≫ partι c a M = eA M c a :=
  kernel.lift_ι _ _ _

theorem ι_eA (M : AM B Λ) : partι c a M ≫ eA M c a = partι c a M := by
  have h : partι c a M ≫ (𝟙 M.V - eA M c a) = 0 := kernel.condition _
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
  exact h.symm

theorem ι_proj (M : AM B Λ) (h : eA M c a ≫ eA M c a = eA M c a) : partι c a M ≫ proj c a M h = 𝟙 _ := by
  haveI := mono_partι c a M
  rw [← cancel_mono (partι c a M), Category.assoc, proj_ι, ι_eA, Category.id_comp]

theorem map_ι {M N : AM B Λ} (f : M ⟶ N) : (partF c a).map f ≫ partι c a N = partι c a M ≫ f.hom :=
  kernel.lift_ι _ _ _

theorem proj_map {M N : AM B Λ} (f : M ⟶ N) (hM : eA M c a ≫ eA M c a = eA M c a)
    (hN : eA N c a ≫ eA N c a = eA N c a) :
    f.hom ≫ proj c a N hN = proj c a M hM ≫ (partF c a).map f := by
  haveI := mono_partι c a N
  rw [← cancel_mono (partι c a N), Category.assoc, Category.assoc, proj_ι, map_ι, ← Category.assoc, proj_ι, eA_comm]

theorem main : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ] {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) (hidem : ∀ M : AM B Λ, IsAdd M → eA M c a ≫ eA M c a = eA M c a) (P : EPres B Λ), ∃ r, GlobalTheory.VB.IsVB ((partF c a).obj P.E) r ∧ GlobalTheory.VB.IsVB ((partF c a).obj P.E') r ∧
      IsIso (B.genRes.map ((partF c a).map P.ψ)) := by
  intro O _ _ _ B Λ _ n c a hidem P
  have h := hidem _ P.add
  have h' := hidem _ P.add'
  have v := GlobalTheory.VB.isVB_of_retract B.X _ _ _ _ _ (ι_proj c a P.E h) P.vb
  have v' := GlobalTheory.VB.isVB_of_retract B.X _ _ _ _ _ (ι_proj c a P.E' h') P.vb'
  haveI := P.iso
  have hi : IsIso (B.genRes.map ((partF c a).map P.ψ)) :=
    isIso_of_retract _ (B.genRes.map P.ψ.hom) (B.genRes.map (partι c a P.E')) (B.genRes.map (proj c a P.E' h'))
      (B.genRes.map (partι c a P.E)) (B.genRes.map (proj c a P.E h))
      (by rw [← Functor.map_comp, ι_proj, CategoryTheory.Functor.map_id])
      (by rw [← Functor.map_comp, ι_proj, CategoryTheory.Functor.map_id])
      (by rw [← Functor.map_comp, ← Functor.map_comp, map_ι])
      (by rw [← Functor.map_comp, ← Functor.map_comp, proj_map c a P.ψ h' h])
  haveI : Nonempty B.gen.toScheme := ⟨⟨_, B.genericPoint_mem_gen⟩⟩
  have e := ((v'.pullback B.gen.ι).of_iso (asIso (B.genRes.map ((partF c a).map P.ψ)))).rank_unique
    (v.pullback B.gen.ι)
  exact ⟨_, v, e ▸ v', hi⟩

end GlobalTheory.ChainParts.PartVB
