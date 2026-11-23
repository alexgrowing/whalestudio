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

namespace GlobalTheory.ChainParts.FrobPart

theorem nonempty_kernel_iso {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [HasKernels C]
    [HasKernels D] (F : C ⥤ D) [F.Additive] {X : C} (e : X ⟶ X) (he : e ≫ e = e) (e' : F.obj X ⟶ F.obj X)
    (h : F.map e = e') : Nonempty (kernel (𝟙 (F.obj X) - e') ≅ F.obj (kernel (𝟙 X - e))) := by
  subst h
  let r : X ⟶ kernel (𝟙 X - e) := kernel.lift _ e (by rw [Preadditive.comp_sub, he, Category.comp_id, sub_self])
  have hri : r ≫ kernel.ι _ = e := kernel.lift_ι _ _ _
  have hie : kernel.ι (𝟙 X - e) ≫ e = kernel.ι (𝟙 X - e) := by
    have := kernel.condition (𝟙 X - e)
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
    exact this.symm
  have hir : kernel.ι (𝟙 X - e) ≫ r = 𝟙 _ := by
    rw [← cancel_mono (kernel.ι (𝟙 X - e)), Category.assoc, hri, hie, Category.id_comp]
  have hje : kernel.ι (𝟙 (F.obj X) - F.map e) ≫ F.map e = kernel.ι (𝟙 (F.obj X) - F.map e) := by
    have := kernel.condition (𝟙 (F.obj X) - F.map e)
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
    exact this.symm
  refine ⟨⟨kernel.ι _ ≫ F.map r, kernel.lift _ (F.map (kernel.ι _)) ?_, ?_, ?_⟩⟩
  · rw [Preadditive.comp_sub, Category.comp_id, ← F.map_comp, hie, sub_self]
  · rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, Category.assoc, ← F.map_comp, hri, hje,
      Category.id_comp]
  · rw [← Category.assoc, kernel.lift_ι, ← F.map_comp, hir, F.map_id]

section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
  {B : Vert.Model O} (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0)

theorem map_smulHom (F : B.X.Modules) (g : Γ(B.X, ⊤)) :
    (frobFun p h).map (smulHom F g) = smulHom _ (g ^ p) := by
  unfold frobFun
  rw [Functor.comp_map, VB.pullback_map_smulHom, GlobalTheory.MixedLocalChains.FrobQuot.appTop_absFrob_comp p B h g, ← map_pow]
  exact pushforward_map_smulHom _ _ _

theorem smulHom_p (F : B.X.Modules) : smulHom ((frobFun p h).obj F) (p : Γ(B.X, ⊤)) = 0 := by
  have k := pushforward_map_smulHom (fibI p B).subschemeι
    ((Scheme.Modules.pullback (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h ≫ (fibI p B).subschemeι)).obj F)
    (p : Γ(B.X, ⊤))
  rw [map_natCast, h, smulHom_zero, Functor.map_zero] at k
  exact k.symm

end

theorem main : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] {B : Vert.Model O} {Λ : Type} [CommRing Λ] (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) {n : ℕ} (c c' : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) (hc : ∀ k, ∃ v : Γ(B.X, ⊤), c' k = c k ^ p + p * v) (hidem : ∀ M : AM B Λ, IsAdd M → eA M c a ≫ eA M c a = eA M c a) (M : AM B Λ) (hM : IsAdd M), Nonempty ((partF c' a).obj (frobA p h M) ≅ (frobFun p h).obj ((partF c a).obj M)) := by
  intro O _ _ _ p _ _ _ B Λ _ h n c c' a hc hidem M hM
  haveI := Examples₂.additive_frobFun p h
  refine nonempty_kernel_iso (frobFun p h) (eA M c a) (hidem M hM) (eA (frobA p h M) c' a) ?_
  unfold eA
  rw [Functor.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨v, hv⟩ := hc k
  have e : smulHom ((frobFun p h).obj M.V) (c' k) = smulHom _ (c k ^ p) := by
    rw [hv, smulHom_add, smulHom_mul, smulHom_p, comp_zero, add_zero]
  rw [Functor.map_comp, map_smulHom, ← e]
  rfl

end GlobalTheory.ChainParts.FrobPart
