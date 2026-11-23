import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Vert.Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem genRes_exact_mono (Z : GlobalTheory.Vert.Model O) (S : ShortComplex Z.X.Modules) (hS : S.ShortExact)
    {s : ℕ} (h₃ : GlobalTheory.VB.IsVB S.X₃ s) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    (S.map Z.genRes).Exact ∧ Mono (Z.genRes.map S.f) := by
  refine ⟨?_, GlobalTheory.FlagPull.mono_pullback_map_f Z.gen.ι S hS h₃⟩
  exact ShortComplex.exact_of_g_is_cokernel _
    (CokernelCofork.mapIsColimit _ hS.gIsCokernel Z.genRes)

theorem exists_genIso_ker : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Z : GlobalTheory.Vert.Model O) (A B C A' B' C' : Z.X.Modules) (f : A ⟶ B) (g : B ⟶ C)
    (hfg : f ≫ g = 0) (f' : A' ⟶ B') (g' : B' ⟶ C') (hfg' : f' ≫ g' = 0),
    (ShortComplex.mk f g hfg).ShortExact → (ShortComplex.mk f' g' hfg').ShortExact →
    ∀ (s s' : ℕ), GlobalTheory.VB.IsVB C s → GlobalTheory.VB.IsVB C' s' →
    ∀ [A.IsQuasicoherent] [B.IsQuasicoherent] [A'.IsQuasicoherent] [B'.IsQuasicoherent]
    (φB : Z.GenIso B B') (φC : Z.GenIso C C'),
    Z.genRes.map g ≫ φC.hom = φB.hom ≫ Z.genRes.map g' →
    ∃ γ : Z.GenIso A A', γ.hom ≫ Z.genRes.map f' = Z.genRes.map f ≫ φB.hom := by
  intro O _ _ _ Z A B C A' B' C' f g hfg f' g' hfg' hS hS' s s' hC hC' _ _ _ _ φB φC hc
  obtain ⟨hT, hm⟩ := genRes_exact_mono Z _ hS (s := s) hC
  obtain ⟨hT', hm'⟩ := genRes_exact_mono Z _ hS' (s := s') hC'
  have hc' : φB.inv ≫ Z.genRes.map g = Z.genRes.map g' ≫ φC.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hk : (Z.genRes.map f ≫ φB.hom) ≫ Z.genRes.map g' = 0 := by
    rw [Category.assoc, ← hc, ← Category.assoc, ← Functor.map_comp, hfg, Functor.map_zero,
      zero_comp]
  have hk' : (Z.genRes.map f' ≫ φB.inv) ≫ Z.genRes.map g = 0 := by
    rw [Category.assoc, hc', ← Category.assoc, ← Functor.map_comp, hfg', Functor.map_zero,
      zero_comp]
  haveI : Mono (ShortComplex.map (ShortComplex.mk f g hfg) Z.genRes).f := hm
  haveI : Mono (ShortComplex.map (ShortComplex.mk f' g' hfg') Z.genRes).f := hm'
  let α : Z.genRes.obj A ⟶ Z.genRes.obj A' := hT'.lift (Z.genRes.map f ≫ φB.hom) hk
  let β : Z.genRes.obj A' ⟶ Z.genRes.obj A := hT.lift (Z.genRes.map f' ≫ φB.inv) hk'
  have hα : α ≫ Z.genRes.map f' = Z.genRes.map f ≫ φB.hom := hT'.lift_f _ _
  have hβ : β ≫ Z.genRes.map f = Z.genRes.map f' ≫ φB.inv := hT.lift_f _ _
  refine ⟨⟨α, β, ?_, ?_⟩, hα⟩
  · rw [← cancel_mono (Z.genRes.map f)]
    calc (α ≫ β) ≫ Z.genRes.map f = α ≫ (Z.genRes.map f' ≫ φB.inv) := by
          simp only [Category.assoc, hβ]
      _ = 𝟙 _ ≫ Z.genRes.map f := by
          rw [← Category.assoc, hα, Category.assoc, Iso.hom_inv_id, Category.comp_id,
            Category.id_comp]
  · rw [← cancel_mono (Z.genRes.map f')]
    calc (β ≫ α) ≫ Z.genRes.map f' = β ≫ (Z.genRes.map f ≫ φB.hom) := by
          simp only [Category.assoc, hα]
      _ = 𝟙 _ ≫ Z.genRes.map f' := by
          rw [← Category.assoc, hβ, Category.assoc, Iso.inv_hom_id, Category.comp_id,
            Category.id_comp]

end GlobalTheory.Vert.Model
