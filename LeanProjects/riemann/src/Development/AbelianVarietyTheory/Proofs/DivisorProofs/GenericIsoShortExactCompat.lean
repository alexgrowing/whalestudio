import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassIsoInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsFrame Chart det)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.VBExt

theorem genIso_detUnit_mid : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : GlobalTheory.Vert.Model O} {S S' : ShortComplex Z.X.Modules} (hS : S.ShortExact) (hS' : S'.ShortExact) {r s : ℕ} [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] [S'.X₁.IsQuasicoherent] [S'.X₂.IsQuasicoherent] [S'.X₃.IsQuasicoherent] (g₁ : Z.GenIso S.X₁ S'.X₁) (g₂ : Z.GenIso S.X₂ S'.X₂) (g₃ : Z.GenIso S.X₃ S'.X₃), g₁.hom ≫ Z.genRes.map S'.f = Z.genRes.map S.f ≫ g₂.hom → g₂.hom ≫ Z.genRes.map S'.g = Z.genRes.map S.g ≫ g₃.hom → ∀ (a : GlobalTheory.VBExt.AdaptedChart S r s) (a' : GlobalTheory.VBExt.AdaptedChart S' r s) {T : Z.gen.toScheme.Opens} (h : T ≤ Z.gen.ι ⁻¹ᵁ (a.U ⊓ a'.U)), g₂.detUnit (a.mid hS) (a'.mid hS') h = g₁.detUnit a.sub a'.sub h * g₃.detUnit a.quot a'.quot h := by
  intro O _ _ _ Z S S' hS hS' r s _ _ _ _ _ _ g₁ g₂ g₃ hf hg a a' T h
  have hf' : Z.genRes.map S'.f ≫ g₂.inv = g₁.inv ≫ Z.genRes.map S.f := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hg' : Z.genRes.map S'.g ≫ g₃.inv = g₂.inv ≫ Z.genRes.map S.g := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h1 : T ≤ Z.gen.ι ⁻¹ᵁ a.U := h.trans (Z.gen.ι.preimage_mono inf_le_left)
  have h2 : T ≤ Z.gen.ι ⁻¹ᵁ a'.U := h.trans (Z.gen.ι.preimage_mono inf_le_right)
  have hfg : ∀ x, appLinear (Z.genRes.map S.g) T (appLinear (Z.genRes.map S.f) T x) = 0 := by
    intro x
    rw [appLinear_apply, appLinear_apply, QCoh.app_app, ← Functor.map_comp, S.zero,
      Functor.map_zero]
    rfl
  refine Units.ext ?_
  rw [Units.val_mul]
  simp only [GlobalTheory.Vert.Model.GenIso.detUnit, IsFrame.val_detUnit]
  classical
  have hb : ∀ i, (((a.mid hS).isFrame.pullback Z.gen.ι).basis h1).reindex finSumFinEquiv.symm (.inl i) =
      appLinear (Z.genRes.map S.f) T ((a.sub.isFrame.pullback Z.gen.ι).basis h1 i) := by
    intro i
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, IsFrame.basis_apply, IsFrame.basis_apply,
      appLinear_apply, app_resM, QCoh.pullback_map_app_pullbackSections]
    simp [AdaptedChart.mid, AdaptedChart.frame, AdaptedChart.sub]
  have hc : ∀ k, appLinear (Z.genRes.map S.g) T
      ((((a.mid hS).isFrame.pullback Z.gen.ι).basis h1).reindex finSumFinEquiv.symm (.inr k)) =
      (a.quot.isFrame.pullback Z.gen.ι).basis h1 k := by
    intro k
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, IsFrame.basis_apply, IsFrame.basis_apply,
      appLinear_apply, app_resM, QCoh.pullback_map_app_pullbackSections]
    simp [AdaptedChart.mid, AdaptedChart.frame, AdaptedChart.quot]
  have key := det_sumElim hfg ((a.sub.isFrame.pullback Z.gen.ι).basis h1)
    ((a.quot.isFrame.pullback Z.gen.ι).basis h1)
    ((((a.mid hS).isFrame.pullback Z.gen.ι).basis h1).reindex finSumFinEquiv.symm) hb hc
    (fun i => resM _ h2 (g₁.inv.app _ (pullbackSections Z.gen.ι S'.X₁ le_rfl (a'.e i))))
    (fun k => resM _ h2 (g₂.inv.app _ (pullbackSections Z.gen.ι S'.X₂ le_rfl (a'.t k))))
  rw [Module.Basis.det_reindex] at key
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    funext j
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective j
    rcases x with i | k
    · simp only [AdaptedChart.mid, AdaptedChart.frame, Function.comp_apply, Equiv.symm_apply_apply,
        Sum.elim_inl]
      rw [← QCoh.pullback_map_app_pullbackSections, QCoh.app_app, hf', appLinear_apply, app_resM,
        QCoh.app_app]
    · simp only [AdaptedChart.mid, AdaptedChart.frame, Function.comp_apply, Equiv.symm_apply_apply,
        Sum.elim_inr]
  · congr 2
    funext k
    simp only [AdaptedChart.quot]
    rw [appLinear_apply, app_resM, QCoh.app_app, ← hg', ← QCoh.app_app,
      QCoh.pullback_map_app_pullbackSections]

end GlobalTheory.VBExt
