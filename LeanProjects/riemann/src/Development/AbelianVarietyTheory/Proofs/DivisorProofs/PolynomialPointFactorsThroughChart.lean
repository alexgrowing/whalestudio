import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

theorem exists_lift_toSpecΓ {Y : Scheme.{0}} (W : Y.Opens) (A : CommRingCat.{0})
    (ψ : Spec A ⟶ Y) (hψ : ⊤ ≤ ψ ⁻¹ᵁ W) :
    ∃ ψ' : Spec A ⟶ W.toScheme, ψ' ≫ W.ι = ψ ∧
      ψ' ≫ W.toSpecΓ = Spec.map (ψ.appLE W ⊤ hψ ≫ (Scheme.ΓSpecIso A).hom) := by
  refine ⟨(Spec A).topIso.inv ≫ ψ.resLE W ⊤ hψ, ?_, ?_⟩
  · rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.toIso_inv_ι,
      Category.id_comp]
  · rw [Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_appLE, Scheme.Opens.toSpecΓ_top,
      Spec.map_comp, SpecMap_ΓSpecIso_hom, ← Category.assoc, ← Category.assoc,
      Scheme.toIso_inv_ι, Category.id_comp]

theorem isAffineOpen_and_bijective_of_section :
    ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (U : B.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (N : Type) (n : N → Γ(Y, W)) (ψ : Spec (CommRingCat.of (MvPolynomial N Γ(B, U))) ⟶ Y), ψ ≫ π = Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U))) ≫ hU.fromSpec → ∀ (hψ : ⊤ ≤ ψ ⁻¹ᵁ W), (∀ s, (ψ.appLE W ⊤ hψ).hom (n s) = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N Γ(B, U)))).inv.hom (MvPolynomial.X s)) → W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n)) ≫ ψ = W.ι → IsAffineOpen W ∧ Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) := by
  intro B Y π U hU W hW N n ψ hπ hψ hn hι
  obtain ⟨ψ', h0, h1⟩ := exists_lift_toSpecΓ W _ ψ hψ
  set g := ψ.appLE W ⊤ hψ ≫ (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N Γ(B, U)))).hom with hg
  have h2 : π.appLE U W hW ≫ g =
      CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U)) := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, ← hπ, Spec.map_comp, ← h1, Category.assoc, Category.assoc,
      ← Category.assoc W.toSpecΓ, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc,
      hU.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι, ← Category.assoc, h0]
  set ev : CommRingCat.of (MvPolynomial N Γ(B, U)) ⟶ Γ(Y, W) :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) with hev
  have h3 : ev ≫ g = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      have := congrArg (fun f => f.hom c) h2
      simpa [hev] using this
    · intro s
      simp [hev, hg, hn s]
  have h4 : ψ' ≫ (W.toSpecΓ ≫ Spec.map ev) = 𝟙 _ := by
    rw [← Category.assoc, h1, ← Spec.map_comp, h3, Spec.map_id]
  have h5 : (W.toSpecΓ ≫ Spec.map ev) ≫ ψ' = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, h0, Category.assoc, hι, Category.id_comp]
  haveI : IsIso (W.toSpecΓ ≫ Spec.map ev) := ⟨ψ', h5, h4⟩
  have hWa : IsAffineOpen W := IsAffine.of_isIso (W.toSpecΓ ≫ Spec.map ev)
  refine ⟨hWa, ?_⟩
  haveI : IsIso W.toSpecΓ := by
    rw [← hWa.isoSpec_hom]; infer_instance
  haveI : IsIso (Spec.map ev) := IsIso.of_isIso_comp_left W.toSpecΓ _
  haveI : IsIso ev := by
    have h : IsIso (Scheme.Spec.map ev.op) := this
    haveI := isIso_of_reflects_iso ev.op Scheme.Spec
    exact isIso_of_op ev
  exact ConcreteCategory.bijective_of_isIso ev

end GlobalTheory.FlagCell
