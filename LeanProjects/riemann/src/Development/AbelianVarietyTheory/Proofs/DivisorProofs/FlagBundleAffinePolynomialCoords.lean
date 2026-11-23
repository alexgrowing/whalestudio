import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackFrameSpanningFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameIsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagSpannedFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCarriesBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedFlagTriangularFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChartOfFlagBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsSameFrameIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialPointFactorsThroughChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CellScheme

theorem cell_affine : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens), IsAffineOpen U → ∀ (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), IsAffineOpen W ∧ ∃ n : (Σ a, Low (r a)) → Γ(Y, W), Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) ∧ ∀ a, GlobalTheory.FlagCell.Spans (fl a) W (GlobalTheory.FlagCell.pullCol π (eU a) hW (GlobalTheory.FlagCell.uniR fun s => n ⟨a, s⟩)) := by
  intro B Y π ι _ r E fl hfl hE U hU eU heU
  obtain ⟨W, hW, n, hSp, hMax⟩ := GlobalTheory.T.exists_pullback_frame_spanning_flag B Y π ι r E fl hE U eU heU
  let A := CommRingCat.of (MvPolynomial (Σ a, Low (r a)) Γ(B, U))
  let g : Spec A ⟶ B := Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial (Σ a, Low (r a)) Γ(B, U))) ≫ hU.fromSpec
  have hgU : (⊤ : (Spec A).Opens) ≤ g ⁻¹ᵁ U := by
    simp [g, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  let n' : (Σ a, Low (r a)) → Γ(Spec A, ⊤) := fun s => (Scheme.ΓSpecIso A).inv.hom (MvPolynomial.X s)
  have hfr : ∀ a, IsFrame (pullCol g (eU a) hgU (uniR fun s => n' ⟨a, s⟩)) := fun a =>
    GlobalTheory.T.pullback_unipotent_frame_isFrame _ _ g (E a) (r a) (hE a) U (eU a) (heU a) ⊤ hgU _
  choose fl' hfl' using fun a => GlobalTheory.T.exists_flag_spanned_frame (Spec A) _ (r a) _ (hfr a)
  obtain ⟨ψ, ⟨w, hC⟩, -⟩ := hfl (Spec A) g fl'
  have hψ : (⊤ : (Spec A).Opens) ≤ ψ ⁻¹ᵁ W := by
    intro t _
    obtain ⟨V, hV, n₀, ht, hV'⟩ := GlobalTheory.T.flag_bundle_carries_base_change B Y π ι r E fl hE U eU heU (Spec A) ψ g w fl' hC ⊤ hgU n' hfl' t trivial
    obtain ⟨hVW, -⟩ := hMax V hV n₀ hV'
    exact hVW ht
  have hn : ∀ s, (ψ.appLE W ⊤ hψ).hom (n s) = (Scheme.ΓSpecIso A).inv.hom (MvPolynomial.X s) := by
    rintro ⟨a, s⟩
    have h1 := GlobalTheory.T.carried_flag_triangular_frame B Y (Spec A) π ι r E fl ψ g w fl' hC U a (eU a) W hW (uniR fun s => n ⟨a, s⟩) ⊤ hψ hgU (hSp a)
    rw [map_uniR] at h1
    exact congrFun (GlobalTheory.T.pullback_unipotent_frame_unique (Spec A) B g (E a) (r a) (hE a) U (eU a) (heU a) (fl' a) ⊤ hgU _ _ h1 (hfl' a)) s
  let φ : W.toScheme ⟶ Spec A := W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))
  obtain ⟨hφg, hφn⟩ := GlobalTheory.T.exists_polynomial_chart_of_flag_bundle B Y π U hU W hW _ n
  have hφg' : φ ≫ g = W.ι ≫ π := by simpa only [φ, g, Category.assoc] using hφg
  have hWU : (⊤ : W.toScheme.Opens) ≤ (W.ι ≫ π) ⁻¹ᵁ U := by
    intro x _
    exact hW x.2
  have h₁ : (⊤ : W.toScheme.Opens) ≤ φ ⁻¹ᵁ ⊤ := le_top.trans (by simp)
  have h₂ : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  have hφC : Carries g E r fl' φ (W.ι ≫ π) hφg' (carried π E r fl W.ι (W.ι ≫ π) rfl) := by
    intro a i
    have k₁ := GlobalTheory.T.carried_flag_triangular_frame _ _ _ g ι r E fl' φ (W.ι ≫ π) hφg' _ (carries_carried g E r fl' φ (W.ι ≫ π) hφg') U a (eU a) ⊤ hgU (uniR fun s => n' ⟨a, s⟩) ⊤ h₁ hWU (hfl' a)
    have k₂ := GlobalTheory.T.carried_flag_triangular_frame _ _ _ π ι r E fl W.ι (W.ι ≫ π) rfl _ (carries_carried π E r fl W.ι (W.ι ≫ π) rfl) U a (eU a) W hW (uniR fun s => n ⟨a, s⟩) ⊤ h₂ hWU (hSp a)
    rw [map_uniR] at k₁ k₂
    have e : (fun s => (φ.appLE ⊤ ⊤ h₁).hom (n' ⟨a, s⟩)) = fun s => (W.ι.appLE W ⊤ h₂).hom (n ⟨a, s⟩) :=
      funext fun s => hφn h₁ h₂ _
    rw [e] at k₁
    obtain ⟨e, he⟩ := GlobalTheory.T.flags_same_frame_iso _ _ _ _ _ _ k₁ k₂ i
    exact ⟨e, by simpa [carried, Vert.Flag.ofIso, Vert.Flag.pull] using he⟩
  have huniq : W.ι = φ ≫ ψ := (hfl W.toScheme (W.ι ≫ π) (carried π E r fl W.ι (W.ι ≫ π) rfl)).unique
    ⟨rfl, carries_carried π E r fl W.ι (W.ι ≫ π) rfl⟩
    ⟨by rw [Category.assoc, w, hφg'], carries_comp π E r fl ψ g w fl' φ (W.ι ≫ π) hφg' _ _ hC hφC⟩
  obtain ⟨hAff, hBij⟩ := GlobalTheory.T.polynomial_point_factors_through_chart B Y π U hU W hW _ n ψ w hψ hn (by simpa only [φ, Category.assoc] using huniq.symm)
  exact ⟨W, hW, hAff, n, hBij, hSp⟩

end GlobalTheory.CellScheme

end
