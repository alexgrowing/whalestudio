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

namespace GlobalTheory
namespace CellToSpec

theorem part1 (B Y : Scheme.{0}) (π : Y ⟶ B) (U : B.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (N : Type) (n : N → Γ(Y, W)) :
    W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n)) ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U))) ≫ hU.fromSpec = W.ι ≫ π := by
  rw [← Spec.map_comp_assoc]
  have e : CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U)) ≫ CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) = π.appLE U W hW := by
    ext x
    simp
  rw [e, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

theorem topIso_inv_eq {Y : Scheme.{0}} (W : Y.Opens) (h' : ⊤ ≤ W.ι ⁻¹ᵁ W) : W.topIso.inv = W.ι.appLE W ⊤ h' := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  rfl

theorem appLE_top_top {X Z : Scheme.{0}} (g : X ⟶ Z) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) : g.appLE ⊤ ⊤ h = g.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem part2 {Y : Scheme.{0}} (W : Y.Opens) (R : CommRingCat.{0}) (N : Type) (ρ : MvPolynomial N R →+* Γ(Y, W))
    (h : ⊤ ≤ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ ⊤) (h' : ⊤ ≤ W.ι ⁻¹ᵁ W) (s : N) :
    ((W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ ⊤ h).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N R))).inv.hom (MvPolynomial.X s)) = (W.ι.appLE W ⊤ h').hom (ρ (MvPolynomial.X s)) := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N R))).inv ≫ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ)).appTop =
      CommRingCat.ofHom ρ ≫ W.topIso.inv := by
    rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Opens.toSpecΓ_appTop,
      Iso.inv_hom_id_assoc]
  rw [appLE_top_top, ← topIso_inv_eq W h']
  exact congrArg (fun q => q.hom (MvPolynomial.X s)) e

end CellToSpec

theorem cellToSpec : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (U : B.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (N : Type) (n : N → Γ(Y, W)), W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n)) ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U))) ≫ hU.fromSpec = W.ι ≫ π ∧ ∀ (h : ⊤ ≤ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))) ⁻¹ᵁ ⊤) (h' : ⊤ ≤ W.ι ⁻¹ᵁ W) (s : N), ((W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))).appLE ⊤ ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N Γ(B, U)))).inv.hom (MvPolynomial.X s)) = (W.ι.appLE W ⊤ h').hom (n s) := by
  intro B Y π U hU W hW N n
  refine ⟨CellToSpec.part1 B Y π U hU W hW N n, fun h h' s => ?_⟩
  rw [CellToSpec.part2 W (CommRingCat.of Γ(B, U)) N _ h h' s, MvPolynomial.eval₂Hom_X']

end GlobalTheory
