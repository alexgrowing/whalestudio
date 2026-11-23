import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar BottChern ArRing ArChow HolAtlas Alt IsType IsReal dens chPart tdPart hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DualPullMet

open GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections)

variable {X Y : Scheme.{0}}

theorem theta_coord {E : X.Modules} [E.IsQuasicoherent] (f : Y ⟶ X) {J : Type} [Fintype J]
    {U : X.Opens} {e : J → Γ(E, U)} (he : IsFrame e) (i : J) :
    (DualPull.theta f E).app _ (pullbackSections f (VB.dual E) (le_refl (f ⁻¹ᵁ U)) (he.coord i)) =
      (he.pullback f).coord i :=
  DualPull.dual_pull_ext f le_rfl fun W hW S hS e' s => by
    rw [DualPull.dualApp_theta f _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
    exact (he.pullback_basis_repr f hW e' s i).symm

theorem dualMap_coord {E F : X.Modules} (φ : E ≅ F) {J : Type} [Fintype J]
    {U : X.Opens} {e : J → Γ(E, U)} (he : IsFrame e) (i : J) :
    (dualMap φ.inv).app U (he.coord i) = (he.map_iso φ.hom).coord i := by
  classical
  refine (he.map_iso φ.hom).dual_ext le_rfl fun j => ?_
  rw [IsFrame.dualApp_coord_frame, dualApp_dualMap, ← Twist.app_resM]
  have : ∀ s : Γ(E, U), φ.inv.app U (φ.hom.app U s) = s := fun s => congr(($(φ.hom_inv_id)).app U s)
  rw [this, IsFrame.dualApp_coord_frame]

theorem exists_isIsometry_dual_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (f : Y ⟶ X) (hf : f ≫ p = q) (r : ℕ) (E : HermVB p r) (F : Y.Modules) (φ : (Scheme.Modules.pullback f).obj E.E ≅ F), ∃ χ : (E.dual.pull f hf).E ≅ VB.dual F, (E.dual.pull f hf).h.IsIsometry ((E.h.pull f hf).map φ).dual χ := by
  intro k _ X Y p q f hf r E F φ
  have hE := E.h.isVB
  have := hE.isQuasicoherent
  have := DualPull.isIso_theta f hE
  let χ : (Scheme.Modules.pullback f).obj (VB.dual E.E) ≅ VB.dual F :=
    asIso (DualPull.theta f E.E) ≪≫ dualIso φ.symm
  refine ⟨χ, VMetric.isIsometry_iff _ |>.2 (VMetric.ext (funext fun σ =>
    Met.ext_of_exists fun z => ?_))⟩
  have hc := hE.mem_pick (Points.PtsOver.map f hf _ z)
  set c := hE.pick (Points.PtsOver.map f hf _ z)
  have hch : ((c.pull hE f).map φ).dual = (c.dual.pull hE.dual f).map χ := by
    have H : ((c.pull hE f).map φ).dual.e = ((c.dual.pull hE.dual f).map χ).e := funext fun i =>
      ((congrArg ((dualMap φ.inv).app _) (theta_coord f c.isFrame i)).trans
        (dualMap_coord φ _ i)).symm
    exact congr(VB.Chart.mk _ $H _)
  refine ⟨((c.pull hE f).map φ).dual, hc, ?_⟩
  have e₁ : (((E.h.met σ).pull f hf).map φ).dual.G ((c.pull hE f).map φ).dual z =
      HermFrame.dualGram ((E.h.met σ).G c (Points.PtsOver.map f hf _ z)) :=
    (Met.dual_G (y := z) _ ((c.pull hE f).map φ) hc).trans (congrArg _
      ((Met.map_G (y := z) _ φ (c.pull hE f) hc).trans (Met.pull_G _ f hf c hc)))
  have e₂ : (((E.h.met σ).dual.pull f hf).map χ).G ((c.dual.pull hE.dual f).map χ) z =
      HermFrame.dualGram ((E.h.met σ).G c (Points.PtsOver.map f hf _ z)) :=
    (Met.map_G (y := z) _ χ (c.dual.pull hE.dual f) hc).trans
      ((Met.pull_G _ f hf c.dual hc).trans (Met.dual_G _ c hc))
  rw [← hch] at e₂
  exact e₁.trans e₂.symm

end GlobalTheory.DualPullMet
