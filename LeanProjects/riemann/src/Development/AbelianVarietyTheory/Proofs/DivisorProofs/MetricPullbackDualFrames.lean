import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option autoImplicit false

namespace GlobalTheory.LieFilt

theorem trCo_chart_pull {X Y : Scheme.{0}} {E : X.Modules} {r : ℕ} (hE : IsVB E r) (π : Y ⟶ X) (c c' : VB.Chart E r)
    (b a : Fin r) : trCo (c.pull hE π).isFrame (c'.pull hE π).e b a =
      π.appLE (c.U ⊓ c'.U) (π ⁻¹ᵁ c.U ⊓ π ⁻¹ᵁ c'.U) (fun _ hx => hx) (trCo c.isFrame c'.e b a) := by
  have := hE.isQuasicoherent
  have hle : π ⁻¹ᵁ c.U ⊓ π ⁻¹ᵁ c'.U ≤ π ⁻¹ᵁ (c.U ⊓ c'.U) := fun _ hx => hx
  have e := c.isFrame.pullback_basis_repr π inf_le_left hle (Twist.resM E inf_le_right (c'.e a)) b
  refine Eq.trans ?_ e
  exact congrArg (fun t => ((c.isFrame.pullback π).basis inf_le_left).repr t b)
    ((QCoh.res_pullbackSections π E le_rfl inf_le_right (c'.e a)).trans
      (QCoh.pullbackSections_res π E hle inf_le_right (c'.e a)).symm)

theorem trCo_chart_dual {X : Scheme.{0}} {E : X.Modules} {r : ℕ} (c c' : VB.Chart E r) (b a : Fin r) :
    trCo c.dual.isFrame c'.dual.e b a =
      X.presheaf.map (homOfLE (show c.U ⊓ c'.U ≤ c'.U ⊓ c.U from fun _ hx => ⟨hx.2, hx.1⟩)).op
        (trCo c'.isFrame c.e a b) := by
  change (c.isFrame.dual.basis inf_le_left).repr
    (Twist.resM (VB.dual E) inf_le_right (c'.isFrame.coord a)) b = _
  rw [VB.IsFrame.dual_basis_repr, VB.dualApp_res, VB.IsFrame.dualApp_coord]
  have e := c'.isFrame.repr_resM (inf_le_left : c'.U ⊓ c.U ≤ c'.U)
    (show c.U ⊓ c'.U ≤ c'.U ⊓ c.U from fun _ hx => ⟨hx.2, hx.1⟩) (Twist.resM E inf_le_right (c.e b)) a
  rw [Twist.resM_resM] at e
  exact e

theorem appLE_map_appLE {X Y Z : Scheme.{0}} (β : X ⟶ Y) (b : Y ⟶ Z) {U : Z.Opens} {V V' : Y.Opens} {T : X.Opens}
    (h₁ : V ≤ b ⁻¹ᵁ U) (h₂ : V' ≤ V) (h₃ : T ≤ β ⁻¹ᵁ V') (h₄ : T ≤ (β ≫ b) ⁻¹ᵁ U) (x : Γ(Z, U)) :
    β.appLE V' T h₃ (Y.presheaf.map (homOfLE h₂).op (b.appLE U V h₁ x)) = (β ≫ b).appLE U T h₄ x := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE]

theorem exists_dualCharts_pull_dual_pull : ∀ {k k' : Type} [CommRing k] [CommRing k'] (φ : k ≃+* k') {X Y Y' : Scheme.{0}} {F : Y'.Modules} {g : ℕ}
    {p' : Y' ⟶ Sp k'} (h : VMetric p' F g) (b : Y ⟶ Y') {p : Y ⟶ Sp k}
    (h₀ : VMetric p ((Scheme.Modules.pullback b).obj F) g), SameMet φ (h.pull b rfl) h₀ →
    ∀ (β : X ⟶ Y) {q : X ⟶ Sp k} (w : β ≫ p = q),
    ∃ (ℓ : ∀ c : VB.Chart F g, Fin g →
        Γ((Scheme.Modules.pullback β).obj (VB.dual ((Scheme.Modules.pullback b).obj F)), (β ≫ b) ⁻¹ᵁ c.U))
      (hℓ : ∀ c, VB.IsFrame (ℓ c)), DualCharts (β ≫ b) ℓ hℓ ∧
      ∀ (σ : k →+* ℂ) (σ' : k' →+* ℂ), σ' = σ.comp φ.symm.toRingHom → ∀ (z : CxPts q σ) (y : CxPts p' σ'),
        y.1 = z.1 ≫ β ≫ b → ∀ c : VB.Chart F g, y ∈ CxPts.ptsIn p' σ' c.U →
        ((h₀.dual.pull β w).met σ).G ⟨(β ≫ b) ⁻¹ᵁ c.U, ℓ c, hℓ c⟩ z = HermFrame.dualGram ((h.met σ').G c y) := by
  intro k k' _ _ φ X Y Y' F g p' h b p h₀ hs β q w
  refine ⟨fun c => ((c.pull h.isVB b).dual.pull h₀.isVB.dual β).e,
    fun c => ((c.pull h.isVB b).dual.pull h₀.isVB.dual β).isFrame, fun c c' j i => ?_, ?_⟩
  · refine (trCo_chart_pull h₀.isVB.dual β (c.pull h.isVB b).dual (c'.pull h.isVB b).dual j i).trans ?_
    rw [trCo_chart_dual, trCo_chart_pull]
    exact appLE_map_appLE β b _ _ _ _ _
  · rintro σ σ' rfl z y hy c hc
    let y₀ : CxPts p σ := Points.PtsOver.map β w _ z
    let y₁ : CxPts (b ≫ p') (σ.comp φ.symm.toRingHom) := ⟨z.1 ≫ β, by
      rw [← y.2, hy, Category.assoc, Category.assoc, Category.assoc]⟩
    have e : Points.PtsOver.map b rfl _ y₁ = y := Subtype.ext ((Category.assoc _ _ _).trans hy.symm)
    have hc₁ : Points.PtsOver.map b rfl _ y₁ ∈ CxPts.ptsIn p' _ c.U := e ▸ hc
    have hc₀ : y₀ ∈ CxPts.ptsIn p σ (c.pull h.isVB b).U := hc₁
    refine (((h₀.met σ).dual).pull_G β w (c.pull h.isVB b).dual hc₀).trans ?_
    refine ((h₀.met σ).dual_G (c.pull h.isVB b) hc₀).trans (congrArg _ ?_)
    refine (hs σ y₀ y₁ rfl _ hc₀).trans ?_
    exact ((h.met _).pull_G b rfl c hc₁).trans (congrArg _ e)

end GlobalTheory.LieFilt
