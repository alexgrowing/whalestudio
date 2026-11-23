import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

theorem spMap_comp_cellpt {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂)
    (g : R₂ →+* R₃) : spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem cellpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (b : A.B) (w : Pm Dw.mult) (S : Type) [CommRing S] (ψ₀ : Γ(Y.X, (A.V b).1) →+* S) (xc : CellVar Dw.mult → S) (z : Sp S ⟶ Z), z = spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w → z ≫ π = spMap ψ₀ ≫ (A.V b).2.fromSpec ∧ ∃ hz : ⊤ ≤ z ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult), ∀ σ, (cellFrames hZ ht).uAt ((b, w) : A.B × Pm Dw.mult) z hz σ = (((A.k b).u σ).map ψ₀).submatrix id (w σ) * Matrix.of (cell xc σ) := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht b w S _ ψ₀ xc z hzd
  refine ⟨?_, ?_⟩
  · rw [hzd, Category.assoc, hZ.plk.base b w, cbase, ← Category.assoc, spMap_comp_cellpt,
      MvPolynomial.eval₂Hom_comp_C]
  · have hz : ⊤ ≤ z ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult) := by
      intro x _
      show z x ∈ Set.range (κ b w)
      rw [hzd, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    refine ⟨hz, fun σ => ?_⟩
    have key : (ev z _ hz).comp (cellθ κ ((b, w) : A.B × Pm Dw.mult)).toRingHom = MvPolynomial.eval₂Hom ψ₀ xc := by
      have h1 := eq_spMap_ev (κ := κ) ((b, w) : A.B × Pm Dw.mult) z hz
      have h2 : spMap ((ev z _ hz).comp (cellθ κ ((b, w) : A.B × Pm Dw.mult)).toRingHom) =
          spMap (MvPolynomial.eval₂Hom ψ₀ xc) := by
        rw [← cancel_mono (κ b w)]
        exact h1.trans hzd
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    show ((uC A b w σ).map (cellθ κ ((b, w) : A.B × Pm Dw.mult))).map (ev z _ hz) = _
    change (uC A b w σ).map ((ev z _ hz).comp (cellθ κ ((b, w) : A.B × Pm Dw.mult)).toRingHom) = _
    rw [key, uC, Matrix.map_mul, Matrix.submatrix_map, Matrix.map_map]
    congr 1
    · congr 1
      ext i j
      simp [cC]
    · ext i j
      simp only [cellMat, Matrix.map_apply, Matrix.of_apply, cell]
      split_ifs <;> simp

end GlobalTheory.FlagMod.FieldFlag
