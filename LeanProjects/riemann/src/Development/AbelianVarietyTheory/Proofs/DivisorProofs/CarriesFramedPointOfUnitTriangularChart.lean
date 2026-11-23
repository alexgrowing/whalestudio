import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagMod.Frames

theorem lies_of_chart_tri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (F : Frames Y π), F.TopEigen → ∀ (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (z : Sp S ⟶ Z) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hx : z ≫ π = frX P ≫ Y.j) (U : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ σ, (U σ).BlockTriangular id) → (∀ σ i, IsUnit (U σ i i)) → (∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • F.vecAt k z hz hx σ j) → F.Lies z P := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F hT S _ _ P z k hz hx U hU hd hv
  obtain ⟨Q, hQ⟩ := hT.exists_chartFr (frX_snd P) hx k hz
  have hQx : frX Q ≫ Y.j = frX P ≫ Y.j := hQ.over.trans hx
  have hv' : ∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • frVec Y Q hQx σ j := fun σ i => by
    rw [hQ.frVec_eq hx hQx]; exact hv σ i
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) hQx.symm]
  have hB : ∃ t, FrBor t Q P := by
    have hM := F.inM hz hx
    clear hv hQ
    revert hv' hQx hM
    obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
    dsimp only at e
    subst e
    intro hQx hv' hM
    obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
    exact ⟨_, frBor_of_frVec hM hQx rfl
      (fun ix => match ix with | none => u0 | some p => (hd p.1 p.2).unit) U hU (fun _ _ => rfl) hv' fun _ => hu0⟩
  obtain ⟨t, ht⟩ := hB
  exact hQ.lies.frBor ht

end GlobalTheory.FlagMod.Frames
