import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM.Cht

theorem isFrame_congr_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l l' : Level H} {c : Coeff l} {c' : Coeff l'} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R]
    {f : c.F →+* R} {f' : c'.F →+* R} (h : ∀ τ a, f' (embK c' τ a) = f (embK c τ a)) (x : Sp R ⟶ X) (u : Vecs Dw t R) :
    GlobalTheory.LocM.IsFrame t f' x u ↔ GlobalTheory.LocM.IsFrame t f x u := by
  simp only [GlobalTheory.LocM.IsFrame, h]

theorem frameMove : FrameMoveSt := by
  intro E _ _ _ H Dw l l' c c' X X' t t' g m R _ f f' x h
  refine ⟨fun u' hu => ?_, fun u hu => ?_⟩
  · exact (BaseMdl.frame_push m f u' fun τ i => (hu.1 τ i).1.1).1 ((isFrame_congr_coeff t' h x u').1 hu)
  · choose u' h1 h2 using fun τ i => BaseMdl.exists_lift m (hu.1 τ i).1.1
    refine ⟨u', (isFrame_congr_coeff t' h x u').2 ((BaseMdl.frame_push m f u' h2).2 ?_), h1⟩
    rw [show (fun τ i => u' τ i ≫ m.φ : Vecs Dw t R) = u from funext fun τ => funext fun i => h1 τ i]
    exact hu

end GlobalTheory.LocM.Cht
