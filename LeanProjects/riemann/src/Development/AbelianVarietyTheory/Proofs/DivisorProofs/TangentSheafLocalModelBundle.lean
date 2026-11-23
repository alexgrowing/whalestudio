import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSectionsFormFrameStatement
open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

namespace GlobalTheory.TanSec

theorem isVB_om : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p)
    (Z : GlobalTheory.LocM.Mdl Y i₀) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x → GlobalTheory.VB.IsVB (GlobalTheory.TanSec.om Z) r := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z r x hx
  have hfr := GlobalTheory.T.tangent_sections_form_frame E H Dw Xo p W Y i₀ Z r x hx
  have := (Y Z.i).t.semi
  have := (Y Z.i).t.semi.smooth
  intro y
  obtain ⟨U, n, s, hyU, hs⟩ := GlobalTheory.LieVB.exists_isFrame_omega (Y Z.i).t.G (Z.π y)
  have hs' := hs.pullback Z.π
  have hyU' : y ∈ Z.π ⁻¹ᵁ U := hyU
  obtain ⟨z, hzU, hzo⟩ := Z.dense.inter_open_nonempty _ (Z.π ⁻¹ᵁ U).isOpen ⟨y, hyU'⟩
  rw [← Z.cover] at hzo
  obtain ⟨a, hza⟩ := Set.mem_iUnion.1 hzo
  have hn : n = r := by
    have b₁ := hs'.dual.stalkBasis z hzU
    have b₂ := (hfr a).stalkBasis z hza
    simpa using Fintype.card_congr (b₁.indexEquiv b₂)
  subst hn
  exact ⟨_, _, hyU', hs'⟩

end GlobalTheory.TanSec
