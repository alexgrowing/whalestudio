import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

theorem top (hP : SPois) (hI : SPois → SInt) (hG : SPois → SInt → SSmooth → SGrowth) (hS : SPois → SInt → SSmooth)
    (hL : SPois → SInt → SSmooth → SLeft) (hV : SPois → SInt → SSmooth → SLevel) (hO : SPois → SInt → SSmooth → SOpen) (hC : SPois → SInt → SSmooth → SCent)
    (hK : SPois → SInt → SSmooth → SKfin) (hW : SPois → SInt → SSmooth → SWt) (hLo : SPois → SInt → SSmooth → SLow) (hZ : SPois → SInt → SSmooth → SZfin)
    (hE : SPois → SInt → SSmooth → SExp) (hM : SPois → SInt → SSmooth → SSmul) : HilbertEisOne := by
  have hI' := hI hP
  have hS' := hS hP hI'
  intro F _ _ _ ω c hfin hodd hcond hram
  have H : Hyp ω c := ⟨hfin, hodd, hcond, hram⟩
  obtain ⟨C₀, L, hC₀, hexp⟩ := hE hP hI' hS' F ω c H
  have hs := hS' F ω c H
  let φ : UpperTheory.V.TR.Sm F 2 := ⟨Eis ω (Phi c), hs⟩
  have hlev : ∀ w, φ ∈ UpperTheory.V.Hi.fixd (locSm F w) (K1 w (c w)) := by
    intro w k hk
    refine Subtype.ext (funext fun g => ?_)
    exact hV hP hI' hS' F ω c H w k hk g
  have hcent := hC hP hI' hS' F ω c H
  have hwt := hW hP hI' hS' F ω c H hs
  have hlow := hLo hP hI' hS' F ω c H hs
  have hol : IsHol 1 c ω φ :=
    { aut := ⟨hL hP hI' hS' F ω c, hO hP hI' hS' F ω c H hs, hK hP hI' hS' F ω c H hs, hZ hP hI' hS' F ω c hfin φ hcent hwt hlow,
        hG hP hI' hS' F ω c H⟩
      level := hlev
      cent := hcent
      wt := hwt
      low := hlow }
  have hM' := hM hP hI' hS' F ω c 1 φ C₀⁻¹ (inv_ne_zero hC₀)
  refine ⟨C₀⁻¹ • φ, C₀⁻¹ * L, hM'.1 hol, ?_⟩
  have h2 := hM'.2 _ _ hexp
  convert h2 using 2
  rw [← mul_assoc, inv_mul_cancel₀ hC₀, one_mul]

end UpperTheory.HilbertEisensteinWeightOne
