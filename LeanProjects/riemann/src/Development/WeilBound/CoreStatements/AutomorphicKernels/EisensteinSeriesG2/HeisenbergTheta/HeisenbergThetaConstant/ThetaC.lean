import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import GroundTheory.GlobalFields.TateThesis.TateMain

open NumberField Matrix MeasureTheory
open scoped NumberField.AdeleRing

namespace PositivityTheory.He2M1

open GroundTheory.Global GroundTheory.Automorphic IdeleGroup PositivityTheory.RgEis

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def ltr (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) : (ι → 𝔸[k]) → ℂ :=
  fun x ↦ F ((A : Matrix ι ι 𝔸[k]) *ᵥ x)

noncomputable def thetaC (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) : ℂ :=
  ∑' ξ : ι → k, F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)

noncomputable def scalC (a : IdeleGroup k) : GL ι 𝔸[k] :=
  Units.map (Matrix.scalar ι : 𝔸[k] →+* Matrix ι ι 𝔸[k]).toMonoidHom a

noncomputable def thetaCInt (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ u in normOneFundamentalDomain k,
    thetaC F (scalC (moduleSection w t * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ)
      ∂normOneMeasure k

noncomputable def thetaCFun (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (x : ℝ) : ℂ :=
  if hx : 0 < x then thetaCInt w F ω ⟨x, hx⟩ else 0

noncomputable def volChar (ω : HeckeCharacter k) : ℂ :=
  ∫ u in normOneFundamentalDomain k, (ω.toIdele (u : IdeleGroup k) : ℂ) ∂normOneMeasure k

noncomputable def thetaCConst (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) : ℂ :=
  F 0 * volChar ω

end PositivityTheory.He2M1
