import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.GodementEis
import GroundTheory.GlobalFields.TateThesis.TateMain

open NumberField Matrix MeasureTheory
open scoped NumberField.AdeleRing

namespace PositivityTheory.EisRk1

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection
  IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

noncomputable def theta2 (F : (Fin 2 → 𝔸[K]) → ℂ) (h : GL (Fin 2) 𝔸[K]) : ℂ :=
  ∑' ξ : Fin 2 → K, F ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K]))

noncomputable def scal (a : IdeleGroup K) : GL (Fin 2) 𝔸[K] := borelElt a a 0

noncomputable def theta2Integral (w : InfinitePlace K) (F : (Fin 2 → 𝔸[K]) → ℂ)
    (μ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ u in normOneFundamentalDomain K,
    theta2 F (scal (moduleSection w t * (u : IdeleGroup K))) * (μ.toIdele (u : IdeleGroup K) : ℂ)
      ∂normOneMeasure K

noncomputable def theta2Fun (w : InfinitePlace K) (F : (Fin 2 → 𝔸[K]) → ℂ)
    (μ : HeckeCharacter K) (x : ℝ) : ℂ :=
  if hx : 0 < x then theta2Integral w F μ ⟨x, hx⟩ else 0

noncomputable def theta2Const (F : (Fin 2 → 𝔸[K]) → ℂ) (μ : HeckeCharacter K) : ℂ :=
  F 0 * ∫ u in normOneFundamentalDomain K, (μ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K

end PositivityTheory.EisRk1
