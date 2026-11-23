import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentreChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.Transfer

theorem nonempty_place (K : Type) [Field K] [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩⟩

theorem transferLaw_of_normalCharts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.regular₂ Xo c U := by
  intro E _ _ _ H Dw l Xo c h r U
  have hs : ∀ {a n} {f : Rul Xo c}, f ∈ Formalism.L2.PjFree.cusp Xo c U a n → f ∈ sec Xo c a n :=
    fun hf => Formalism.L2.PjFree.cusp_le_sec Xo c U _ _ hf
  obtain ⟨la0⟩ := nonempty_place c.F
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro w F h0
    refine ⟨fun la y' => ?_, fun q => ?_⟩
    · obtain ⟨S, -⟩ := (h la).1
      exact integral_place S (hs F.2) (fun v hv => h0 la ⟨v, hv⟩) y'.1 y'.2
    · obtain ⟨S, hQ⟩ := (h la0).1
      exact integral_trivial S hQ (hs F.2) (fun v hv => h0 la0 ⟨v, hv⟩) q.1 q.2
  · intro wL wE n ws et nu c' hc' hNZ hyp
    refine ⟨fun la y' => ?_, fun q => ?_⟩
    · obtain ⟨S, hSF, -⟩ := (h la).2 wL.1.1 wL.1.2 n (fun i => (ws i).1) (fun i => hs (ws i).2) hNZ
      exact ⟨integral_place S (hs et.2) (fun v hv => (hyp la ⟨v, hv⟩).1) y'.1 y'.2,
        fun hT => combined_place S _ hSF (fun k => hs (ws k).2) (hs et.2) (nu la) c' hc'
          (fun v hv => hyp la ⟨v, hv⟩) y'.1 y'.2 hT⟩
    · obtain ⟨S, hSF, hQ⟩ := (h la0).2 wL.1.1 wL.1.2 n (fun i => (ws i).1) (fun i => hs (ws i).2) hNZ
      exact ⟨integral_trivial S hQ (hs et.2) (fun v hv => (hyp la0 ⟨v, hv⟩).1) q.1 q.2,
        fun hT => combined_trivial S hQ _ hSF (fun k => hs (ws k).2) (hs et.2) (nu la0) c' hc'
          (fun v hv => hyp la0 ⟨v, hv⟩) q.1 q.2 hT⟩
  · intro a n _ m ws hws hNZ nu hyp la v hv
    obtain ⟨S, hSF, -⟩ := (h la).2 a n m ws (fun i => hs (hws i)) hNZ
    exact family_place S ws hSF (fun i => hs (hws i)) (nu la) (hyp la) v hv

end GlobalTheory.Reg.Transfer
