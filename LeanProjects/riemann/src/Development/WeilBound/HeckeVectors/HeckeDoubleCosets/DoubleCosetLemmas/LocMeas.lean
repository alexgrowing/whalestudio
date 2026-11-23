import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.ExtendedCharacterCongrOfTame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBallsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MatrixHaarRightTranslateStatement

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def dM [MeasurableSpace (Cv v)] (μ : Measure (Cv v)) (n m : ℕ) :
    Measure (Matrix (Fin n) (Fin m) (Cv v)) :=
  (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => μ : Measure (Fin n → Fin m → Cv v))

structure Pack [MeasurableSpace (Cv v)] (μ : Measure (Cv v)) : Prop where
  sf : SigmaFinite μ
  sc : SecondCountableTopology (Cv v)
  pos : ∀ n m, (dM μ n m).IsOpenPosMeasure
  one : μ {x | Valued.v x ≤ 1} = 1
  scale : ∀ c : Cv v, c ≠ 0 → ∀ S, MeasurableSet S →
    μ ((· * c) ⁻¹' S) = ENNReal.ofReal (absV v c)⁻¹ * μ S
  left : ∀ n m, ∀ k ∈ KGL v n, Measure.map (fun x => k.1 * x) (dM μ n m) = dM μ n m
  right : ∀ n m, ∀ k ∈ KGL v m, Measure.map (fun x => x * k.1) (dM μ n m) = dM μ n m
  prod : ∀ r d c, MeasurePreserving
    (fun x : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v) => ((bAA x, bDA x), (bAD x, bDD x)))
    (dM μ (r + d) (r + c)) (((dM μ r r).prod (dM μ d r)).prod ((dM μ r c).prod (dM μ d c)))

end CompanionTheory.D.Upq.DoubleCosetLemmas
