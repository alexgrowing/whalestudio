import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkingRootsDilationCoprimeLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marking_roots_dilation_coprime_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (r n : ℕ) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (m : ℤ), IsCoprime m (l.M : ℤ) → (IsMark l L mk → IsMark l L (m • mk)) ∧ ∀ (N : ℕ) (Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E), ((∀ a, mk a ∈ L) → IsRoots l L mk N Y → IsRoots l L (m • mk) N (fun q => Y (m • q))) ∧ ∀ (g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (w : E) (Λ : Lt E n) (v : TF n g) (c : (Fin n → LevQ Dw l) → ℂ), gphi X bas w Λ L v (fun q => c (m • q)) (fun q => Y (m • q)) = gphi X bas w Λ L v c Y := by
  first | exact @GlobalTheory.DilateLevel.dilate | exact GlobalTheory.DilateLevel.dilate | (intros; apply GlobalTheory.DilateLevel.dilate <;> assumption)
