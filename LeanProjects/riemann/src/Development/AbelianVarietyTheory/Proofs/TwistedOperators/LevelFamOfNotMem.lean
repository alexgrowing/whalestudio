import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.TrIdem

def normInd {G : Type} [MeasurableSpace G] (μ : Measure G) (H : Set G) : G → ℂ :=
  (μ.real H : ℂ)⁻¹ • H.indicator 1

variable {D : D7} {V : HSp D}

def kerSub (T : TypeDataG V) (v : T.S) : Subgroup (GLoc D.sp.cm.sig V.gram v) :=
  ((T.frame v).red.ker).map (Kv V v).subtype

def levelFam (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v) :=
  Function.update (fun v => if hv : v ∈ T.S then kerSub T ⟨v, hv⟩ else Kv V v) U.u U.frame.iwahori

def fam (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ :=
  fun v => if hv : v ∈ T.S ∧ v ∈ A then T.idem μf ⟨v, hv.1⟩ else normInd (μf v) (levelFam T U v : Set _)

variable (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
  (A : Finset (HeightOneSpectrum (𝓞 D.host.F)))

theorem levelFam_u : levelFam T U U.u = U.frame.iwahori := Function.update_self ..

theorem levelFam_of_mem (hu : U.u ∉ T.S) (v : T.S) : levelFam T U v = kerSub T v := by
  have : (v : HeightOneSpectrum (𝓞 D.host.F)) ≠ U.u := fun e => hu (e ▸ v.2)
  rw [levelFam, Function.update_of_ne this, dif_pos v.2]

theorem levelFam_of_notMem {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ T.S) (hu : v ≠ U.u) :
    levelFam T U v = Kv V v := by
  rw [levelFam, Function.update_of_ne hu, dif_neg hv]

theorem fam_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ T.S) (hA : v ∈ A) :
    fam T U μf A v = T.idem μf ⟨v, hv⟩ := dif_pos ⟨hv, hA⟩

theorem fam_of_not {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ¬ (v ∈ T.S ∧ v ∈ A)) :
    fam T U μf A v = normInd (μf v) (levelFam T U v : Set _) := dif_neg h

end GlobalTheory.TrIdem
