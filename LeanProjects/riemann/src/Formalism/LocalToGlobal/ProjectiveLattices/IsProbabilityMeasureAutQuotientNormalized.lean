import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta
open scoped Classical TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.Pj

variable {D : D7}

abbrev AutQ (V : HSp D) : Type := Quotient (QuotientGroup.rightRel (GQ V))

abbrev autMk (V : HSp D) (g : GA D V) : AutQ V := Quotient.mk _ g

def volPair (V : HSp D) : Measure (GA D V) × Set (GA D V) :=
  if h : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 then h.choose
  else Classical.epsilon fun p => ∃ P Q : D.what₂.Tau → ℕ, IsVolMeasG D V P Q p.1 ∧ IsFundamentalDomain (GQ V) p.2 p.1

def muQ (V : HSp D) : Measure (AutQ V) := ((volPair V).1.restrict (volPair V).2).map (autMk V)

def muQ1 (V : HSp D) : Measure (AutQ V) :=
  if muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤ then (muQ V Set.univ)⁻¹ • muQ V else Measure.dirac (autMk V 1)

instance isProbabilityMeasure_autQuotientNormalized (V : HSp D) : IsProbabilityMeasure (muQ1 V) := by
  unfold muQ1
  split_ifs with h
  · exact ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h.1 h.2]⟩
  · infer_instance

end Formalism.L2.Pj
