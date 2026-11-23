import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def TupTied.InQ' {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (μ : D.what₂.Tup)
    (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ w ∈ aboveF (L := D.host.E) D.host.F v, ¬ (Tp.xi μ).UnrAt w

structure DivisorCharacterCompatibility (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) (Z : DivX D) where
  Qp_iff : ∀ μ p, p ∈ Z.Qp μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w
  eQPl : ∀ μ, Z.QPl μ ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}
  qv_eq : ∀ μ v, Z.qv μ v = Ideal.absNorm (eQPl μ v).1.asIdeal

end Formalism.L2.Host
