import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.AbelianUnitPowers.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NormOneOfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.WideOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FrobDual

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

section CongLemmas

variable {l : ℕ} [Fact l.Prime]

private theorem cong_trans {a b c : (Qbar l)ˣ} (h : Cong a b) (h' : Cong b c) : Cong a c := by
  unfold Cong at *
  have := IsUltrametricDist.norm_add_le_max ((a : Qbar l) - b) ((b : Qbar l) - c)
  rw [sub_add_sub_cancel] at this
  exact this.trans_lt (max_lt h h')

private theorem cong_norm {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : ‖(a : Qbar l)‖ = 1 := by
  unfold Cong at h
  have := IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := (a : Qbar l)) (y := -(b : Qbar l))
    (by rw [← sub_eq_add_neg, norm_neg, hb]; exact h.trans_le (le_max_right _ _))
  rw [this, norm_neg, hb]

private theorem cong_mul_right {a b : (Qbar l)ˣ} (h : Cong a b) (c : (Qbar l)ˣ) (hc : ‖(c : Qbar l)‖ = 1) :
    Cong (a * c) (b * c) := by
  unfold Cong at *
  rw [Units.val_mul, Units.val_mul, ← sub_mul, norm_mul, hc, mul_one]
  exact h

private theorem cong_mul {a b c d : (Qbar l)ˣ} (h : Cong a b) (h' : Cong c d) (hb : ‖(b : Qbar l)‖ = 1)
    (hd : ‖(d : Qbar l)‖ = 1) : Cong (a * c) (b * d) := by
  refine cong_trans (cong_mul_right h c (cong_norm h' hd)) ?_
  rw [mul_comm b c, mul_comm b d]
  exact cong_mul_right h' b hb

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

end CongLemmas

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

end Gal

section Shape

variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

end Shape

end UpperTheory.V.Sd
