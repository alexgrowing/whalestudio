import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS
open UpperTheory.ConvolutionTheory.R

private theorem exPow (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : ∃ ν : ℂ → HChar E,
    ∀ z v, (ν z).UnrAt v ∧ ((ν z).val v : ℂ) = (normV v : ℂ) ^ (-z) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ → HChar E, ∀ t, (a t).IsAbsPow t :=
    ⟨UnitExponent.nu E, fun t => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) t⟩
  obtain ⟨b, hb, -⟩ := norm_exponent_equality E
  refine ⟨fun z => a z.re * b z.im, fun z v => ⟨fun x hx => ?_, ?_⟩⟩
  · rw [HChar.loc_mul, (ha _).1 v x hx, (hb _ v).1 x hx, one_mul]
  · have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    rw [HChar.val_mul, Units.val_mul, (ha _).2.1 v, (hb _ v).2, ← Complex.cpow_add _ _ h0, ← neg_add, Complex.re_add_im]
    rfl
