import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SeparableConjugates.ExistsHasSatakeOfUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}
theorem exists_hasSatake_of_unr_alt (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : IrrRep (GL (Fin a) (w.adicCompletion E))}
    (hu : (rc (cls σ)).unr) : ∃ α, HasSatake σ.ρ α := by
  obtain ⟨m, c, e⟩ := Unram.exists_diag hu
  have H' := H
  first | (have hOpn := UpperTheory.One.M.opn _ (H'); obtain ⟨_, _, _, H'⟩ := hOpn) | obtain ⟨_, _, _, -, H'⟩ := H'
  obtain rfl : a = m := by simpa [e] using (H'.dim (cls σ)).symm
  obtain ⟨τ, hτ⟩ := exists_hasSatake (k := w.adicCompletion E) fun i => (c i)⁻¹
  have e2 := _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hτ
  simp only [inv_inv] at e2
  have g : UpperTheory.Zero.LLC.Good (cls σ) :=
    (GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz _ _ ((H'.sph _).2 hu)).2
  obtain ⟨φ⟩ := (IrrGL.of_eq_of (π := τ.ρ) (σ := σ.ρ) (hs := τ.smooth) (hi := τ.irr) (hs' := σ.smooth) (hi' := σ.irr)).1
    (_root_.UpperTheory.One.M.LawsM.inj H' (cls τ) (cls σ) g (e2.trans e.symm))
  exact ⟨_, σ.irr, fixed_ne_bot_of_equiv φ hτ.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hτ.2.2⟩
end UpperTheory.One.M
end
end
