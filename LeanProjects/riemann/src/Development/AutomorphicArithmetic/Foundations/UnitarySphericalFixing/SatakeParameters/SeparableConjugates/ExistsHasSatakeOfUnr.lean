import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem exists_hasSatake_of_unr (H : IsRec h rc) {σ : IrrRep (GL (Fin a) (w.adicCompletion E))}
    (hu : (rc (cls σ)).unr) : ∃ α, HasSatake σ.ρ α := by
  obtain ⟨m, c, e⟩ := Unram.exists_diag hu
  have H' := H
  obtain ⟨_, _, _, -, H'⟩ := H'
  obtain rfl : a = m := by simpa [e] using (H'.dim (cls σ)).symm
  obtain ⟨τ, hτ⟩ := exists_hasSatake (k := w.adicCompletion E) fun i => (c i)⁻¹
  have e2 := rec_eq_diag H hτ
  simp only [inv_inv] at e2
  have g : UpperTheory.Zero.LLC.Good (cls σ) :=
    (GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz _ _ ((H'.sph _).2 hu)).2
  obtain ⟨φ⟩ := (IrrGL.of_eq_of (π := τ.ρ) (σ := σ.ρ) (hs := τ.smooth) (hi := τ.irr) (hs' := σ.smooth) (hi' := σ.irr)).1
    (Old.inj H' (cls τ) (cls σ) g (e2.trans e.symm))
  exact ⟨_, σ.irr, fixed_ne_bot_of_equiv φ hτ.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hτ.2.2⟩

example : type_of% @GlobalTheory.CuspRep.ParLaws.exists_hasSatake_of_unr := @exists_hasSatake_of_unr

end UpperTheory.One.M
