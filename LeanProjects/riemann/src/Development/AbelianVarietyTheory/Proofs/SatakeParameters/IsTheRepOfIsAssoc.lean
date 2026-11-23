import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseFrobOutside
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvTransposeInvTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

namespace GlobalTheory.CarUniq

theorem isTheRep_of_isAssoc : LocalLanglandsExists → RecUnique → AutomorphicFormsFiniteGL → IrreducibleAdmissibleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (R : G E Ω →* GL (Fin a) (Qbar l)), GlobalTheory.CarHyp.IsAssoc π ι R → GlobalTheory.CarHyp.IsTheRep π ι R := by
  intro hLL hU hAF hIA E Ω _ _ _ _ _ _ l _ ι a π R hR
  refine ⟨hR, fun R' hR' => ?_⟩
  refine GlobalTheory.TraceConjCofinite.main E Ω l a R R' hR.cont hR'.cont hR.ss hR'.ss ?_
  have hl : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    have h0 : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_)
    exact Ideal.dvd_span_singleton.2 (not_not.1 hv)
  filter_upwards [GlobalTheory.CuspRep.LocSph.locComp_spherical E a π, hl] with w hw hlw A h σ
  obtain ⟨rc, hrc⟩ := hLL E Ω A w h
  have hrc' := hU.isTheRec hrc
  obtain ⟨s, hs, had⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hAF E a π w
  obtain ⟨v, h0, hv⟩ := hw s hs
  have hsp : SmGL.IsSpherical s.ρ := by
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩
    obtain ⟨x, hx⟩ := x
    rw [SmGL.SphCompletion.KO_completion] at hx
    obtain ⟨g, rfl⟩ := hx
    exact (hv g).trans (one_smul _ _).symm
  have hirr := (GlobalTheory.ContraRefl.contra_irreducible_reflexive _ (GlobalTheory.LocalThetaGL.compact_open_basis _) _ _
    s.ρ s.ρ had had).1 s.irred
  let s' : SmIrr (GL (Fin a) (w.adicCompletion E)) :=
    { V := _, ρ := SmGL.contra s.ρ, smooth := SmGL.isSmooth_contra _, irred := hirr }
  have e : Nonempty (s'.ρ.Equiv (SmGL.contra s.ρ)) := ⟨.refl _⟩
  have h1 := hR.unr w hlw A h rc hrc' s s' hs hsp e
  have h2 := hR'.unr w hlw A h rc hrc' s s' hs hsp e
  have hx := isWDOf_wdOf (h := h) hlw ι (Units.continuous_val.comp hR.cont)
  have hx' := isWDOf_wdOf (h := h) hlw ι (Units.continuous_val.comp hR'.cont)
  rw [h1] at hx
  rw [h2] at hx'
  exact GlobalTheory.WdTrace.trace_eq_of_isWDOf E Ω l ι a R R' w A h _ hx hx' σ

end GlobalTheory.CarUniq

end
