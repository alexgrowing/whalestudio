import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrOfConjRes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceNormVEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.RoadU

open UpperTheory.V.Af in

theorem frobEig_of_dec {E Ω : Type} [Field E] [NumberField E]
    [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (π : CuspSub E a) (Q : GlobalTheory.RealGal.QCM E Ω) (P : CuspSub ↥Q.K a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l))
    (ρ : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hdec : ∀ A : ValuationSubring Ω, IsPlaceOver A w → Dec (F := E) A ≤ (Bc.res E Ω ↥Q.K).range)
    (hsph : ∀ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w → (CG.mk P).HasSat w' B → SphAt .unr P ι r w' B)
    (hP : IsLift π P) (hB : (CG.mk π).HasSat w B) (hiso : RepIso r (ρ.comp (Bc.res E Ω ↥Q.K)))
    (hunr : ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, ρ s = 1) :
    FrobEig ι ρ w (algSat a (normV w) B) := by
  intro A hA
  refine ⟨hunr A hA, fun σ hσ => ?_⟩
  obtain ⟨w', hw', hA', hq⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA (hdec A hA)
  obtain ⟨τ, rfl⟩ := hdec A hA hσ.1
  have hτ : IsFrob (F := ↥Q.K) A (normV w') τ := by
    rw [hq]
    exact ⟨hσ.1, hσ.2⟩
  have hl' : ((l : ℕ) : 𝓞 ↥Q.K) ∉ w'.asIdeal := by
    intro h
    apply hl
    rw [← hw']
    change ((l : ℕ) : 𝓞 E) ∈ Ideal.comap (algebraMap (𝓞 E) (𝓞 ↥Q.K)) w'.asIdeal
    simpa using h
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hw', hq]) (by rw [hw']; exact hB)
    simpa using this
  have key := ((hsph w' hw' hB' hl') A hA').2 τ hτ
  obtain ⟨g, hg⟩ := hiso
  have e : ρ (Bc.res E Ω ↥Q.K τ)⁻¹ = g * r τ⁻¹ * g⁻¹ := by
    rw [← map_inv]
    exact hg τ⁻¹
  rw [e, ← hq, ← key, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

open UpperTheory.V.Af in

theorem ex_all_of_good : Inputs → Ex .good → SphericalLevelCondition .good .unr → Ex .all := by
  intro hIn hEx hHolds E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc
  have hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL := GlobalTheory.automorphicFormsFiniteGL
  have hQL : QuadLift := GlobalTheory.QuadLiftBridge.quadLift hIn.ac hIn.js
  obtain ⟨hreg, hpol, -⟩ := hsc
  let S : Set (GlobalTheory.RealGal.QCM E Ω) := {Q | ∃ P : CuspSub ↥Q.K a, IsLift π P ∧ Good l P}
  have fam := GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π
  have famS : ∀ (Q : GlobalTheory.RealGal.QCM E Ω),
      (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) →
      (∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P) → Q ∈ S := by
    intro Q hram hgood
    obtain ⟨P, hP⟩ := hQL E ↥Q.K Q.two a ha π hram
    exact ⟨P, hP, hgood P hP⟩
  obtain ⟨v0⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩⟩
  have hS : S.Infinite := (fam v0).mono fun Q hQ => famS Q hQ.2.2.1 hQ.2.2.2
  choose P hP using fun Q : ↥S => Q.2
  have key : ∀ Q : ↥S, ∃ (χ' : HChar (maximalRealSubfield ↥Q.1.K)) (r : G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)),
      InScope .good l (P Q) χ' ∧ Weak (P Q) ι r := fun Q => by
    obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hIn.js hIn.gk E ↥Q.1.K l a ha π χ (P Q) (hP Q).1 ⟨hreg, hpol, trivial⟩
    have hs : InScope .good l (P Q) χ' := ⟨hχ'.1, hχ'.2.1, (hP Q).2⟩
    obtain ⟨r, hr⟩ := hEx ↥Q.1.K Ω l ι a ha (P Q) χ' hs
    exact ⟨χ', r, hs, hr⟩
  choose χ' r hχ' hr using key
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.CMBasePatch.main hAF E Ω l ι a π S hS P r fun Q => ⟨(hP Q).1, hr Q⟩
  refine ⟨ρ, hρc, hρs, ?_⟩
  haveI : Infinite ↥S := hS.to_subtype
  obtain ⟨Q0, hQ0⟩ := hev.exists
  have hunr := GlobalTheory.RealGal.ConjUnr.unr_of_conj_res E Ω Q0.1 l a ρ (r Q0) hQ0 ((hr Q0).2.2.mono fun w' hw' A hA => by
    obtain ⟨B, -, hF⟩ := hw'
    exact (hF A hA).1)
  have hlf : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hsat := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hAF E a π
  have hpick : ∀ w : HeightOneSpectrum (𝓞 E), ∃ Q : ↥S,
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → Dec (F := E) A ≤ (Bc.res E Ω ↥Q.1.K).range) ∧
      (∀ w' : HeightOneSpectrum (𝓞 ↥Q.1.K), w'.under (𝓞 E) = w → GlobalTheory.UnitaryBC.IsSplitAt w') ∧
      RepIso (r Q) (ρ.comp (Bc.res E Ω ↥Q.1.K)) := by
    intro w
    have hfin := (Filter.eventually_cofinite.1 hev).image Subtype.val
    obtain ⟨Q, hQ, hQn⟩ := ((fam w).diff hfin).nonempty
    have hQS : Q ∈ S := famS Q hQ.2.2.1 hQ.2.2.2
    refine ⟨⟨Q, hQS⟩, hQ.1, hQ.2.1, ?_⟩
    by_contra hc
    exact hQn ⟨⟨Q, hQS⟩, hc, rfl⟩
  filter_upwards [hlf, hsat, hunr] with w hl hB hu
  obtain ⟨B, hB⟩ := hB
  refine ⟨B, hB, ?_⟩
  obtain ⟨Q, hdec, hsplit, hiso⟩ := hpick w
  exact frobEig_of_dec ι π Q.1 (P Q) (r Q) ρ w B hl hdec
    (fun w' hw' hB' => hHolds ↥Q.1.K Ω l ι a ha (P Q) (χ' Q) (hχ' Q) (r Q) (hr Q) w' (hsplit w' hw') B hB')
    (hP Q).1 hB hiso hu

end GlobalTheory.RoadU
end
