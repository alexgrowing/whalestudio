import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexConjAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnramifiedAtOfInertiaEqBot
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.CsdLift

theorem evenReal (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (h : Even (Module.finrank ℚ (maximalRealSubfield E))) :
    Even (Module.finrank ℚ (maximalRealSubfield M)) := by
  have hE : Module.finrank ℚ E = Module.finrank ℚ (maximalRealSubfield E) * 2 := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
  have hM : Module.finrank ℚ M = Module.finrank ℚ (maximalRealSubfield M) * 2 := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield M) M, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield M) M]
  have hEM : Module.finrank ℚ M = Module.finrank ℚ E * Module.finrank E M :=
    (Module.finrank_mul_finrank ℚ E M).symm
  obtain ⟨k, hk⟩ := h
  refine ⟨k * Module.finrank E M, ?_⟩
  have : Module.finrank ℚ (maximalRealSubfield M) * 2 = (k * Module.finrank E M) * 2 + (k * Module.finrank E M) * 2 := by
    rw [← hM, hEM, hE, hk]; ring
  omega

theorem unramUp (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (w : HeightOneSpectrum (𝓞 M))
    (h : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) (w.under (𝓞 E)).asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield M)) w.asIdeal := by
  set v := w.under (𝓞 E) with hvdef
  have hv : v.asIdeal.inertia (E ≃ₐ[maximalRealSubfield E] E) = ⊥ := by
    haveI := v.isMaximal
    haveI : (v.asIdeal.under (𝓞 (maximalRealSubfield E))).IsMaximal := Ideal.IsMaximal.under _ _
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx (v.asIdeal.under (𝓞 (maximalRealSubfield E))) v.asIdeal
        (E ≃ₐ[maximalRealSubfield E] E),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[maximalRealSubfield E] E)
        (v.asIdeal.under (𝓞 (maximalRealSubfield E))) v.asIdeal] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  apply GlobalTheory.isUnramifiedAt_of_inertia_eq_bot (maximalRealSubfield M) M w.asIdeal w.ne_bot
  have hcard : Nat.card (M ≃ₐ[maximalRealSubfield M] M) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  haveI : Fact (Nat.card (M ≃ₐ[maximalRealSubfield M] M)).Prime := ⟨hcard ▸ Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (w.asIdeal.inertia (M ≃ₐ[maximalRealSubfield M] M)) with h1 | h1
  · exact h1
  exfalso
  have hc : IsCMField.complexConj M ∈ w.asIdeal.inertia (M ≃ₐ[maximalRealSubfield M] M) := h1 ▸ Subgroup.mem_top _
  have hcE : IsCMField.complexConj E ∈ v.asIdeal.inertia (E ≃ₐ[maximalRealSubfield E] E) := by
    intro y
    have := hc (algebraMap (𝓞 E) (𝓞 M) y)
    show _ ∈ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M))
    rw [Ideal.mem_comap]
    have e : algebraMap (𝓞 E) (𝓞 M) (IsCMField.complexConj E • y - y) =
        IsCMField.complexConj M • algebraMap (𝓞 E) (𝓞 M) y - algebraMap (𝓞 E) (𝓞 M) y := by
      rw [map_sub]
      congr 1
      apply RingOfIntegers.ext
      first
        | exact (GlobalTheory.LiftPolar.conj_algebraMap (y : E)).symm
        | simpa using (GlobalTheory.LiftPolar.conj_algebraMap (y : E)).symm
    rw [e]
    exact this
  rw [hv, Subgroup.mem_bot] at hcE
  exact IsCMField.complexConj_ne_one E hcE

theorem val_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).val w = 1 := by
  rfl

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

theorem compNorm_quadChar_pow (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) :
    compNorm E (quadChar E ^ a) = 1 := by
  rw [map_pow, compNorm_quadChar, one_pow]

theorem main : JacquetShalikaRigidity → GelfandKazhdanDual → ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (π' : CuspSub M a), IsLift π π' → InScope .csd l π (quadChar E ^ a) → InScope .csd l π' (quadChar M ^ a) := by
  intro hJ hG E M _ _ _ _ _ _ _ l a ha π π' hL hS
  have hF := GlobalTheory.automorphicFormsFiniteGL
  obtain ⟨⟨χ', hreg', -⟩, -⟩ := GlobalTheory.LiftPolar.main hF hJ hG E M l a ha π _ π' hL ⟨hS.1, hS.2.1, trivial⟩
  obtain ⟨-, hpol, ⟨hx, heven, hns⟩, -⟩ := hS
  refine ⟨hreg', ⟨fun v => by rw [locInf_pow, quadChar_locInf], ?_⟩, ⟨?_, ?_, ?_⟩, rfl⟩
  · rw [compNorm_quadChar_pow]
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha π' 1 ?_
    have hsd := GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace hF E a π _ hpol
    have hun := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π
    filter_upwards [(GlobalTheory.LiftPolar.tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hs, B, hB⟩
    rw [compNorm_quadChar_pow] at hs
    have e1 := GlobalTheory.LiftPolar.cPl_under (E := E) w
    have e2 := GlobalTheory.LiftPolar.normV_cPl w
    have e3 := GlobalTheory.LiftPolar.normV_cPl (w.under (𝓞 E))
    have hf := GlobalTheory.LiftPolar.normV_under (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    have hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B := (CG.hasSat_mk _ _ _).2 hB
    have h1 := hL.sat w f B hf hB0
    have h2 := hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)
    refine ⟨unrAt_one w, _, _, h1, h2, ?_⟩
    simp only [val_one, Multiset.map_map, Function.comp_def, mul_one, inv_one, inv_pow, inv_inv]
  · obtain ⟨x, d, hd, hx2⟩ := hx
    exact ⟨algebraMap E M x, d, hd, by rw [← map_pow, hx2]; simp⟩
  · exact evenReal E M heven
  · intro w hw
    have hv : ¬ IsSplitAt (w.under (𝓞 E)) := fun h => hw (GlobalTheory.IndDataDown.isSplitAt_of_under E M _ w rfl h)
    obtain ⟨hl, hu, B, hB⟩ := hns _ hv
    refine ⟨fun h => hl ?_, unramUp E M w hu, ⟨_, hL.sat w _ B (GlobalTheory.LiftPolar.normV_under w) hB⟩⟩
    show (l : 𝓞 E) ∈ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M))
    rw [Ideal.mem_comap, map_natCast]
    exact h

end GlobalTheory.CsdLift

end
