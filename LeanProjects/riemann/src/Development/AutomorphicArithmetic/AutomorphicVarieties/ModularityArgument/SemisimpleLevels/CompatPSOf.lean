import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.SignFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

private theorem compatK (P : Hypotheses₂) (hS : CsdSs) {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} (hn : 2 ≤ n) {r : G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hr : Continuous r) (hreg : (CG.mk π).IsRegAlg) (hd : GlobalTheory.ContraPair.DualIsConj π) (ha : AttC ι r π)
    {w : HeightOneSpectrum (𝓞 K)} {A : ValuationSubring Ω} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : Induces Bw) :
    IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := K) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
      SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := K) A).subtype)) (rc (algNorm σ)) := by
  obtain ⟨R, hc, hs, Haw, Hab⟩ := hS K Ω l ι n hn π hd (P.litN.aut.coh K n (by omega) π hreg)
  obtain ⟨p, hp⟩ : RepIso R r := by
    refine isoOfFrob P K Ω l ι n R r hc hr hs ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem K l] with w ⟨B, hB, hf⟩ hw
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    exact ⟨_, satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => Haw w hw A h rc hrc σ hσ, hf⟩
  have h1 := Hab _ _ (Loc.tiedP l) w A h O Bw hj
  have h3 := GlobalTheory.PstConj.main K Ω l ι n _ _ (Loc.tiedP l) w A h O Bw hj (R.comp (Dec (F := K) A).subtype)
    (r.comp (Dec (F := K) A).subtype) p (fun g => hp g.1) h1.1
  exact ⟨h3.1, fun σ hσ rc hrc => h3.2 ▸ h1.2 σ hσ rc hrc⟩

end UpperTheory.V.Lev

open UpperTheory.V.Lev in
theorem UpperTheory.V.Lev.compatPSOf :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lev.CsdSs → UpperTheory.V.Lev.CompatPS := by
  intro P hS K _ _ _ hK n hn l _ Ω _ _ _ ι r π hr hreg hpol hatt w A h O _ _ _ Bw hj
  obtain ⟨χ₀, hχ₀⟩ := hpol
  obtain ⟨χ, -, wt, HT, hN, -, -, hall⟩ := galoisExistence_from_published P K Ω l ι n (by omega) π χ₀ hreg
    (fun v v' => (hχ₀.sign v).trans (hχ₀.sign v').symm) hχ₀.dual
  have hG := hall r hr hatt
  have hpst : IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := K) A).subtype) := by
    obtain ⟨T⟩ := Loc.tiedP l
    exact P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hr.comp continuous_subtype_val))
      (hG.above _ _ ⟨T⟩ w A h O Bw hj).1
  refine ⟨hpst, fun σ hσ rc hrc hab => ?_⟩
  obtain ⟨μ₀, ⟨-, -, a, -, hχa, -⟩, -⟩ := hG.pol
  have hχa' : IsAlgPos χ⁻¹ (-a) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hχa k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨k, b, hb⟩ := Cq.signFix K hK χ⁻¹ (-a) hχa'
  obtain ⟨κ, mκ, hκ, hκχ⟩ := Cq.extReal K _ b hb
  have hcsd : GlobalTheory.ContraPair.DualIsConj (π.twist κ) := Cq.csdTwist K n π _ κ hχ₀.dual (by
    rw [hκχ, map_mul, map_pow, compNorm_quadChar, one_pow, mul_one, map_inv, hN])
  obtain ⟨artK, hartK, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt P.litN.aut.art).1 K Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ mκ (isAlgPos_of_isAlg hκ)
  obtain ⟨c1, c2⟩ := compatK P hS hn (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ n _ μ hr hμc) (regAlg_twist hreg hκ) hcsd
    (Cq.attTwist K Ω l ι n _ π hatt artK κ mκ μ hartK hμ) h Bw hj
  obtain ⟨ν, hν⟩ := hab
  exact Lev.untwistS P.litN.aut.chA P.litN.aut.chW P.litN.aut.berger K Ω l ι n _ hr artK κ mκ μ hartK
    (isAlgPos_of_isAlg hκ) hμc hμ w A h O Bw hj hpst c1 σ rc hrc (c2 _ (hσ.twist κ) rc hrc)
    (Or.inl ((Lev.ssCalc K Ω A w h).1 n _ ν hν))

end
