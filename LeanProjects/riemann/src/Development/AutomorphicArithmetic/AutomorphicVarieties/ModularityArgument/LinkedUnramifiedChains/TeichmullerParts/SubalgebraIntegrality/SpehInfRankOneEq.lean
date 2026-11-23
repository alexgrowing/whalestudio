import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatCsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepDirectSumAwayFromPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumHodgeTate
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumTwoOfHodgeTate
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumFamilyOfReductions
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EtaCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistLocalComponentsCompatible
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompatiblePolarizationOfLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HalfOfCompatiblePolarization
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpehParameterStrings
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalReciprocity
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalFrobeniusCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeGaloisCompatibilityOfHeckeEigensystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.IrrComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitarStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af.Gu UpperTheory.V.Z.J.D GlobalTheory.DefiniteBC GlobalTheory.SmGL
open UpperTheory.V.Z.Mult (Cp At)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

private theorem irr_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (e : RepIso r r') (h : IsIrr r) :
    IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let T : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : Formalism.MainNotions.N.IsInv r (M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have h1 := hM g _ hv
    have h2 : T ((r g : Matrix (Fin n) (Fin n) k).mulVec v) = (r' g : Matrix (Fin n) (Fin n) k).mulVec (T v) := by
      rw [hT, hT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP g]
      simp [Matrix.mul_assoc]
    show T _ ∈ M
    rw [h2]
    exact h1
  rcases h.2.2 _ le_top hi with h0 | h0
  · left
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    have h1 : T.symm v ∈ M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k)) := by simpa using hv
    rw [h0] at h1
    simpa using (Submodule.mem_bot k).1 h1
  · right
    refine (Submodule.eq_top_iff').2 fun v => ?_
    have h1 : T.symm v ∈ M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k)) := by rw [h0]; trivial
    simpa using h1

private theorem iso_split {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (r r' : G E Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (hr' : Continuous r')
    (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) : RepIso r r' := by
  have hc : ∀ g : G E Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G E Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G E Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob (Filter.eventually_cofinite.1 hw) h1 h2 ?_) g
    intro v hv hd A hA σ hσ
    obtain ⟨B, hB, hB'⟩ := (not_not.1 hv) (UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E v (hE v) hd)
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

private theorem speh_inf_rank_one_eq (m : Multiset ℂ) : GlobalTheory.DefiniteBC.spehInf 1 m = m := by
  simp [GlobalTheory.DefiniteBC.spehInf]

private theorem ev_away {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem onePart (H : HypothesesH) (hLink : SatLink) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {n : ℕ} (hn : 1 ≤ n) (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (hsum : ∑ _i : Fin 1, 1 * n = n)
    (P : Fin 1 → CuspSub E n) (ρ : Fin 1 → ∀ w : HeightOneSpectrum (𝓞 E), LocIrr w n)
    (m : Fin 1 → (E →+* ℂ) → Multiset ℂ) (τs : Fin 1 → ∀ w : HeightOneSpectrum (𝓞 E), LocIrr w (1 * n))
    (hP : GlobalTheory.BcSpeh.Parts σ (fun _ => n) (fun _ => 1) hsum P ρ m)
    (hS : ∀ i w, GlobalTheory.SmGL.IsUnitarisable (ρ i w).ρ ∧ GlobalTheory.SmGL.IsUnitarisable (τs i w).ρ ∧
      GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) 1 (τs i w).ρ)
    (hsplit : ∀ w, IsSplitAt w → IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hsum w (τs · w))) :
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ At π σ ∧
      (∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam)) ∧ ∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B := by
  have hw : ∀ φ lam, HasWeightAt σ φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := hP.weight φ lam h
    rw [Fin.sum_univ_one, speh_inf_rank_one_eq] at e
    exact e ▸ hP.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, GlobalTheory.LocGlobDual.Model.dualIsConj_of_isCsd (H.toClassicalTheorems.litN.aut.gk E _ (P 0)) (hP.csd 0), ?_, hw, fun w hu => ?_⟩
  · obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E _ hn σ hσ τ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
    refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
    rw [infOfWeight, Multiset.mem_map] at hz
    obtain ⟨j, -, rfl⟩ := hz
    exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
  · filter_upwards [(hLink E _ (P 0)).2] with w ⟨B, hB⟩ hs
    have e : (fun i => τs i w) = fun _ => τs 0 w := funext fun i => by rw [Subsingleton.elim i 0]
    have key : ∀ f : Fin 1 → LocIrr w (1 * n), f = (fun _ => τs 0 w) →
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hsum w f) →
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hsum w fun _ => τs 0 w) := by
      rintro f rfl h
      exact h
    have hc := key _ e (hsplit w hs)
    exact ⟨ρ 0 w, B, UpperTheory.V.Z.Desc.irrComp E n σ hsum (P 0) w (ρ 0 w) (τs 0 w) (hP.loc 0 w) (hS 0 w).2.2 hc (ρ 0 w) (hP.loc 0 w),
      ((hLink E _ (P 0)).1 w _ (hP.loc 0 w) _).1 hB, hB⟩
  · obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1
      (GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n σ hσ 1 _ _ hsum P ρ m τs hP hS hsplit w hu 0 (ρ 0 w) (hP.loc 0 w))
    obtain ⟨B, hB⟩ := (satLoc H.toClassicalTheorems E n w (ρ 0 w)).1 ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩
    exact ⟨B, ((hLink E _ (P 0)).1 w _ (hP.loc 0 w) _).2 hB⟩

private theorem assemble (H : HypothesesH) (hB : GlobalTheory.BcSpeh.BcSpeh) (hFam : SumFam) (hHalf : Half) (hStr : Strings) (hUni : CompUnique)
    (hRec : RecTot) (hFrob : FrobTot) (hLink : SatLink) : BcOf := by
  intro _ E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ R hRc hRi hR
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ := hB E hE n hn π hπ
  have hc : 1 ≤ c := by
    rcases c with _ | c
    · simp at hsum; omega
    · omega
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ
    exact (hStr n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  choose r₀ HT₀ h₀ hw₀ using fun i (k : Fin (d i)) =>
    hHalf E Ω l ι (a i) (hP.pos i).1 (P i) (hP.csd i) (ρ i) (hP.loc i) (m i) (hP.inf i) (ex n (d i) k) (hint i k)
  choose r₁ h₁ hi₁ using fun i => hFam E Ω l ι (d i) (hP.pos i).2 (fun _ => a i) (fun _ => (hP.pos i).1) (d i * a i) (by simp)
    (r₀ i) _ (HT₀ i) (h₀ i)
  obtain ⟨r, hr, hi⟩ := hFam E Ω l ι c hc (fun i => d i * a i) (fun i => Nat.mul_pos (hP.pos i).2 (hP.pos i).1) n hsum r₁ _ _ h₁
  have hpar : ∀ w, ParAt ι r w (totPar n d (ρ · w)) := hr.par
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_away (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  have hRp : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ParAt ι R w (totPar n d (ρ · w)) := by
    filter_upwards [hR] with w hw hs
    let T : SmIrr (GL (Fin n) (w.adicCompletion E)) :=
      { V := _, ρ := locProd hsum w (σ · w), smooth := GlobalTheory.SmGL.isSmooth_parInd _ _, irred := (hsplit w hs).1 }
    exact ((locGlob_iff ι R w T).1 (hw hs T (hsplit w hs))).congr fun A h rc hrc =>
      (hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) T
        (hUni E n π hπ w hs _ _ _ _ (hsplit w hs) (hsplit w hs)) A h rc hrc).symm
  have hiso : RepIso R r := iso_split hE ι R r hRc hr.cont (ss_irr hRi) hr.ss (by
    filter_upwards [hev, hRp] with w ⟨hw, S, hS'⟩ hp hs
    have hSat : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i) := fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS' i)
    exact ⟨_, hFrob E Ω l ι n c a d R hRc w hw (ρ · w) S hSat (hp hs), hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S hSat (hpar w)⟩)
  have hirr : IsIrr r := irr_conj hiso hRi
  obtain ⟨hc1, hr1⟩ := hi hirr
  have hd1 : ∀ i, d i = 1 := fun i => (hi₁ i (hr1 i)).1
  clear hi hi₁ h₁ hr hpar hint hev hRp hiso hirr hr1 h₀ hw₀
  subst hc1
  obtain rfl : d = fun _ => 1 := funext hd1
  have ha : a = fun _ => n := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hsum
  subst ha
  exact onePart H hLink hE hn π hπ hsum P ρ m σ hP hS hsplit

theorem UpperTheory.V.Z.J.D.bcOf :
    BcOf := fun H =>
  assemble H (GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main H.litN.aut.bc H.litN.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual H.litN.aut.mw))
    (UpperTheory.sum_family_of_reductions (UpperTheory.sum_two_of_hodge_tate H UpperTheory.galoisRep_direct_sum_away_from_places UpperTheory.sum_hodge_tate) UpperTheory.finiteSum_reduction)
    (UpperTheory.half_of_compatible_polarization H UpperTheory.eta_condition UpperTheory.twist_local_components_compatible (UpperTheory.compatible_polarization_of_link H (compatCsd H) (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H)))
    UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness (UpperTheory.total_reciprocity H) (UpperTheory.total_frobenius_compatibility H) (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H) H
