import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ThruBad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitTr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitCM
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.ThruTr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SatNumInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.PlainOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.WinPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycFree
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurTwistHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base
  UpperTheory.V.Z.Gam UpperTheory.V.Z.Win GroundTheory.Global.SemiLocal

namespace UpperTheory.V.Z.Win.Birth.RealAlgebraicWindow

private theorem coeffCont {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

private theorem isoFrob : IsoOfFrob := by
  intro F Ω _ _ _ _ _ l _ ι n r r' hr hr' hs hs' hw
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (coeffCont n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (coeffCont n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

private theorem noTw : NoTwist :=
  UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible isoFrob UpperTheory.frobenius_eigenvalues_twist UpperTheory.exists_quadratic_sign_character UpperTheory.frobenius_sign_compatibility UpperTheory.schur_twist_holds UpperTheory.galoisRep_irreducibility_criterion

private theorem normUnder {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem satEq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem satPow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  simp only [satEq, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]

private theorem underTendsto {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

private theorem selfTw : Sd.SelfTwGal := by
  intro F Ω _ _ _ _ _ l _ ι n r sat hu hc hatt η m hm hη hη1 hT
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) hm hη)
  have hpow : δ ^ m = 1 := hL.pow_eq_one ha.quot.surjective hη
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv A hA =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hA).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hA hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  refine ⟨δ, ?_, isOpen_ker_of_pow δ hδc hm fun g => DFunLike.congr_fun hpow g, ?_, ?_⟩
  · rintro rfl
    refine hη1 (Subtype.ext (MonoidHom.ext fun x => Units.ext ?_))
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    have e := hL x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
      map_eq_one_iff _ ι.symm.injective] at e
    exact e
  · refine isoFrob F Ω l ι n r _ hc (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ n r δ hc hδc) hatt.1
      ((UpperTheory.galoisRep_irreducibility_criterion.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hT] with v hv hw
    obtain ⟨B, hB, hF⟩ := hv
    obtain ⟨h1, B', hB', h2⟩ := hw
    obtain rfl := hu v _ _ hB hB'
    refine ⟨_, hF, ?_⟩
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι n r δ _ _ _ hF (hE v h1)
    convert h4 using 1
    conv_lhs => rw [← h2]
    simp only [satEq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  · intro E _ _ _ _ _ hN
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := F) E
    haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
    have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, CharEig ι (δ.comp (res F Ω E)) w 1 := by
      filter_upwards [hN.2.2, (underTendsto (K := F) (K' := E)).eventually hT] with w h1 h2
      have hf := normUnder (K := F) w
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 δ _ (hE _ h2.1)
      rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
    have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res F Ω E s)) (f' := fun _ => 1)
      (hδc.comp (continuous_restrictScalarsHom F E Ω)) continuous_const fun v hv _ A hA σ hσ => by
        have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
        rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
        exact h
    exact MonoidHom.ext fun s => congrFun key s

private theorem upCycle : Sd.UpCyc := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hp n hn r hr ⟨π, hreg, hatt⟩ hirr
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have key : (∃ η : HChar F, IsNormChar E η ∧ SelfTw (CG.mk π).HasSat η) ∨
      ∃ P : CuspSub E n, (∀ τ m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m) ∧ WeakBC (CG.mk π).HasSat (CG.mk P).HasSat := by
    rcases (Z.Bc.cycC_holds F E hp inferInstance n hn).1 _ _ (Or.inl ⟨inferInstance, π, rfl, rfl⟩)
      (fun τ => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, hreg τ⟩) with h1 | ⟨sat', inf', hc, hw, hi⟩
    · exact Or.inl h1
    · rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hR, -⟩
      · exact Or.inr ⟨P, hi, hw⟩
      · obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
        exact absurd (hR.isReal v) (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v))
  rcases key with ⟨η, hη, hT⟩ | ⟨P, hinf, hbc⟩
  · obtain ⟨δ, hδ1, -, hiso, hres⟩ := selfTw F Ω l ι n r (CG.mk π).HasSat
      (fun _ _ _ h h' => h.unique h') hr hatt η _ hp.pos hη.2.1 hη.1 hT
    exact (hδ1 (UpperTheory.schur_twist_holds _ _ _ n r _ δ hirr (hres E hη) hiso)).elim
  · refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, (UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ n _).2.1 hirr, ?_⟩
    · have h := hreg (τ.comp (algebraMap F E))
      have hm : π.HasInfChar (τ.comp (algebraMap F E)) ((CG.mk π).infChar (τ.comp (algebraMap F E))) :=
        ParLaws.hasInfChar_infChar (CG.mk π) _
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ _ hm)]
      exact h
    · filter_upwards [hbc, (underTendsto (K := F) (K' := E)).eventually hatt.2] with w h1 h2
      obtain ⟨B, hB, hPw⟩ := h1 _ (normUnder (K := F) w)
      obtain ⟨B', hB', hF⟩ := h2
      obtain rfl := hB.unique hB'
      refine ⟨_, hPw, ?_⟩
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ (normUnder (K := F) w)).1 n r _ hF
      rw [← satPow, ← normUnder] at h3
      exact h3

private theorem quadGalois (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h : Module.finrank K L = 2) : IsGalois K L := by
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h }
  infer_instance

private theorem plainUp : RealUp := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ hE l _ ι r π hr hreg hatt hirr P hPreg hPatt w hw
  obtain ⟨E', M, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, hM, hsp⟩ :=
    splitCM F E Ω hE l 2 r hirr (w.under (𝓞 F))
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  haveI : IsAlgClosure E' Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) E'⟩
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  have e1 : (r.comp (resG F E' Ω)).comp (resG E' M Ω) = r.comp (resG F M Ω) := MonoidHom.ext fun _ => rfl
  have e2 : (r.comp (resG F E Ω)).comp (UpperTheory.V.Base.galEmb E M Ω) = r.comp (resG F M Ω) := MonoidHom.ext fun _ => rfl
  have e3 : (r.comp (resG F E Ω)).comp (resG E M Ω) = r.comp (resG F M Ω) := MonoidHom.ext fun _ => rfl
  have hirrE' : IsIrr (r.comp (resG F E' Ω)) :=
    (UpperTheory.galoisRep_irreducibility_criterion.1 (G E' Ω) (G M Ω) (Qbar l) 2 (r.comp (resG F E' Ω))).1 (resG E' M Ω) (e1 ▸ hM)
  obtain ⟨P', hBC⟩ := (UpperTheory.ConvolutionTheory.R2.quadBC2 F E' h1 π hreg).resolve_left
    fun ⟨η, hη, ht⟩ => noTw F E' Ω l ι h1 2 r π hr hatt hirrE' η hη ht
  have hP'att : AttC ι (r.comp (resG F E' Ω)) P' :=
    (Bc.bcAtt F E' Ω l ι 2 r π P' hBC).2 hatt ((Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirrE')
  haveI gE : IsGalois E M := quadGalois E M h2
  haveI gE' : IsGalois E' M := quadGalois E' M h3
  obtain ⟨Q, -, hQatt⟩ := upCycle E M Ω l ι (h2 ▸ Nat.prime_two) 2 one_le_two (r.comp (resG F E Ω))
    (hr.comp (continuous_restrictScalarsHom F E Ω)) ⟨P, hPreg, hPatt⟩ (e2.symm ▸ hM)
  rw [e2] at hQatt
  have hB1 : WeakBC (CG.mk P).HasSat (CG.mk Q).HasSat :=
    attBC E M Ω l ι 2 (r.comp (resG F E Ω)) P Q hPatt (e3.symm ▸ hQatt)
  have hB2 : WeakBC (CG.mk P').HasSat (CG.mk Q).HasSat :=
    attBC E' M Ω l ι 2 (r.comp (resG F E' Ω)) P' Q hP'att (e1.symm ▸ hQatt)
  have hpl : ∀ w' : HeightOneSpectrum (𝓞 E'), w'.under (𝓞 F) = w.under (𝓞 F) → PlainAt P' w' := by
    intro w' hw'
    obtain ⟨i, hi⟩ := hsp w' hw'
    rcases hw with h | h
    · exact ((splitTr F E' 2 one_le_two π P' hBC _ w' i hi).1).1 h
    · exact (plainOf E' 2 one_le_two P' w').2 ((splitTr F E' 2 one_le_two π P' hBC _ w' i hi).2 h)
  obtain ⟨t, ht⟩ := winPt suppFacts ImaginaryQuadraticEtaCharacter.winOf E' 2 one_le_two P'
  have hund : ∀ x : HeightOneSpectrum (𝓞 M), w.asIdeal = x.asIdeal.under (𝓞 E) →
      (x.under (𝓞 E')).under (𝓞 F) = w.under (𝓞 F) := by
    intro x hx
    refine HeightOneSpectrum.ext ?_
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, hx,
      Ideal.under_under, Ideal.under_under]
  have hup : ∀ u : PlacesOver M w, ImaginaryQuadraticEtaCharacter.WinAt Q t u.1 ∧ ThruAt Q u := by
    intro u
    have hl : u.1.asIdeal.LiesOver (u.1.under (𝓞 E')).asIdeal := ⟨rfl⟩
    have hw' : (u.1.under (𝓞 E')).under (𝓞 F) = w.under (𝓞 F) := hund u.1 u.2.over
    have h := (ImaginaryQuadraticEtaCharacter.winUpDown E' M (h3 ▸ Nat.prime_two) 2 le_rfl P' Q hB2 t (u.1.under (𝓞 E'))).1
      (ht _ (hpl _ hw')) ⟨u.1, hl⟩
    have hi : ∃ i : ((u.1.under (𝓞 E')).under (𝓞 F)).adicCompletion F ≃+* (u.1.under (𝓞 E')).adicCompletion E', IsCompl i := by
      rw [hw']
      exact hsp _ hw'
    obtain ⟨i, hi⟩ := hi
    exact ⟨h.1, thruTr F E E' M 2 Q w (u.1.under (𝓞 E')) u ⟨u.1, hl⟩ rfl i hi h.2⟩
  exact (plainOf E 2 one_le_two P w).1 t ((ImaginaryQuadraticEtaCharacter.winUpDown E M (h2 ▸ Nat.prime_two) 2 le_rfl P Q hB1 t w).2 hup)

end UpperTheory.V.Z.Win.Birth.RealAlgebraicWindow

theorem UpperTheory.V.Z.Win.Birth.awReal :
    UpperTheory.V.Z.Win.Birth.AwReal := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ hE l _ ι r hr hirr ⟨π, hreg, hatt, hpl⟩ P hPreg hPatt
  obtain ⟨t, ht⟩ := winPt suppFacts ImaginaryQuadraticEtaCharacter.winOf E 2 one_le_two P
  exact ⟨t, fun v => ht v (UpperTheory.V.Z.Win.Birth.RealAlgebraicWindow.plainUp F E Ω hE l ι r π hr hreg hatt hirr P hPreg hPatt v (hpl _))⟩
