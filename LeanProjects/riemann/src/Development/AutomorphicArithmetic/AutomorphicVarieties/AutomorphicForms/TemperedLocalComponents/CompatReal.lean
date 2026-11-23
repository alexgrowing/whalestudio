import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.RecMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBC0
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatCsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Untwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.PstRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.WdRelRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.RecTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeInvMulCharEqOfSimilitudePairing
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticComplexMultiplication
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ImaginaryGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CmInertiaRestrictionHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleRestrictionToNormalSubgroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharRealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.V.Af.Bc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem eventually_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {P : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ P w := by
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v :=
    HeightOneSpectrum.ext hl.over.symm
  exact ⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩

private theorem sat_of_isoTwist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} {π : TR.CuspSub F n}
    {η : HChar F} (h : IsoTwist π η) {v : HeightOneSpectrum (𝓞 F)} (hη : η.UnrAt v) {B : Multiset ℂˣ}
    (hB : π.HasSat v B) : B = B.map (· * η.val v) := by
  obtain ⟨T, hT, -⟩ := h
  refine hB.unique (GlobalTheory.SphGal.hasSatGL_of_twist hη T.symm (fun g x => ?_) hB)
  obtain ⟨x, rfl⟩ := T.surjective x
  apply T.injective
  rw [LinearEquiv.symm_apply_apply, TR.CuspSub.locRep_eq, hT, map_smul, LinearEquiv.apply_symm_apply,
    TR.CuspSub.chiDet_locGL]
  rfl

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem sf_isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem sf_quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

private theorem noTwistRam (hP : Hypotheses₂) : Cr.NoTwistRam := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι h2 n hn r π hc hatt ⟨s, hs, hs1⟩ η hη hT
  obtain ⟨δ, hδc, -, hδs, hδu⟩ := UpperTheory.exists_quadratic_sign_character F E Ω l h2
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, by
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    exact Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨g, hg⟩ : RepIso r (tw r δ) := by
    refine isoOfFrob hP F Ω l ι n r _ hc (irrBasic.2 _ _ n r δ hc hδc) hatt.1 ((irrBasic.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hδu, eventually_under (F := F) hη] with v hv hu hw
    obtain ⟨w, rfl, hw⟩ := hw
    obtain ⟨B, hB, hE⟩ := hv
    obtain ⟨h1, h3⟩ := hw (w.under (𝓞 F)) rfl
    refine ⟨_, hE, ?_⟩
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι n r δ _ _ _ hE (UpperTheory.frobenius_sign_compatibility F E Ω l ι δ hδs w hu)
    convert h4 using 1
    conv_lhs => rw [sat_of_isoTwist hT h1 hB]
    have h5 : ((η.val (w.under (𝓞 F)) : ℂˣ) : ℂ) = if normV w = normV (w.under (𝓞 F)) then 1 else -1 := by
      refine (congrArg Units.val h3).trans ?_
      change ((if normV w = normV (w.under (𝓞 F)) then 1 else -1 : ℂˣ) : ℂ) = _
      split_ifs <;> simp
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    rw [← h5]
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  have h6 := congrArg (fun x : GL (Fin n) (Qbar l) => (x : Matrix (Fin n) (Fin n) (Qbar l)) ⟨0, hn⟩ ⟨0, hn⟩) (hg s)
  simp only [tw_val, hs1, mul_one, mul_inv_cancel, (hδs.2 s).resolve_left (mt (hδs.1 s).1 hs)] at h6
  norm_num at h6

private theorem exists_sign {K : Type} [Field K] [NumberField K] [IsCMField K] (χ : HChar (maximalRealSubfield K))
    (h : ∀ v v' : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = χ.locInf v' (-1)) (b : ℤ) :
    ∃ k : ℕ, ∀ v, (χ * quadChar K ^ k).locInf v (-1) = (-1) ^ b := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have hval : ∀ (k : ℕ) v, (χ * quadChar K ^ k).locInf v (-1) = χ.locInf v₀ (-1) * (-1) ^ k := fun k v => by
    rw [HChar.locInf_mul, locInf_pow, quadChar_locInf, h v v₀]
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  simp only [hval, Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_neg,
    Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e <;> rcases Int.even_or_odd b with hb' | hb' <;> rw [e, hb'.neg_one_zpow]
  · exact ⟨0, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨0, fun _ => by simp⟩

private theorem csdTw (hg : GlobalTheory.Published.GaloisRepOfPolarizedPair) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) : Cr.CsdTw := by
  intro K _ _ _ n hn P χ hreg hs hd
  have hN : ∀ (ψ : HChar (maximalRealSubfield K)) (k : ℕ), compNorm K (ψ * quadChar K ^ k) = compNorm K ψ := fun ψ k => by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  obtain ⟨k, hk⟩ := exists_sign χ hs n
  obtain ⟨a, ha⟩ : ∃ a, IsAlgPos (χ * quadChar K ^ k) a := by
    obtain ⟨r, wt, HT, hr⟩ := hg K (AlgebraicClosure K) l ι n hn P (χ * quadChar K ^ k) hreg
      ⟨fun v => (hk v).trans (zpow_natCast _ _), by rwa [hN]⟩
    obtain ⟨μ, ⟨-, art, a, -, ha, -⟩, -⟩ := hr.pol
    exact ⟨a, ha⟩
  set χ₁ := χ * quadChar K ^ k with hχ₁
  have ha' : IsAlgPos χ₁⁻¹ (-a) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, ha k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield K →+* ℂ) := inferInstance
  obtain ⟨j, hj⟩ := exists_sign χ₁⁻¹ (fun v v' => congrArg (·⁻¹) ((hk v).trans (hk v').symm)) ((-a) φ₀)
  have ho : (quadChar K ^ j).OrderDvd 2 := by
    have := sf_quadChar_order K
    unfold HChar.OrderDvd at this ⊢
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have hpos := sf_isAlgPos_mul ha' (isAlgPos_zero_of_orderDvd two_pos ho)
  rw [add_zero, show -a = fun _ => (-a) φ₀ from funext fun φ => UpperTheory.heckeChar_parallel_weight _ _ _ ha' φ φ₀] at hpos
  obtain ⟨κ, m, hκ, hκχ⟩ := Cq.extReal K _ _ (UpperTheory.heckeChar_algebraic_of_sign _ _ _ hpos hj)
  exact ⟨κ, m, hκ, Cq.csdTwist K n P _ κ hd (by rw [hκχ, hN, map_inv, hχ₁, hN])⟩

private theorem bcDual : Cr.BcDual := by
  intro js gk F K _ _ _ _ _ _ _ h2 n hn π χ P hpol hBC
  obtain ⟨χ', hs, hv⟩ := UpperTheory.heckeChar_realTransport F K h2 χ
  refine ⟨χ', fun v v' => ?_, UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse js gk K n hn P _ ?_⟩
  · obtain ⟨u, e⟩ := hs v
    obtain ⟨u', e'⟩ := hs v'
    rw [e, e', hpol.sign u u']
  have hu : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, χ.UnrAt (w.under (𝓞 F)) := by
    rw [Filter.eventually_cofinite]
    refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F))
      fun v _ => ?_).subset fun w hw => hw
    haveI := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
    exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩
  filter_upwards [hu, hBC.unr, UpperTheory.baseChange_complexConj_invariance F K n π P hBC] with w hw h3 ⟨B₁, hB₁, hB₂⟩
  obtain ⟨B, hB, hB'⟩ := h3 (w.under (𝓞 F)) rfl _ (normV_under w)
  obtain rfl := hB'.unique hB₁
  obtain ⟨e1, e2⟩ := hv w
  obtain ⟨e3, e4⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ' w _ (e1.symm ▸ normV_under (K := F) w) (e2 hw).1
  refine ⟨e3, _, _, hB', hB₂, ?_⟩
  obtain ⟨β, d, hl, -, -, hβ, -⟩ := hpol.dual
  have e5 := UpperTheory.satake_inv_mul_char_eq_of_similitude_pairing F n _ _ _ (π.isSmooth_locRep _) χ hw β hl (fun g x y => by
    have := hβ (GlobalTheory.CuspRep.locGL F n _ g) x y
    rwa [TR.CuspSub.chiDet_locGL] at this) B hB
  rw [e4, (e2 hw).2]
  conv_rhs => rw [← e5]
  simp only [Multiset.map_map]
  exact Multiset.map_congr rfl fun b _ => by simp [mul_pow]

end UpperTheory.V.Af

theorem UpperTheory.V.Af.compatReal :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.CompatReal := by
  intro PH F Ω _ _ _ _ _ _ l _ hl ι n _ hn r π χ hr hreg hpol hatt v σ hσ A h rc hrc
  have P := PH.toClassicalTheorems
  obtain ⟨-, wt, HT, -, -, hG⟩ := exR PH F Ω l ι n hn π χ hreg hpol
  replace hG := hG r hr hatt
  refine ⟨fun hv => hG.away v hv A h rc hrc σ hσ, fun O _ _ _ Bw hj => ?_⟩
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.litN.loc.llc P.litN.loc.conv P.litN.loc.dzc P.litN.loc.dzi
      P.litN.loc.brauer P.litN.loc.chev P.litN.aut.art P.litN.loc.exh P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel
      P.litN.loc.geo P.litN.loc.bz
  have hpst : IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) := by
    obtain ⟨T⟩ := Loc.tiedP l
    exact P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hr.comp continuous_subtype_val))
      (hG.above _ _ ⟨T⟩ v A h O Bw hj).1
  refine ⟨hpst, ?_⟩
  obtain ⟨K, _, _, _, _, _, _, _, hK, hemb, v₀, A₀, ⟨B₀, -, hB₀⟩, hA₀, s, hs, hs'⟩ :=
    UpperTheory.exists_quadratic_of_inertia UpperTheory.quadratic_complex_multiplication UpperTheory.imaginary_generator UpperTheory.cm_inertia_restriction_holds F Ω l hl _ hatt.2
  obtain ⟨Q, hQ⟩ := (Br.quadBCw P F K hK n hn π hreg).resolve_left fun ⟨η, hη, ht⟩ =>
    noTwistRam P F K Ω l ι hK n hn r π hr hatt ⟨s, hs', (hB₀ A₀ hA₀).1 s hs⟩ η hη ht
  have hnorm : (res F Ω K).range.Normal := by
    obtain ⟨δ, -, -, hδ, -⟩ := UpperTheory.exists_quadratic_sign_character F K Ω l hK
    rw [show (res F Ω K).range = δ.ker from Subgroup.ext fun s => (hδ.1 s).symm]
    infer_instance
  obtain ⟨hQr, hQa⟩ := Br.bcAtt0 F K Ω l ι n r π Q hQ.toIsBC0
  replace hQr := hQr hreg
  replace hQa := hQa hatt (UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ n r _ hnorm hatt.1)
  obtain ⟨χ', hsg, hd⟩ := Br.bcDual0 P.litN.aut.js.1 P.litN.aut.gk F K hK n hn π χ Q hpol hQ.toIsBC0
  obtain ⟨κ, mκ, hκ, hcsd⟩ := csdTw P.litN.aut.gal ι K n hn Q χ' hQr hsg hd
  obtain ⟨artK, hartK, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt P.litN.aut.art).1 K Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ mκ (isAlgPos_of_isAlg hκ)
  have hR : Continuous (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
    hr.comp (continuous_restrictScalarsHom F K Ω)
  have hjK : ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := hemb Bw.j Bw.Kw Bw.j_E
  obtain ⟨Bw', e1, e2, e3⟩ := Cq.exBridge F K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w, h', i, hi⟩ := Cq.exPlaceIso F K Ω l A v h O Bw hj hjK
  obtain ⟨⟨σ', hσ'⟩, -⟩ := locCompC P K n Q w
  obtain ⟨rc', hrc', -⟩ := hL.1 K Ω A w h'
  obtain ⟨e, he⟩ := hQ.split hreg ⟨χ, hpol⟩ v w i hi.cont hi.loc σ σ' hσ hσ'
  obtain ⟨c1, c2⟩ := (compatCsd PH K Ω l ι n hn _ _ (Bc.irrBasic.2 _ _ n _ μ hR hμc) (regAlg_twist hQr hκ) hcsd
    (Cq.attTwist K Ω l ι n _ Q hQa artK κ mκ μ hartK hμ) w _ (hσ'.twist κ) A h' rc' hrc').2 O Bw' hj'
  have c3 := Lev.untwistS P.litN.aut.chA P.litN.aut.chW P.litN.aut.berger K Ω l ι n _ hR artK κ mκ μ hartK
    (isAlgPos_of_isAlg hκ) hμc hμ w A h' O Bw' hj' (Cq.pstRes F K Ω l A O Bw Bw' e1 e2 e3 n r hpst) c1 σ' rc' hrc' c2
  refine Lev.recMove hL F K Ω A v w h h' _ i hi n σ σ' e he rc rc' hrc hrc' _ _ ?_ c3
  exact Cq.wdRelRes F K Ω l A O Bw Bw' e1 e2 e3 n r hpst ι v w h h' hj hj' i hi

end
