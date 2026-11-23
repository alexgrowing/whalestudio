import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackComposite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHodgeCh2Omega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagExtensionOfSubbundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModifFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDualRiemann
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRiemannDataPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.Points GlobalTheory.HermFrame

namespace GlobalTheory.FlagValuationRings

theorem exists_dvd_all {A F : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field F] [Algebra A F]
    [IsFractionRing A F] {ι : Type} [Finite ι] (w : ι → F) (hw : ∃ i, w i ≠ 0) :
    ∃ i, w i ≠ 0 ∧ ∀ j, ∃ a : A, algebraMap A F a * w i = w j := by
  obtain ⟨i₀, h₀⟩ := hw
  have : Nonempty ι := ⟨i₀⟩
  let v := ValuationRing.valuation A F
  obtain ⟨i, hi⟩ := Finite.exists_max fun i => v (w i)
  have hne : w i ≠ 0 := fun h => h₀ (by
    have := hi i₀
    rw [h, map_zero, le_zero_iff] at this
    exact v.zero_iff.1 this)
  refine ⟨i, hne, fun j => ?_⟩
  have : w j / w i ∈ v.integer := by
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (hi j) zero_le
  obtain ⟨a, ha⟩ := (ValuationRing.mem_integer_iff A F _).1 this
  exact ⟨a, by rw [ha, div_mul_cancel₀ _ hne]⟩

theorem nonempty_flag {X : Scheme.{0}} [IsIntegral X] (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (r : ℕ) :
    ∀ E : X.Modules, IsVB E r → Nonempty (Vert.Flag E r) := by
  induction r with
  | zero => exact fun E hE => FlagModelExists.flag_rank_zero X E hE
  | succ r ih =>
    intro E hE
    have := hE.isQuasicoherent
    choose U e hx he using id hE
    let φ := ((he _).stalkBasis _ (hx (genericPoint X))).coord 0
    have hφ : φ ≠ 0 := fun h0 => by
      have := LinearMap.congr_fun h0 ((he _).stalkBasis _ (hx (genericPoint X)) 0)
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at this
      exact one_ne_zero this
    have hQ := CorankOne.isVB_cokernel_ofGeneric (F := E) φ fun y => by
      have := hX y
      obtain ⟨i, hi, hj⟩ := exists_dvd_all (A := X.presheaf.stalk y) (F := X.functionField)
        (fun j => φ (E.presheaf.germ _ _ (gen_mem (hx y)) (e y j))) (by
          by_contra! H
          exact hφ (((he y).stalkBasis _ (gen_mem (hx y))).ext fun j => by
            rw [IsFrame.stalkBasis_apply]; exact H j))
      exact ⟨U y, hx y, e y, i, he y, hi, fun j => (hj j).elim fun a ha => ⟨_, ⟨a, rfl⟩, ha⟩⟩
    have hS : (ShortComplex.mk _ (cokernel.π (Sub.ofGeneric (LinearMap.ker φ)).incl)
        (cokernel.condition _)).ShortExact := { exact := ShortComplex.exact_cokernel _ }
    obtain ⟨fl⟩ := ih _ (isVB_X₁_of_shortExact X _ r 1 hS hE hQ)
    exact Vert.Flag.nonempty_extend X E _ _ r ⟨inferInstance, 1, hQ⟩ hE fl

theorem valuationRing_atPrime (R : Type) [CommRing R] [IsDedekindDomain R] (P : Ideal R) [P.IsPrime] :
    ValuationRing (Localization.AtPrime P) := by
  by_cases h : P = ⊥
  · have hf : IsField (Localization.AtPrime P) := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
      subst h
      exact Ideal.map_bot
    let := hf.toField
    infer_instance
  · have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h (Localization.AtPrime P)
    infer_instance

theorem valuationRing_stalk (R : Type) [CommRing R] [IsDedekindDomain R] (x : Sp R) :
    ValuationRing ((Sp R).presheaf.stalk x) := by
  have key (y : PrimeSpectrum R) : Nonempty (Localization.AtPrime y.asIdeal ≃+* (Sp R).presheaf.stalk y) :=
    ⟨(Spec.stalkIso (.of R) y).commRingCatIsoToRingEquiv.symm⟩
  have := x.isPrime
  obtain ⟨e⟩ := key x
  have := valuationRing_atPrime R x.asIdeal
  exact Function.Surjective.valuationRing e.toRingHom e.surjective

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {E : X.Modules} {r : ℕ}

theorem isCInf_of_discrete (hd : ∀ σ, DiscreteTopology (CxPts p σ)) (h : VMetric p E r) : h.IsCInf :=
  fun σ c y _ a b => (vInfAt_const ((h.met σ).G c y a b) y).congr (by
    have := hd σ
    rw [nhds_discrete]
    exact eventually_pure.2 rfl)

theorem bcMeas_pull_eq_zero (hd : ∀ σ, DiscreteTopology (CxPts p σ)) {h : VMetric p E r} (H : h.IsCInf)
    (fl : Vert.Flag E r) (π : Y ⟶ X) (hπ : π ≫ p = q) (i : Fin r) (σ : k →+* ℂ) :
    (((h.pull π hπ).stepMet (fl.pull π) i).met σ).bcMeas (VMetric.stepSeq_shortExact (fl.pull π) i)
      ((fl.pull π).isVB i.castSucc) ((fl.pull π).isVB_gr i) = 0 := by
  refine Met.bcMeas_eq_zero _ _ _ fun c z hz => ?_
  obtain ⟨a, ha⟩ := Met.exists_adapted (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc)
    (fl.isVB_gr i) (PtsOver.map π hπ _ z)
  have ha' : z ∈ ptsIn q σ (π ⁻¹ᵁ a.U) := ha
  have H₂ : ((h.pull π hπ).stepMet (fl.pull π) i).IsCInf := (H.pull π hπ).restrict _ _
  have := hd σ
  have hm : Continuous (PtsOver.map π hπ (spMap σ)) := PtsOver.continuous_map π hπ _
  have hS : IsOpen (PtsOver.map π hπ (spMap σ) ⁻¹' {PtsOver.map π hπ (spMap σ) z}) :=
    (isOpen_discrete _).preimage hm
  have hn := (ChartGlue.isOpen_over c.e hS).mem_nhds (ChartGlue.mem_over c.e hz (S := _) rfl)
  rw [Met.bcDens_eq _ _ _ (VMetric.pullStep fl π i a) c (H₂ σ) hz ha', Met.bcForm,
    extTrace_congr (K' := fun _ => ((h.stepMet fl i).met σ).gram a.frame (PtsOver.map π hπ _ z))]
  · simp [diagVal, extTrace, extForm]
  · filter_upwards [hn] with v hv
    have e : PtsOver.map π hπ (spMap σ) (c.e.symm v) = PtsOver.map π hπ (spMap σ) z := hv.2
    have hv' : PtsOver.map π hπ (spMap σ) (c.e.symm v) ∈ ptsIn p σ a.U := e ▸ ha
    exact (VMetric.gram_pullStep h hπ a hv').trans (congrArg _ e)

theorem isFlagCh2_pull_zero (HC : Published.ArCalc) [IsIntegral Y] (hX : IsArithVar p 0) (hY : IsArithVar q 1)
    (hd : ∀ σ, DiscreteTopology (CxPts p σ)) {h : VMetric p E r} (H : h.IsCInf)
    (fl : Vert.Flag E r) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    VMetric.IsFlagCh2 (H.pull π hπ) (fl.pull π) 0 := by
  have e := bcMeas_pull_eq_zero hd H fl π hπ
  refine ⟨fun i σ => ?_, fun _ => 0, fun i => ?_, ?_⟩
  · rw [e]; simp
  · refine (VMetric.isometric_grLB_pull k X Y p q E r h H fl π hπ i).symm.isSelfInter hY
      (ProjDrop.isSelfInter_zero_of_dim_lt HC k X Y p q 0 1 hX hY π hπ ?_ _)
    refine ((topologicalKrullDim_subspace_le _ _).trans hX.dim_eq.le).trans_lt ?_
    exact_mod_cast (by norm_num : 0 + 1 < 1 + 1)
  · simp only [VMetric.flagBc, VMetric.bcInt, e]; simp

theorem exists_order {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Module.Finite ℤ A] [Module.Finite ℤ B]
    [IsDomain C] [CharZero C] (a : A →+* C) (b : B →+* C) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : CharZero R) (_ : Module.Finite ℤ R)
      (a' : A →+* R) (b' : B →+* R) (c : R →+* C), c.comp a' = a ∧ c.comp b' = b := by
  let f := Algebra.TensorProduct.productMap a.toIntAlgHom b.toIntAlgHom
  refine ⟨f.range, inferInstance, inferInstance, inferInstance,
    Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective,
    (f.rangeRestrict.comp Algebra.TensorProduct.includeLeft).toRingHom,
    (f.rangeRestrict.comp Algebra.TensorProduct.includeRight).toRingHom, f.range.val.toRingHom, ?_, ?_⟩
  · ext x; simp [f]
  · ext x; simp [f]

section Order

variable {R : Type} [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R] (a : k →+* R)

theorem isArithVar_order [IsDomain k] [Module.Finite ℤ k] : IsArithVar (spMap a) 0 := by
  have hA : IsAmpleLB (LB.triv (Sp R)) := ⟨LB.isLB_triv _, inferInstance, fun x => by
    obtain ⟨s, hs⟩ := ((isGenerated_triv (Sp R)).pow 1).exists_mem x
    exact ⟨1, le_rfl, s, hs, inf_top_eq (Out.nonzeroLocus s) ▸ isAffineOpen_nonzeroLocus_inf
      (isLB_lbPow (LB.isLB_triv _) 1) s (isAffineOpen_top _)⟩⟩
  have hf : a.Finite := by
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℤ k) ?_
    rw [RingHom.ext_int (a.comp (algebraMap ℤ k)) (algebraMap ℤ R)]
    exact RingHom.finite_algebraMap.2 ‹_›
  have : IsFinite (spMap a) := (IsFinite.SpecMap_iff _).2 hf
  have hd : ringKrullDim R = 1 := by
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := ℤ) (B := R) (algebraMap ℤ R).injective_int]
    exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField
  exact ⟨‹_›, ‹_›, inferInstance, hA.isProjOver _, (flat_int_iff_charZero _).2
    (((Scheme.ΓSpecIso (.of R)).inv.hom.charZero_iff
      (ConcreteCategory.bijective_of_isIso _).1).1 ‹_›),
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R).trans hd⟩

theorem discrete_order [IsDomain k] [Module.Finite ℤ k] (σ : k →+* ℂ) : DiscreteTopology (CxPts (spMap a) σ) := by
  have := t2Space_cxPts_of_isProjOver (σ := σ) (isArithVar_order a).isProjOver
  have : Finite (R →+* ℂ) := .of_equiv _ (RingHom.equivIntAlgHom R ℂ).symm
  have : Finite (CxPts (spMap a) σ) := .of_injective (β := R →+* ℂ) (fun y => (Spec.preimage y.1).hom)
    fun y y' e => Subtype.ext (by
      rw [← Spec.map_preimage y.1, ← Spec.map_preimage y'.1]
      exact congrArg Spec.map (CommRingCat.hom_ext e))
  infer_instance

end Order

theorem toSpecΓ_comp {A : Type} [CommRing A] (g : Y ⟶ Sp A) :
    Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop) = g := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem exists_isPull_cancel {S T T' : Scheme.{0}} {P : PPAS S} {P' : PPAS T} {Q : PPAS T'} {f : T ⟶ S}
    {φ : P'.A.left ⟶ P.A.left} {g : T' ⟶ T} {ψ : Q.A.left ⟶ P.A.left} (hP : P'.IsPull P f φ)
    (hQ : Q.IsPull P (g ≫ f) ψ) : ∃ ψ' : Q.A.left ⟶ P'.A.left, Q.IsPull P' g ψ' := by
  obtain ⟨hP, hPc⟩ := hP
  obtain ⟨hQ, hQc⟩ := hQ
  have w : ψ ≫ P.A.hom = (Q.A.hom ≫ g) ≫ f := by
    rw [hQ.1.w, Category.assoc]
  let ψ' : Q.A.left ⟶ P'.A.left := hP.1.lift ψ (Q.A.hom ≫ g) w
  have h₁ : ψ' ≫ φ = ψ := hP.1.lift_fst _ _ _
  have h₂ : ψ' ≫ P'.A.hom = Q.A.hom ≫ g := hP.1.lift_snd _ _ _
  have n : IsGrpPullback Q.A P.A (g ≫ f) (ψ' ≫ φ) := hQ.congr rfl h₁.symm
  have hc : IsGrpPullback Q.A P'.A g ψ' := IsGrpPullback.cancel hP n h₂
  refine ⟨ψ', hc, ?_⟩
  rw [hQc, hPc, ← CechPic.pull_comp, HodgePull.sqMap_comp hP.1.w hc.1.w n.1.w]
  have key {χ χ' : Q.A.left ⟶ P.A.left} (e : χ = χ') (u u') :
      sqMap (f := g ≫ f) (φ := χ) u = sqMap (f := g ≫ f) (φ := χ') u' := by subst e; rfl
  rw [key h₁ n.1.w hQ.1.w]

theorem ch2Deg_eq_zero : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (K : Type) [Field K] [NumberField K] (E : PPAS (Sp (𝓞 K))), E.HasTheta → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) [IsIntegral Y], IsRegSurf p → ∀ (q : Y ⟶ Sp (𝓞 K)) (Q : PPAS Y) (φ : Q.A.left ⟶ E.A.left), Q.IsPull E q φ → ∀ h : VMetric p (LieVB.omega Q.A) Q.g, Q.IsHodge h → h.IsCInfNorm → ∀ a : ℝ, h.IsCh2Deg a → a = 0 := by
  intro HP _ K _ _ E _ k _ Y p _ hY q Q φ hQ h H _ a ha
  have := hY.isDomain
  have := hY.finite
  have := hY.toIsArithVar.charZero
  obtain ⟨R, _, _, _, _, a', b', c, h₁, h₂⟩ := exists_order
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom ((Scheme.ΓSpecIso (.of (𝓞 K))).inv ≫ q.appTop).hom
  let π : Y ⟶ Sp R := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c)
  have w₁ : π ≫ spMap a' = p := by
    rw [← toSpecΓ_comp p, Category.assoc, spMap, ← Spec.map_comp]
    exact congrArg (fun t => Y.toSpecΓ ≫ Spec.map t) (CommRingCat.hom_ext h₁)
  have w₂ : π ≫ spMap b' = q := by
    rw [← toSpecΓ_comp q, Category.assoc, spMap, ← Spec.map_comp]
    exact congrArg (fun t => Y.toSpecΓ ≫ Spec.map t) (CommRingCat.hom_ext h₂)
  obtain ⟨P, ψ, hg, hP⟩ := PPAS.exists_pull _ _ E (spMap b')
  obtain ⟨χ, hχ⟩ := exists_isPull_cancel hP (w₂.symm ▸ hQ)
  have hg' : Q.g = P.g :=
    Q.isVB_omega.rank_unique ((P.isVB_omega.pullback π).of_iso (ShFam.Pad.omegaPullIso hχ))
  obtain ⟨fl₀⟩ := nonempty_flag (valuationRing_stalk (𝓞 K)) _ _ E.isVB_omega
  have fl : Vert.Flag (LieVB.omega P.A) P.g :=
    hg.symm ▸ (fl₀.pull (spMap b')).ofIso (ShFam.Pad.omegaPullIso hP)
  obtain ⟨h₀, H₀⟩ := PPAS.exists_isDualRiemann k _ (spMap a') P _ Real.pi_pos
  have hd := discrete_order a'
  have hC := isCInf_of_discrete hd h₀
  have z := isFlagCh2_pull_zero HP.p4 (isArithVar_order a') hY.toIsArithVar hd hC fl π w₁
  have I := HodgePull.form_omegaBase k _ _ Y p π w₁ P Q χ hχ.1 hg' hχ _ h₀ h H₀ H
  clear H
  revert h
  rw [hg']
  intro h _ ha I
  have I' : (h₀.pull π w₁).IsIsometry h (ShFam.Pad.omegaPullIso hχ) := I
  have hC' : h.IsCInf := by
    rw [(VMetric.isIsometry_iff _).1 I']
    exact (hC.pull π w₁).map _
  exact ChTwoModel.eq_of_isFlagCh2 hY ha
    ((VMetric.isFlagCh2_ofIso k Y p _ _ _ _ _ _ (hC.pull π w₁) hC' _ 0 I').1 z)

end GlobalTheory.FlagValuationRings
