import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.WeightedPresExistsAlgHomExtensionOfAdicComplete
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

section SlopeTestRemainingChoices

open Polynomial in
private theorem md_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem md_ext {O X R K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X]
    [CommRing R] [Algebra O R] (W : WPres O X R) [NormedField K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (hw : ∀ x : K, ‖x‖ ≤ 1 → IsIntegral O x)
    (ξ : W.A →ₐ[O] DualNumber K) (h1 : ∀ x, ‖(ξ x).fst‖ ≤ 1) (hz : ∀ s, ‖(ξ (W.zA s)).fst‖ < 1)
    (hfg : ((W.gr 0).map ξ.toLinearMap).FG) :
    ∃ Ξ : R →ₐ[O] DualNumber K, (∀ x : W.A, Ξ x = ξ x) ∧ ∀ x, IsIntegral O (Ξ x) := by
  have hw' : ∀ x : DualNumber K, ‖x.fst‖ ≤ 1 → IsIntegral O x := fun x hx => by
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    refine IsIntegral.add ((hw _ hx).map (TrivSqZeroExt.inlAlgHom O K K)) ?_
    exact ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simp [pow_two]⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ hinj).2 hp.ne_zero
  let y : W.σ → DualNumber K := fun s => ξ (W.zA s)
  have hc : ∀ s, ∃ n : ℕ, IsIntegral O ((algebraMap O K p)⁻¹ • y s ^ n) := fun s => by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hp0) (hz s)
    refine ⟨n, hw' _ ?_⟩
    rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_pow, smul_eq_mul, norm_mul, norm_inv, norm_pow, ← div_eq_inv_mul]
    exact div_le_one_of_le₀ hn.le (norm_nonneg _)
  choose e he using hc
  obtain ⟨T, hT⟩ := id hfg
  let G : Set (DualNumber K) := (T : Set _) ∪ Set.range y ∪ Set.range fun s => (algebraMap O K p)⁻¹ • y s ^ e s
  have hG : G.Finite := (T.finite_toSet.union (Set.finite_range _)).union (Set.finite_range _)
  have hGi : ∀ x ∈ G, IsIntegral O x := by
    rintro x ((hx | ⟨s, rfl⟩) | ⟨s, rfl⟩)
    · have : x ∈ (W.gr 0).map ξ.toLinearMap := hT ▸ Submodule.subset_span hx
      obtain ⟨a, -, rfl⟩ := this
      exact hw' _ (h1 a)
    · exact hw' _ (hz s).le
    · exact he s
  let B : Subalgebra O (DualNumber K) := Algebra.adjoin O G
  haveI : Module.Finite O B := Algebra.finite_adjoin_of_finite_of_isIntegral hG hGi
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite O B
  haveI := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) B
  let J : Ideal B := ((maximalIdeal O).map (algebraMap O B)).radical
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg ((maximalIdeal O).map (algebraMap O B))
    (IsNoetherian.noetherian _)
  haveI : IsAdicComplete J B :=
    { toIsHausdorff := GlobalTheory.NilpotentEval.isHausdorff_of_pow_le hN
      toIsPrecomplete := GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le hN Ideal.le_radical }
  have hB : ∀ x, ξ x ∈ B := fun x => by
    have h2 : (⊤ : Subalgebra O W.A) ≤ B.comap ξ := by
      rw [← gr_gen O R X W]
      refine Algebra.adjoin_le ?_
      rintro a (ha | ⟨s, rfl⟩)
      · have h1 : ξ a ∈ Submodule.span O (T : Set (DualNumber K)) := hT ▸ Submodule.mem_map_of_mem ha
        have h2 : Submodule.span O (T : Set (DualNumber K)) ≤ B.toSubmodule :=
          Submodule.span_le.2 fun a ha => Algebra.subset_adjoin (Or.inl (Or.inl ha))
        exact h2 h1
      · exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨s, rfl⟩))
    exact h2 trivial
  have hyB : ∀ s, ξ.codRestrict B hB (W.zA s) ∈ J := fun s => by
    refine ⟨e s, ?_⟩
    have : ξ.codRestrict B hB (W.zA s) ^ e s = algebraMap O B p *
        ⟨(algebraMap O K p)⁻¹ • y s ^ e s, Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)⟩ := by
      apply Subtype.ext
      show y s ^ e s = algebraMap O (DualNumber K) p * ((algebraMap O K p)⁻¹ • y s ^ e s)
      rw [← Algebra.smul_def, ← algebraMap_smul K p, smul_inv_smul₀ hp0]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp.not_isUnit)
  obtain ⟨f, hf⟩ := UpperTheory.weightedPres_exists_algHom_extension_of_adicComplete W J (ξ.codRestrict B hB) hyB
  refine ⟨B.val.comp f, fun x => congrArg Subtype.val (DFunLike.congr_fun hf x), fun x => ?_⟩
  exact (Algebra.IsIntegral.isIntegral (R := O) (f x)).map B.val

private theorem md_uniq {O σ K : Type} [CommRing O] [Fintype σ] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    (φ ψ : MvPowerSeries σ O →ₐ[O] K) (h1 : ∀ F, ‖φ F‖ ≤ 1) (h2 : ∀ F, ‖ψ F‖ ≤ 1)
    (hz : ∀ s, ‖φ (MvPowerSeries.X s)‖ < 1) (h : ∀ s, φ (MvPowerSeries.X s) = ψ (MvPowerSeries.X s)) : φ = ψ := by
  let V : Subalgebra O K :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha (norm_nonneg _) hb
      add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      algebraMap_mem' := fun a => by
        have := h1 (algebraMap O _ a)
        rwa [AlgHom.commutes] at this }
  let ρ : NNReal := Finset.univ.sup fun s => ‖φ (MvPowerSeries.X s)‖₊
  have hρ : ρ < 1 := (Finset.sup_lt_iff (by norm_num)).2 fun s _ => hz s
  let J : Ideal V :=
    { carrier := {x | ‖(x : K)‖ ≤ ρ}
      add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        show ‖(a : K) * b‖ ≤ ρ
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) a.2).trans hb }
  have key : ∀ n : ℕ, ∀ z ∈ J ^ n, ‖(z : K)‖ ≤ (ρ : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro z _; rw [pow_zero]; exact z.2
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [Subalgebra.coe_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) hb (norm_nonneg _) (pow_nonneg ρ.2 _)
      · rw [Subalgebra.coe_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  have hJ : ∀ s, φ.codRestrict V h1 (MvPowerSeries.X s) ∈ J := fun s =>
    Finset.le_sup (f := fun s => ‖φ (MvPowerSeries.X s)‖₊) (Finset.mem_univ s)
  have he : ∀ s, φ.codRestrict V h1 (MvPowerSeries.X s) = ψ.codRestrict V h2 (MvPowerSeries.X s) :=
    fun s => Subtype.ext (h s)
  refine AlgHom.ext fun F => ?_
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one ρ.2 hρ) fun n => ?_
  exact key n _ (GlobalTheory.algHom_sub_mem_pow (φ.codRestrict V h1) (ψ.codRestrict V h2) hJ (fun s => he s ▸ hJ s)
    (fun s => by rw [he s, sub_self]; exact zero_mem _) F)

private theorem md_main {O R S K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] (hinj : Function.Injective (algebraMap O K))
    (hw : ∀ x : K, IsIntegral O x ↔ ‖x‖ ≤ 1)
    (W : WPres O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[O] S) (hq : Function.Surjective qh) {κ : Type} (g : κ → W.A)
    (hker : RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R))) (hM : M2 W.gr (Ideal.span (Set.range g)))
    (f : S →ₐ[O] K) (hf : IsLocPt f) (D : W.A →ₗ[O] K) (hD : D ∈ PtDer (f.comp (qh.comp W.A.val)) K)
    (hDI : ∀ y ∈ Ideal.span (Set.range g), D y = 0) :
    ∃ F : S →ₐ[O] DualNumber K, dualFst F = f ∧ ∀ y : W.A, (F (qh y)).snd = D y := by
  have hO : ∀ a : O, ‖algebraMap O K a‖ ≤ 1 := fun a => (hw _).1 isIntegral_algebraMap
  have hf1 : ∀ x, ‖f x‖ ≤ 1 := fun x => by
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    have := hf _ ha
    rw [map_sub, AlgHom.commutes] at this
    rw [← sub_add_cancel (f x) (algebraMap O _ a)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le this.le (hO a))
  have hz : ∀ s, ‖f (qh (W.z s))‖ < 1 := fun s => hf _ (by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact mem_max_of_zero (W.origin h) (origin_presentation_var_eq_zero W h s))
  letI : Module Oᵐᵒᵖ K := Module.compHom K ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O K := ⟨fun _ _ => rfl⟩
  obtain ⟨τ, hτ⟩ := (der_hom O W.A K K (f.comp (qh.comp W.A.val)) D).1 ⟨D, hD, rfl⟩
  have hg0 : ∀ i, τ (g i) = 0 := fun i => by
    have h1 : qh (g i) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.subset_span ⟨i, rfl⟩
    ext
    · rw [(hτ _).1]
      show f (qh (g i)) = 0
      rw [h1, map_zero]
    · rw [(hτ _).2]
      exact hDI _ (Ideal.subset_span ⟨i, rfl⟩)
  have hτI : ∀ y ∈ Ideal.span (Set.range g), τ y = 0 := by
    have : Ideal.span (Set.range g) ≤ RingHom.ker τ := Ideal.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact hg0 i)
    exact this
  have hfg : ((W.gr 0).map τ.toLinearMap).FG := by
    have := Submodule.FG.map (Ideal.Quotient.liftₐ _ τ hτI).toLinearMap hM
    rw [← Submodule.map_comp] at this
    exact this
  obtain ⟨Ξ, hΞ, hint⟩ := md_ext W (K := K) hinj (fun x => (hw x).2) τ (fun x => by rw [(hτ x).1]; exact hf1 _)
    (fun s => by rw [(hτ _).1]; exact hz s) hfg
  have hfst : (dualFst Ξ).comp W.π = (f.comp qh).comp W.π := by
    have e : ∀ s, (Ξ (W.z s)).fst = f (qh (W.z s)) := fun s => by
      have := hΞ (W.zA s)
      rw [show W.z s = (W.zA s : R) from rfl, this, (hτ _).1]
      rfl
    refine md_uniq _ _ (fun F => ?_) (fun F => hf1 _) (fun s => ?_) e
    · exact (hw _).1 ((hint (W.π F)).map (TrivSqZeroExt.fstHom O K K))
    · exact (congrArg norm (e s)).trans_lt (hz s)
  have hK : ∀ x ∈ RingHom.ker qh, Ξ x = 0 := by
    have : RingHom.ker qh ≤ RingHom.ker Ξ := by
      rw [hker]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact (hΞ _).trans (hg0 i)
    exact this
  let F : S →ₐ[O] DualNumber K := (Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hK).comp
    (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom
  have hF : ∀ x, F (qh x) = Ξ x := by
    intro x
    have : (Ideal.quotientKerAlgEquivOfSurjective hq).symm (qh x) = Ideal.Quotient.mk _ x := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [F, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl
  refine ⟨F, AlgHom.ext fun x => ?_, fun y => by rw [hF, hΞ, (hτ y).2]⟩
  obtain ⟨x, rfl⟩ := hq x
  obtain ⟨G, rfl⟩ := W.surj x
  show (F (qh (W.π G))).fst = _
  rw [hF]
  exact DFunLike.congr_fun hfst G

end SlopeTestRemainingChoices

theorem UpperTheory.exists_dualNumber_point_of_pointDerivation_vanishing :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {R S : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing S] [Algebra c.O S] [IsCO c.O S]
          (W : WPres c.O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[c.O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
          RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
          ∀ f : S →ₐ[c.O] PadicAlgCl l, IsLocPt f → ∀ D ∈ PtDer (f.comp (qh.comp W.A.val)) (PadicAlgCl l), (∀ y ∈ Ideal.span (Set.range g), D y = 0) →
            ∃ F : S →ₐ[c.O] DualNumber (PadicAlgCl l), dualFst F = f ∧ ∀ y : W.A, (F (qh y)).snd = D y := by
  intro l _ c R S _ _ _ _ _ _ W h qh hq κ g w _ hker hM f hf D hD hDI
  haveI := c.dvr
  haveI := c.fin
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite _ _
  exact md_main Subtype.val_injective (fun x => ⟨fun hx => (md_intIff x).1 (isIntegral_trans (A := c.O) x hx),
    fun hx => ((md_intIff x).2 hx).tower_top⟩) W h qh hq g hker hM f hf D hD hDI
