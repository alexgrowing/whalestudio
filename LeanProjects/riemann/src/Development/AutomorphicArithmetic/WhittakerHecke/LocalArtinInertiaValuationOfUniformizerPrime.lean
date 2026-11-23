import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.DzTameRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAbelianizedGaloisHomOfClosureIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTransportAlgClosureEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds

section Norm

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

private theorem to_nnreal_pow_of_eq_pow {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) {f : ℕ} (hf : f ≠ 0)
    (hab : b = a ^ f) (m : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal hb m = WithZeroMulInt.toNNReal ha m ^ f := by
  by_cases hm : m = 0
  · subst hm
    simp [hf]
  · rw [WithZeroMulInt.toNNReal_neg_apply hb hm, WithZeroMulInt.toNNReal_neg_apply ha hm, hab,
      ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]

private theorem val_of_norm
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hq : ∀ {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)),
      (Ideal.absNorm u.asIdeal : NNReal) = (normV u : NNReal) := by
    intro F _ _ u
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def] at h
  have h2 := NNReal.coe_injective h
  have hwq : (Ideal.absNorm w.asIdeal : NNReal) = (Ideal.absNorm v.asIdeal : NNReal) ^ f := by
    rw [hq, hq, hf]
    push_cast
    rfl
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h1 := one_lt_normV w
    rw [hf, pow_zero] at h1
    exact lt_irrefl _ h1
  rw [to_nnreal_pow_of_eq_pow (HeightOneSpectrum.absNorm_ne_zero v) _ hf0 hwq, ← map_pow] at h2
  exact (WithZeroMulInt.toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal v)).injective h2

variable [Algebra K L]

private theorem norm_loc (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ) :
    ∃ y : ((below K w).adicCompletion K)ˣ, GroundTheory.Global.ideleNorm K L (localIdele L w x) = localIdele K (below K w) y ∧
      Valued.v (y : (below K w).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  refine ⟨GroundTheory.LocalField.normUnits _ _ x, GroundTheory.Global.ideleNorm_finiteEmbedding w x, ?_⟩
  refine val_of_norm (below K w) w _ x ?_ _ (GlobalTheory.ArtinTransport.normV_eq_pow ?_)
  · have h1 := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K) (IdeleGroup.finiteEmbedding w x)
    rw [GroundTheory.Global.ideleNorm_finiteEmbedding] at h1
    rw [← IdeleGroup.ideleModule_finiteEmbedding, ← IdeleGroup.ideleModule_finiteEmbedding, h1]
  · exact ((below_eq_iff w (below K w)).1 rfl).over.symm

omit [Algebra K L] in
private theorem art_diag {Ω : Type} [Field Ω] [Algebra K Ω] {art : Ideles K →* Gab K Ω} (ha : IsGlobalArtin art) (k : Kˣ) :
    art (diagUnits K k) = 1 := by
  have hk : diagUnits K k ∈ art.ker := by
    rw [ha.ker]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
  exact hk

private theorem glob_norm {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω]
    [IsAlgClosure L Ω] {art : Ideles K →* Gab K Ω} {art' : Ideles L →* Gab L Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (x : Ideles L) (τ : G L Ω) (σ : G K Ω) (hσ : ∀ z, σ z = τ z) (hx : art' x = toAb L Ω τ) :
    art (GroundTheory.Global.ideleNorm K L x) = toAb K Ω σ := by
  obtain ⟨ρ, hρc, hρ⟩ := exists_abHom_of_ringEquiv K Ω L Ω (RingEquiv.refl Ω) (algebraMap K L)
    (fun z => IsScalarTower.algebraMap_apply K L Ω z)
  have hρσ : ρ (toAb L Ω τ) = toAb K Ω σ := hρ τ σ (fun z => hσ z)
  rw [← hρσ, ← hx]
  let ψ : Ideles L →* Gab K Ω := art.comp (GroundTheory.Global.ideleNorm K L) / ρ.comp art'
  suffices hψ : ∀ y, ψ y = 1 by
    have h0 := hψ x
    simp only [ψ, MonoidHom.div_apply, MonoidHom.comp_apply, div_eq_one] at h0
    exact h0
  intro y
  apply GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup K Ω
  intro U hU
  haveI : IsClosed (U : Set (Gab K Ω)) := U.isClosed_of_isOpen hU
  let χ : Gab K Ω →* Gab K Ω ⧸ U := QuotientGroup.mk' U
  have hχc : Continuous χ := continuous_quot_mk
  have hart : Continuous art := ha.quot.continuous
  have hart' : Continuous art' := ha'.quot.continuous
  have hψc : Continuous ψ := (hart.comp GroundTheory.Global.continuous_ideleNorm).div' (hρc.comp hart')
  obtain ⟨S, M, -, hS, -⟩ :=
    GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr K (U.comap art) (hU.preimage hart) ∅
  have hfin : (below K (L := L) ⁻¹' (S : Set (HeightOneSpectrum (𝓞 K)))).Finite := by
    have h1 := Filter.mem_cofinite.1
      (GroundTheory.Global.AdeleBaseChange.tendsto_below (K := K) (L := L) S.finite_toSet.compl_mem_cofinite)
    rwa [Set.preimage_compl, compl_compl] at h1
  have hloc : ∀ w ∉ hfin.toFinset, ∀ z, (χ.comp ψ) (localIdele L w z) = 1 := by
    intro w hw
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe] at hw
    have hcomap : Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal = (below K w).asIdeal :=
      ((below_eq_iff w (below K w)).1 rfl).over.symm
    have hunit : ∀ z, IsUnitAt (below K w) z → χ (art (localIdele K (below K w) z)) = 1 := by
      intro z hz
      exact (QuotientGroup.eq_one_iff _).2 (hS _ hw z hz)
    obtain ⟨-, h2⟩ := GlobalTheory.ArtinTransport.chi_artin_transport K Ω L Ω (RingEquiv.refl Ω)
      (fun z => IsScalarTower.algebraMap_apply K L Ω z) art art' ha ha' ρ (fun τ' σ' h => hρ τ' σ' h)
      _ χ (below K w) w hcomap hunit
    obtain ⟨k, hk⟩ := exists_unif (below K w)
    refine GlobalTheory.FrobDense.eq_one_of_unif ((χ.comp ψ).comp (localIdele L w)) ?_
    intro z hz
    obtain ⟨y, hy, hyv⟩ := norm_loc (K := K) w z
    have hu : IsUnitAt (below K w) (y * (atFin (below K w) k ^ w.asIdeal.inertiaDeg (𝓞 K))⁻¹) := by
      unfold IsUnitAt
      unfold IsUnifAt at hk hz
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow,
        hyv, hz, hk]
      exact mul_inv_cancel₀ (pow_ne_zero _ (by simp))
    have e1 := hunit _ hu
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, map_pow, map_pow, map_pow,
      mul_inv_eq_one] at e1
    simp only [MonoidHom.comp_apply, ψ, MonoidHom.div_apply, map_div]
    rw [hy, e1, h2 z _ hz hk, div_self']
  have hall := GlobalTheory.FrobDense.eq_one_of_away (χ.comp ψ) (hχc.comp hψc) ?_ hfin.toFinset hloc
  · exact (QuotientGroup.eq_one_iff _).1 (DFunLike.congr_fun hall y)
  · intro k
    have e1 : GroundTheory.Global.ideleNorm K L (diagUnits L k) = diagUnits K (Units.map (Algebra.norm K) k) :=
      GroundTheory.Global.ideleNorm_diagonal k
    simp only [MonoidHom.comp_apply, ψ, MonoidHom.div_apply]
    rw [e1, art_diag ha, art_diag (K := L) ha' k, map_one, div_one, map_one]

private theorem norm_at_unique (v : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L))
    (hW : W.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal)
    (hu : ∀ W' : HeightOneSpectrum (𝓞 L), W'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal → W' = W) (y : Lˣ) :
    GroundTheory.Global.ideleNorm K L (localIdele L W (Units.map (algebraMap L (W.adicCompletion L)).toMonoidHom y)) =
      localIdele K v (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom
        (Units.map (Algebra.norm K (S := L)) y)) := by
  have hv : below K W = v := (below_eq_iff W v).2 ⟨hW.symm⟩
  subst hv
  refine (GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) W _).trans ?_
  show IdeleGroup.finiteEmbedding _ _ = IdeleGroup.finiteEmbedding _ _
  congr 1
  apply Units.ext
  rw [GroundTheory.LocalField.coe_normUnits]
  have h := GroundTheory.Global.ideleNorm_snd (K := K) (L := L) (IdeleGroup.diagonal L y) (below K W)
  rw [GroundTheory.Global.ideleNorm_diagonal] at h
  have hW' : W.asIdeal.LiesOver (below K W).asIdeal := (below_eq_iff W _).1 rfl
  rw [Fintype.prod_eq_single ⟨W, hW'⟩ ?_] at h
  · exact h.symm
  · intro w hw
    exact absurd (Subtype.ext (hu w.1 w.2.over.symm)) hw

private theorem res_art_norm (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω) (ha : IsGlobalArtin art) (haK : IsGlobalArtin artK)
    (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K))
    (hW : W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (hu : ∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W)
    (y : Kˣ) (τ : G K Ω)
    (hτ : toAb K Ω τ = artK (localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y))) :
    toAb E Ω (τ.restrictScalars E) =
      art (localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
        (Units.map (Algebra.norm E (S := K)) y))) := by
  rw [← norm_at_unique v W hW hu y]
  exact (glob_norm ha haK _ τ (τ.restrictScalars E) (fun z => rfl) hτ.symm).symm

end Norm

section Frob

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

private theorem frob_fix : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : G E Ω, IsFrob (F := E) A (normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  intro hGAR E Ω _ _ _ _ _ art ha v A hA ϖ hϖ hϖ2 π hπ
  have hq : 1 < normV v := GlobalTheory.WeilDeligne.one_lt_normV v
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h0
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h0
    rw [this]
    exact Ideal.zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hϖ0 ((FaithfulSMul.algebraMap_eq_zero_iff E Ω).1 hπ.symm)
  have hint : IsIntegral E π := by
    refine ⟨Polynomial.X ^ (normV v - 1) - Polynomial.C (ϖ : E),
      Polynomial.monic_X_pow_sub_C _ (by omega), ?_⟩
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hπ]
  haveI hfd : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI hnf : NumberField (IntermediateField.adjoin E {π}) :=
    NumberField.of_module_finite E (IntermediateField.adjoin E {π})
  haveI halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI hac : IsAlgClosure (IntermediateField.adjoin E {π}) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  obtain ⟨W, hW, hu, hAW, hNW, hunif⟩ := GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place E Ω v A hA ϖ hϖ hϖ2 π hπ
  obtain ⟨artK, haK⟩ := hGAR (IntermediateField.adjoin E {π}) Ω
  have hg0 : IntermediateField.AdjoinSimple.gen E π ≠ 0 := by
    intro h0
    apply hπ0
    have := congrArg (algebraMap (IntermediateField.adjoin E {π}) Ω) h0
    simpa using this
  have hnorm := (GlobalTheory.TameEis.minpoly_and_norm_of_pow_eq_uniformizer E Ω v ϖ hϖ hϖ2 π hπ).2
  have hc' : IsUnifAt W (Units.map (algebraMap (IntermediateField.adjoin E {π})
      (W.adicCompletion (IntermediateField.adjoin E {π}))).toMonoidHom (Units.mk0 _ hg0)) := hunif _ rfl
  obtain ⟨σ', hσ'F, hσ'⟩ := (haK.frob W A hAW _).1 ⟨_, hc', rfl⟩
  have hres := res_art_norm E Ω (IntermediateField.adjoin E {π}) art artK ha haK v W hW hu
    (Units.mk0 _ hg0) σ'⁻¹ hσ'
  refine ⟨σ'.restrictScalars E, ⟨hσ'F.1, fun x hx => ?_⟩, ?_, fun c hc => ?_⟩
  · rw [← hNW]
    exact hσ'F.2 x hx
  · exact σ'.commutes (IntermediateField.AdjoinSimple.gen E π)
  · have hinv : (σ'.restrictScalars E)⁻¹ = (σ'⁻¹).restrictScalars E := rfl
    rw [hinv, hres]
    congr 2
    ext
    rw [hc]
    simp [Units.coe_map, hnorm]

private theorem ine_of_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) → ∀ (x : (v.adicCompletion E)ˣ) (u : 𝓞 E), IsUnitAt v x → Valued.v ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) < 1 → ∃ σ ∈ Ine (F := E) A, toAb E Ω σ = art (localIdele E v x) ∧ A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 := by
  intro hGAR E Ω _ _ _ _ _ art ha v A hA ϖ hϖ hϖ2 π hπ x u hx hxu
  have hq : 1 < normV v := GlobalTheory.WeilDeligne.one_lt_normV v
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hx1 : Valued.v (x : v.adicCompletion E) = 1 := hx
  have hvu : Valued.v (algebraMap E (v.adicCompletion E) (u : E)) = 1 := by
    rw [← hx1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [Valuation.map_sub_swap, hx1]
    exact hxu
  have hun : u ∉ v.asIdeal := by
    intro hm
    have h2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).2 hm
    have h3 : v.valuation E (u : E) = 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hvu
    exact (ne_of_lt h2) h3
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h0
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h0
    rw [this]
    exact Ideal.zero_mem _
  have hu0 : (u : E) ≠ 0 := by
    intro h0
    apply hun
    have : u = 0 := by exact_mod_cast h0
    rw [this]
    exact Ideal.zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hϖ0 ((FaithfulSMul.algebraMap_eq_zero_iff E Ω).1 hπ.symm)
  have hϖ' : ϖ * u ∈ v.asIdeal := Ideal.mul_mem_right _ _ hϖ
  have hrad : (v.asIdeal ^ 2).radical = v.asIdeal := by
    rw [Ideal.radical_pow v.asIdeal two_ne_zero, v.isPrime.radical]
  have hϖ2' : ϖ * u ∉ v.asIdeal ^ 2 := by
    intro hm
    have hP : (v.asIdeal ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by
      rw [hrad]
      exact v.isMaximal)
    rcases (Ideal.isPrimary_iff.1 hP).2 hm with h | h
    · exact hϖ2 h
    · rw [hrad] at h
      exact hun h
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (u : E)) (show 0 < normV v - 1 by omega)
  have hπt : (π * t) ^ (normV v - 1) = algebraMap E Ω ((ϖ * u : 𝓞 E) : E) := by
    rw [mul_pow, hπ, ht, ← map_mul]
    push_cast
    rfl
  obtain ⟨τ, hτF, hτπ, hτc⟩ := frob_fix hGAR E Ω art ha v A hA ϖ hϖ hϖ2 π hπ
  obtain ⟨τ', hτ'F, hτ'π, hτ'c⟩ := frob_fix hGAR E Ω art ha v A hA (ϖ * u) hϖ' hϖ2' (π * t) hπt
  have hI1 := GlobalTheory.T.frobenius_inv_mul_mem_inertia E Ω v A hA τ τ' hτF hτ'F
  have hV1 := GlobalTheory.T.frobenius_ratio_pi_congr_tame_unit E Ω v A hA u hun π t hπ0 ht τ τ' hτF hτ'F hτπ hτ'π
  set cϖ : (v.adicCompletion E)ˣ := (-1) ^ normV v * atFin v (Units.mk0 _ hϖ0) with hcϖ
  set cu : (v.adicCompletion E)ˣ := atFin v (Units.mk0 _ hu0) with hcu
  have hcu' : (cu : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (u : E) := by
    simp [hcu, atFin]
  have e1 := hτc cϖ (by simp [hcϖ, atFin])
  have e2 := hτ'c (cϖ * cu) (by
    simp [hcϖ, hcu, atFin]
    ring)
  have e0 : toAb E Ω τ = (art (localIdele E v cϖ))⁻¹ := by
    rw [← e1, map_inv, inv_inv]
  have e3 : toAb E Ω (τ'⁻¹ * τ) = art (localIdele E v cu) := by
    rw [map_mul, e2, e0, map_mul, map_mul, mul_right_comm, mul_inv_cancel, one_mul]
  have hy : Valued.v (((cu⁻¹ * x : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) < 1 := by
    have hsplit : ((cu⁻¹ * x : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1 =
        ((x : v.adicCompletion E) - (cu : v.adicCompletion E)) * ((cu⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
      rw [sub_mul, Units.mul_inv, Units.val_mul, mul_comm]
    have hcuinv : Valued.v ((cu⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hcu', hvu, inv_one]
    rw [hsplit, map_mul, hcuinv, mul_one, hcu']
    exact hxu
  obtain ⟨z, hz1, hzy⟩ := GlobalTheory.T.exists_unit_pow_normV_sub_one' E v (cu⁻¹ * x) hy
  obtain ⟨ρ, hρI, hρ⟩ := (ha.ine v A hA (art (localIdele E v z))).1 ⟨z, hz1, rfl⟩
  refine ⟨(τ'⁻¹ * τ) * ρ ^ (normV v - 1), mul_mem hI1 (pow_mem hρI _), ?_, ?_⟩
  · rw [map_mul, e3, map_pow, hρ, ← map_pow, ← map_pow, hzy, ← map_mul, ← map_mul, mul_inv_cancel_left]
  · rw [AlgEquiv.mul_apply, GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem E Ω v A hA (ϖ : E) π hπ ρ hρI]
    exact hV1

end Frob

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Main

open Polynomial Neutral.B1 GlobalTheory.HeckeGal

private theorem weil_smul_eq_of_local_artin_eq {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 M)} (h : IsPlaceOver A v)
    (a : Weil h →* (v.adicCompletion M)ˣ) (ha : IsLocalArtin h a) (π : Ω) (c : M) (hπ0 : π ≠ 0)
    (hπ : π ^ (normV v - 1) = algebraMap M Ω c) (s s' : Weil h) (hs : a s = a s') :
    (s : G M Ω) π = (s' : G M Ω) π := by
  have hn : 0 < normV v - 1 := by
    have := one_lt_normV v
    omega
  have hne : ∀ s : Weil h, (s : G M Ω) π ≠ 0 := fun s => (_root_.map_ne_zero _).2 hπ0
  have hroot : ∀ s : Weil h, ((s : G M Ω) π / π) ^ (normV v - 1) = 1 := by
    intro s
    rw [div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  have hmul : ∀ s s' : Weil h, ((s * s' : Weil h) : G M Ω) π / π =
      ((s : G M Ω) π / π) * ((s' : G M Ω) π / π) := by
    intro s s'
    have hs' : (s' : G M Ω) π = ((s' : G M Ω) π / π) * π := (div_mul_cancel₀ _ hπ0).symm
    have hfix := DiscreteGroups.sglob.DzType.weil_fix_root h s _ (hroot s')
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hs', map_mul, hfix]
    field_simp
  let κ : Weil h →* Ωˣ :=
    { toFun := fun s => Units.mk0 ((s : G M Ω) π / π) (div_ne_zero (hne s) hπ0)
      map_one' := by
        ext
        simp [hπ0]
      map_mul' := fun s s' => by
        ext
        simp only [Units.val_mk0, Units.val_mul]
        exact hmul s s' }
  have hκ : ∀ s, κ s ∈ rootsOfUnity (normV v - 1) Ω := by
    intro s
    rw [mem_rootsOfUnity]
    ext
    simp [κ, hroot s]
  let κ' := κ.codRestrict (rootsOfUnity (normV v - 1) Ω) hκ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed M
  haveI : NeZero (normV v - 1) := ⟨hn.ne'⟩
  haveI : NeZero ((normV v - 1 : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have hcard : Nat.card (rootsOfUnity (normV v - 1) Ω) = Nat.card (rootsOfUnity (normV v - 1) ℂ) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Complex.card_rootsOfUnity]
  let e := mulEquivOfCyclicCardEq hcard
  let ξ : Weil h →* ℂˣ := (rootsOfUnity (normV v - 1) ℂ).subtype.comp (e.toMonoidHom.comp κ')
  have hξ : ∀ s, ξ s = 1 ↔ (s : G M Ω) π = π := by
    intro s
    have h1 : ξ s = 1 ↔ κ' s = 1 := by
      simp only [ξ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]
    rw [h1, Subtype.ext_iff, MonoidHom.codRestrict_apply, OneMemClass.coe_one, Units.ext_iff]
    simp only [κ, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Units.val_one]
    exact div_eq_one_iff_eq hπ0
  have hsm : IsSmooth ξ := by
    haveI : Algebra.IsAlgebraic M Ω := IsAlgClosure.isAlgebraic
    haveI : FiniteDimensional M (IntermediateField.adjoin M {π}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic π).isIntegral
    have hO : IsOpen (((IntermediateField.adjoin M {π}).fixingSubgroup.comap (Ine (F := M) A).subtype : Subgroup (Ine (F := M) A)) :
        Set (Ine (F := M) A)) :=
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin M {π})).preimage continuous_subtype_val
    show IsOpen (((ξ.comp (ineIncl h)).ker : Subgroup (Ine (F := M) A)) : Set (Ine (F := M) A))
    refine Subgroup.isOpen_mono ?_ hO
    intro τ hτ
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hξ]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ π (IntermediateField.subset_adjoin M {π} (Set.mem_singleton π))
  obtain ⟨χ, -, hχ⟩ := ha.factor ξ hsm
  have h2 : ξ (s'⁻¹ * s) = 1 := by
    rw [map_mul, map_inv, hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, hs, inv_mul_cancel]
  have h3 := (hξ _).1 h2
  have h4 := congrArg (s' : G M Ω) h3
  rwa [← AlgEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel_left] at h4

private theorem tame_all : ∀ (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A v), ((g : ℕ) : 𝓞 M) ∈ v.asIdeal → ((g : ℕ) : 𝓞 M) ∉ v.asIdeal ^ 2 → ∀ a : Weil h →* (v.adicCompletion M)ˣ, IsLocalArtin h a → ∀ π : Ω, π ^ (normV v - 1) = (g : Ω) → ∀ (t : Ine (F := M) A) (x : 𝓞 M), Valued.v ((a (ineIncl h t) : v.adicCompletion M) - algebraMap M (v.adicCompletion M) (x : M)) < 1 → A.valuation ((t : G M Ω) π / π - algebraMap M Ω (x : M)) < 1 := by
  intro M Ω _ _ _ _ _ g _ A v h hg hg2 a ha π hπ t x hx
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds M Ω
  have hu := GlobalTheory.ArtinInertia.isUnitAt_artin_ine h a ha t
  have hπ' : π ^ (normV v - 1) = algebraMap M Ω (((g : ℕ) : 𝓞 M) : M) := by
    rw [hπ]
    simp
  have hπ0 : π ≠ 0 := by
    haveI := charZero_of_injective_algebraMap (algebraMap M Ω).injective
    have hg0 : ((g : ℕ) : Ω) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
    rintro rfl
    have hq := one_lt_normV v
    rw [zero_pow (by omega)] at hπ
    exact hg0 hπ.symm
  obtain ⟨σ, hσI, hσ, hσv⟩ := ine_of_unit GlobalTheory.globalArtinReciprocity_holds M Ω art hart v A h
    ((g : ℕ) : 𝓞 M) hg hg2 π hπ' (a (ineIncl h t)) x hu hx
  have heq : a (ineIncl h ⟨σ, hσI⟩) = a (ineIncl h t) := by
    apply GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' M Ω art hart v
    simp only [ha.glob art hart]
    rw [ha.glob art hart] at hσ
    exact hσ
  have key := weil_smul_eq_of_local_artin_eq h a ha π _ hπ0 hπ' _ _ heq
  have key' : (t : G M Ω) π = σ π := key.symm
  rw [key']
  exact hσv

end Main

theorem UpperTheory.localArtin_inertia_valuation_of_uniformizer_prime :
    ∀ (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A v), ((g : ℕ) : 𝓞 M) ∈ v.asIdeal → ((g : ℕ) : 𝓞 M) ∉ v.asIdeal ^ 2 → ∀ a : Weil h →* (v.adicCompletion M)ˣ, IsLocalArtin h a → ∀ π : Ω, π ^ (normV v - 1) = (g : Ω) → ∀ (t : Ine (F := M) A) (x : 𝓞 M), Valued.v ((a (ineIncl h t) : v.adicCompletion M) - algebraMap M (v.adicCompletion M) (x : M)) < 1 → A.valuation ((t : G M Ω) π / π - algebraMap M Ω (x : M)) < 1 :=
  tame_all
