import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
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
open UpperTheory.Lit.CharWD GlobalTheory.Published
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  UpperTheory.V.W GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

private theorem val_of_norm
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [h2, toAdd_pow, nsmul_eq_mul]

variable [Algebra K L]

private theorem norm_loc (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ) :
    ∃ y : ((below K w).adicCompletion K)ˣ, GroundTheory.Global.ideleNorm K L (localIdele L w x) = localIdele K (below K w) y ∧
      Valued.v (y : (below K w).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, h, val_of_norm _ w _ x hm' _ (GlobalTheory.ArtinTransport.normV_eq_pow rfl)⟩

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
  classical
  have hφ : ∀ x, RingEquiv.refl Ω (algebraMap K Ω x) = algebraMap L Ω (algebraMap K L x) :=
    fun x => IsScalarTower.algebraMap_apply K L Ω x
  obtain ⟨ρ, hρc, hρ⟩ := GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv K Ω L Ω (RingEquiv.refl Ω) (algebraMap K L) hφ
  rw [← hρ τ σ hσ, ← hx, eq_comm, ← mul_inv_eq_one]
  refine GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup K Ω _ fun U hU => ?_
  let χ : Gab K Ω →* Gab K Ω ⧸ U := QuotientGroup.mk' U
  haveI : DiscreteTopology (Gab K Ω ⧸ U) := QuotientGroup.discreteTopology hU
  have hχ : Continuous χ := QuotientGroup.continuous_mk
  let Nm : Ideles L →* Ideles K := GroundTheory.Global.ideleNorm K L
  have hN : Continuous Nm := GroundTheory.Global.continuous_ideleNorm
  let ψ : Ideles L →* Gab K Ω ⧸ U := χ.comp (ρ.comp art') * (χ.comp (art.comp Nm))⁻¹
  have hψ : ∀ y, ψ y = χ (ρ (art' y)) * (χ (art (Nm y)))⁻¹ := fun _ => rfl
  have ho : IsOpen ((χ.comp art).ker : Set (Ideles K)) :=
    (isOpen_discrete {1}).preimage (hχ.comp ha.quot.continuous)
  obtain ⟨S, -, -, hS, -⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr K _ ho ∅
  have hT : {w : HeightOneSpectrum (𝓞 L) | ¬ below K w ∉ S}.Finite :=
    Filter.eventually_cofinite.1 ((tendsto_below (K := K) (L := L)).eventually S.eventually_cofinite_notMem)
  have h1 : ψ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away ψ
      ((hχ.comp (hρc.comp ha'.quot.continuous)).mul (hχ.comp (ha.quot.continuous.comp hN)).inv) (fun k => ?_) hT.toFinset
      fun w hw => ?_
    · have e : Nm (diagUnits L k) = diagUnits K _ := GroundTheory.Global.ideleNorm_diagonal (K := K) k
      rw [hψ, e, art_diag ha, art_diag ha']
      simp
    · have hv : below K w ∉ S := by simpa using hw
      have hu : ∀ x, IsUnitAt (below K w) x → χ (art (localIdele K (below K w) x)) = 1 := hS _ hv
      refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.comp (localIdele L w)) fun y hy => ?_
      have h2 := unif_spec (below K w)
      have h3 := (GlobalTheory.ArtinTransport.chi_artin_transport K Ω L Ω _ hφ art art' ha ha' ρ hρ _ χ (below K w) w rfl hu).2
        y _ hy h2
      obtain ⟨z, hz, hv⟩ := norm_loc (K := K) w y
      have h4 := hu (z * ((atFin _ (unif (below K w))) ^ w.asIdeal.inertiaDeg (𝓞 K))⁻¹) (by
        unfold IsUnitAt IsUnifAt at *
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, hy, h2]
        exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero))
      simp only [map_mul, map_inv, map_pow, mul_inv_eq_one] at h4
      rw [MonoidHom.comp_apply, hψ, h3, show Nm (localIdele L w y) = _ from hz, h4, mul_inv_cancel]
  have h5 := DFunLike.congr_fun h1 x
  rw [hψ, ← map_inv, ← map_mul] at h5
  exact (QuotientGroup.eq_one_iff _).1 h5

open Classical in
private theorem emb_norm {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 L)) (res : Emb l w → Emb l (below K w))
    (hres : ∀ τ' x, (res τ').1 x = τ'.1 (algebraMap _ _ x)) (τ : Emb l (below K w)) (y : w.adicCompletion L) :
    τ.1 (Algebra.norm ((below K w).adicCompletion K) y) = ∏ᶠ (τ' : Emb l w) (_ : res τ' = τ), τ'.1 y := by
  letI := τ.1.toAlgebra
  haveI : ContinuousSMul ((below K w).adicCompletion K) (Qbar l) := continuousSMul_of_algebraMap _ _ τ.2
  haveI : ContinuousSMul ((below K w).adicCompletion K) (w.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (continuous_completionMap _ _)
  haveI : FiniteDimensional ((below K w).adicCompletion K) (w.adicCompletion L) := inferInstance
  haveI : CharZero ((below K w).adicCompletion K) := algebraRat.charZero _
  have h := Algebra.norm_eq_prod_embeddings ((below K w).adicCompletion K) (Qbar l) y
  refine h.trans ?_
  rw [← finprod_eq_prod_of_fintype, ← finprod_subtype_eq_finprod_cond (f := fun τ' : Emb l w => τ'.1 y) (fun τ' => res τ' = τ)]
  have hc : ∀ σ : w.adicCompletion L →ₐ[(below K w).adicCompletion K] Qbar l, Continuous σ := fun σ => by
    letI : NontriviallyNormedField ((below K w).adicCompletion K) := Valued.toNontriviallyNormedField _ _
    have := LinearMap.continuous_of_finiteDimensional σ.toLinearMap
    exact this
  let e : (w.adicCompletion L →ₐ[(below K w).adicCompletion K] Qbar l) ≃ {τ' : Emb l w // res τ' = τ} :=
    { toFun := fun σ => ⟨⟨σ, hc σ⟩,
        Subtype.ext (RingHom.ext fun x => (hres _ x).trans (σ.commutes x))⟩
      invFun := fun τ' => ⟨τ'.1.1, fun x => (hres _ x).symm.trans (by rw [τ'.2]; rfl)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← finprod_comp_equiv e]
  rfl

end

theorem UpperTheory.Lit.CharWD.artNorm :
    GlobalArtinReciprocity → ArtNorm := by
  intro hG F F' Ω _ _ _ _ _ _ _ _ _ _ _ l _ A w w' h h' _
  obtain rfl : below F w' = w := HeightOneSpectrum.ext (GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h')
  refine ⟨fun τ' => ⟨τ'.1.comp (algebraMap _ _), τ'.2.comp (continuous_completionMap _ _)⟩,
    GroundTheory.LocalField.normUnits _ _, fun τ' x => ?_, fun τ y => emb_norm w' _ (fun _ _ => rfl) τ y,
    fun a a' ha ha' σ σ' hσ => ?_⟩
  · show τ'.1 (algebraMap _ _ (algebraMap F ((below F w').adicCompletion F) x)) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F F' (w'.adicCompletion F')]
  · obtain ⟨art, hart⟩ := hG F Ω
    obtain ⟨art', hart'⟩ := hG F' Ω
    refine GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart _ ?_
    refine (ha.glob art hart σ).trans ((glob_norm hart hart' _ _ _ hσ (ha'.glob art' hart' σ')).symm.trans ?_)
    exact congrArg art (GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w' (a' σ'))
