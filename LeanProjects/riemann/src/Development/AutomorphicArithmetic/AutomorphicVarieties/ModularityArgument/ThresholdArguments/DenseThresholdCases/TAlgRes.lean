import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base
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
private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem tendsto_under' :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl
omit [Algebra K L] in
private theorem ev_notMem (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
variable (L) in
private noncomputable def cN (χ : HChar K) : HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩
private theorem cN_loc (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion L)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      (cN L χ).loc w x = χ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, congrArg χ.1 h, val_of_norm _ w _ x hm' f hf⟩
private theorem cN_val (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (hχ : χ.UnrAt (w.under (𝓞 K))) : (cN L χ).UnrAt w ∧ (cN L χ).val w = χ.val (w.under (𝓞 K)) ^ f := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := cN_loc χ w f hf x
    rw [hy]
    apply hχ
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := cN_loc χ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hu : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hχ _ hu
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3
private theorem norm_infDiag (k : Lˣ) :
    GroundTheory.Global.ideleNorm K L (infDiag k) = infDiag (Units.map (Algebra.norm K : L →* K) k) := by
  refine Units.ext (Prod.ext (funext fun v => ?_) (Subtype.ext (funext fun v => ?_)))
  · have h1 := GroundTheory.Global.ideleNorm_fst (K := K) (infDiag k) v
    have h2 := GroundTheory.Global.ideleNorm_fst (K := K) (GroundTheory.Global.IdeleGroup.diagonal L k) v
    rw [GroundTheory.Global.ideleNorm_diagonal] at h2
    rw [GlobalTheory.HeckeGal.infDiag_eq] at h1 ⊢
    rw [GlobalTheory.HeckeGal.infDiag_eq]
    exact h1.trans h2.symm
  · have h1 := GroundTheory.Global.ideleNorm_snd (K := K) (infDiag k) v
    rw [GlobalTheory.HeckeGal.infDiag_eq] at h1 ⊢
    rw [GlobalTheory.HeckeGal.infDiag_eq]
    refine h1.trans (Finset.prod_eq_one fun w _ => ?_)
    exact map_one _
open Classical in
private theorem emb_norm (φ : K →+* ℂ) (x : L) :
    φ (Algebra.norm K x) = ∏ ψ ∈ Finset.univ.filter fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ, ψ x := by
  letI := φ.toAlgebra
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have h := Algebra.norm_eq_prod_embeddings K ℂ x
  refine h.trans ?_
  refine Finset.prod_bij (fun σ _ => (σ : L →+* ℂ)) (fun σ _ => ?_) (fun a _ b _ e => AlgHom.coe_ringHom_injective e)
    (fun ψ hψ => ⟨⟨ψ, fun r => DFunLike.congr_fun (Finset.mem_filter.1 hψ).2 r⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, RingHom.ext σ.commutes⟩
private theorem norm_pos (k : Lˣ) (hk : ∀ φ : L →+* ℝ, 0 < φ (k : L)) (φ : K →+* ℝ) : 0 < φ (Algebra.norm K (k : L)) := by
  classical
  have h := emb_norm (Complex.ofRealHom.comp φ) (k : L)
  have h0 : ∀ ψ : L →+* ℂ, ψ (k : L) ≠ 0 := fun ψ => (map_ne_zero ψ).2 k.ne_zero
  have h1 : ∏ ψ ∈ Finset.univ.filter fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = Complex.ofRealHom.comp φ,
      (ψ (k : L) / ((‖ψ (k : L)‖ : ℝ) : ℂ)) = 1 := by
    refine Finset.prod_involution (fun ψ _ => ComplexEmbedding.conjugate ψ) (fun ψ _ => ?_) (fun ψ _ hne e => hne ?_)
      (fun ψ hψ => ?_) fun ψ _ => star_star ψ
    · have : ((‖ψ (k : L)‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0 ψ
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, div_eq_one_iff_eq (mul_ne_zero this this)]
      push_cast; ring
    · have hr : ComplexEmbedding.IsReal ψ := ComplexEmbedding.isReal_iff.2 e
      have := hk hr.embedding
      rw [← ComplexEmbedding.IsReal.coe_embedding_apply hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos this]
      exact div_self (Complex.ofReal_ne_zero.2 this.ne')
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, RingHom.ext fun r => ?_⟩
      have e : ψ (algebraMap K L r) = ((φ r : ℝ) : ℂ) := DFunLike.congr_fun (Finset.mem_filter.1 hψ).2 r
      show ComplexEmbedding.conjugate ψ (algebraMap K L r) = ((φ r : ℝ) : ℂ)
      rw [ComplexEmbedding.conjugate_coe_eq, e, Complex.conj_ofReal]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun ψ _ => by simpa using h0 ψ),
    ← Complex.ofReal_prod] at h1
  have h2 : ((φ (Algebra.norm K (k : L)) : ℝ) : ℂ) = _ := h.trans h1
  rw [Complex.ofReal_inj.1 h2]
  exact Finset.prod_pos fun ψ _ => norm_pos_iff.2 (h0 ψ)
private theorem cN_alg {χ : HChar K} {a : (K →+* ℂ) → ℤ} (h : IsAlgPos χ a) :
    IsAlgPos (cN L χ) fun ψ => a (ψ.comp (algebraMap K L)) := by
  classical
  intro k hk
  have e : (cN L χ).inf k = χ.inf (Units.map (Algebra.norm K : L →* K) k) := congrArg χ.1 (norm_infDiag k)
  rw [e, h _ (norm_pos k hk), ← Finset.prod_fiberwise (s := Finset.univ) (g := fun ψ : L →+* ℂ => ψ.comp (algebraMap K L))]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [Units.coe_map, emb_norm, ← Finset.prod_zpow]
  exact Finset.prod_congr (by convert rfl) fun ψ hψ => by simp only [(Finset.mem_filter.1 hψ).2]
end
theorem UpperTheory.V.Sd.alg_restriction_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.AlgRes := by
  intro P F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι κ ⟨hc, art, χ, a, ha, h1, h⟩
  obtain ⟨art', ha'⟩ := P.litN.aut.art E Ω
  have h1' := cN_alg (L := E) h1
  obtain ⟨μ, hμ, hL⟩ := ha'.exists_isLAdicOf ι h1'
  have hc' : Continuous (κ.comp (galEmb F E Ω)) := hc.comp (continuous_restrictScalarsHom F E Ω)
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ (cN E χ).UnrAt w ∧
      CharEig ι (κ.comp (res F Ω E)) w ((cN E χ).val w : ℂˣ) := by
    filter_upwards [(tendsto_under' (K := F) (L := E)).eventually
      ((Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)).and (ev_notMem l)), ev_notMem (K := E) l]
      with w ⟨hu, hl⟩ hl'
    have hf := normV_under (K := F) w
    obtain ⟨k1, k2⟩ := cN_val χ w _ hf hu
    refine ⟨hl', k1, ?_⟩
    rw [k2, Units.val_pow_eq_pow_val]
    refine (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 κ _ fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => κ.comp (galEmb F E Ω) s) (f' := fun s => μ s)
    hc' hμ fun v hv _ A hA σ hσ => by
      obtain ⟨hl, hu, hE⟩ := not_not.1 hv
      have e := (hE A hA).2 σ hσ
      refine Units.ext ?_
      rw [hL.frob_unr ha' (Or.inl hl) hu hA hσ, ← e, ι.symm_apply_apply, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      rfl
  have e : κ.comp (galEmb F E Ω) = μ := MonoidHom.ext fun s => congrFun key s
  rw [e]
  exact ⟨hμ, art', _, _, ha', h1', hL⟩
end
