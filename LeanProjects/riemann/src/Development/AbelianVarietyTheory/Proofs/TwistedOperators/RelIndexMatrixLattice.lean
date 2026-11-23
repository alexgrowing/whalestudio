import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulActO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinear

open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm

theorem relIndex_comap_lattice {O K W : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
    (M : Submodule O W) [Submodule.IsLattice K M] (B : W →ₗ[K] W) (hB : Function.Bijective B) (hM : ∀ m ∈ M, B m ∈ M)
    {p : O} (hp : Irreducible p) : ∃ (m : ℕ) (u : Oˣ), LinearMap.det B * algebraMap O K u = algebraMap O K p ^ m ∧
      M.toAddSubgroup.relIndex (M.toAddSubgroup.comap B.toAddMonoidHom) = Nat.card (O ⧸ Ideal.span {p}) ^ m := by
  classical

  let f : M →ₗ[O] M := (B.restrictScalars O).restrict hM
  have hinj : Function.Injective f := fun x y hxy => Subtype.ext (hB.1 (congrArg Subtype.val hxy))
  let N : Submodule O M := LinearMap.range f
  have hrank : Module.finrank O N = Module.finrank O M := LinearMap.finrank_range_of_inj hinj
  let b := Module.Free.chooseBasis O M

  set a := Submodule.smithNormalFormCoeffs b hrank with ha_def
  set b' := Submodule.smithNormalFormTopBasis b hrank with hb'_def
  set ab := Submodule.smithNormalFormBotBasis b hrank with hab_def
  have hab : ∀ i, (ab i : M) = a i • b' i := Submodule.smithNormalFormBotBasis_def b hrank
  have ha0 : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank
  choose k u hku using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (ha0 i) hp
  have hassoc : ∀ i, Associated (a i) (p ^ k i) := fun i => by
    rw [hku i]; exact associated_unit_mul_left _ _ (Units.isUnit _)

  have hdiag : LinearMap.det (N.subtype ∘ₗ (b'.equiv ab (Equiv.refl _) : M →ₗ[O] N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply]
    rw [hab, map_smul, Module.Basis.repr_self, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hf_eq : f = N.subtype ∘ₗ (LinearEquiv.ofInjective f hinj : M →ₗ[O] N) := by
    ext x; rfl
  have hdet_assoc : Associated (LinearMap.det f) (p ^ ∑ i, k i) := by
    have h1 := LinearMap.associated_det_comp_equiv N.subtype (LinearEquiv.ofInjective f hinj)
      (b'.equiv ab (Equiv.refl _))
    rw [← hf_eq, hdiag] at h1
    refine h1.trans ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ _ _ fun i _ => hassoc i

  have hdet : LinearMap.det B = algebraMap O K (LinearMap.det f) := by
    let bK := b'.extendOfIsLattice K
    rw [← LinearMap.det_toMatrix bK, ← LinearMap.det_toMatrix b', RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    have h1 : B (bK j) = ((f (b' j) : M) : W) := by
      rw [Module.Basis.extendOfIsLattice_apply]; rfl
    have h2 : ((f (b' j) : M) : W) = ∑ x, algebraMap O K (b'.repr (f (b' j)) x) • bK x := by
      conv_lhs => rw [← b'.sum_repr (f (b' j))]
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, bK, Module.Basis.extendOfIsLattice_apply,
        algebraMap_smul]
    rw [h1, h2]
    exact congrFun (bK.repr_sum_self _) i
  obtain ⟨w, hw⟩ := hdet_assoc
  refine ⟨∑ i, k i, w, ?_, ?_⟩
  · rw [hdet, ← map_mul, hw, map_pow]

  have hidx : M.toAddSubgroup.relIndex (M.toAddSubgroup.comap B.toAddMonoidHom) = Nat.card (M ⧸ N) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective (f := B.toAddMonoidHom) _ _ hB.1,
      AddSubgroup.map_comap_eq_self_of_surjective hB.2]
    have hH : (M.toAddSubgroup.map B.toAddMonoidHom).addSubgroupOf M.toAddSubgroup = N.toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, N,
        LinearMap.mem_range]
      constructor
      · rintro ⟨y, hy, hyx⟩
        exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
    rw [AddSubgroup.relIndex, hH]
    rfl
  have hP0 : Ideal.span {p} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  rw [hidx, Nat.card_congr (Submodule.quotientEquivPiSpan N b hrank).toEquiv, Nat.card_pi,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← ha_def, Ideal.span_singleton_eq_span_singleton.2 (hassoc i), ← Ideal.span_singleton_pow,
    ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hP0]

section Det

variable {K : Type} [Field K] {a b : ℕ}

def mulR (b : ℕ) (G : Matrix (Fin a) (Fin a) K) : Matrix (Fin b) (Fin a) K →ₗ[K] Matrix (Fin b) (Fin a) K :=
  LinearMap.pi fun i : Fin b => (Matrix.toLin' Gᵀ).comp (LinearMap.proj i)

theorem mulR_apply (G : Matrix (Fin a) (Fin a) K) (w : Matrix (Fin b) (Fin a) K) : mulR b G w = w * G := by
  ext i j
  change (Matrix.toLin' Gᵀ (w i)) j = (w * G) i j
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]

theorem det_mulR (G : Matrix (Fin a) (Fin a) K) : LinearMap.det (mulR b G) = G.det ^ b := by

  have h : LinearMap.det (mulR b G) = LinearMap.det (M := Fin b → Fin a → K)
      (LinearMap.pi fun i : Fin b => (Matrix.toLin' Gᵀ).comp (LinearMap.proj i)) := rfl
  rw [h, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Matrix.det_transpose]

theorem exists_mul_map (H : Matrix (Fin b) (Fin b) K) (G : Matrix (Fin a) (Fin a) K) :
    ∃ B : Matrix (Fin b) (Fin a) K →ₗ[K] Matrix (Fin b) (Fin a) K, (∀ w, B w = H * w * G) ∧
      LinearMap.det B = G.det ^ b * H.det ^ a := by

  let L := (Matrix.transposeLinearEquiv (Fin b) (Fin a) K K).symm
  refine ⟨((L : Matrix (Fin a) (Fin b) K →ₗ[K] Matrix (Fin b) (Fin a) K) ∘ₗ mulR a Hᵀ ∘ₗ
      (L.symm : Matrix (Fin b) (Fin a) K →ₗ[K] Matrix (Fin a) (Fin b) K)) ∘ₗ mulR b G, fun w => ?_, ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, mulR_apply, LinearEquiv.coe_coe, L,
      LinearEquiv.symm_symm, Matrix.transposeLinearEquiv_apply, Matrix.mul_assoc]
    change ((w * G)ᵀ * Hᵀ)ᵀ = H * (w * G)
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  · rw [LinearMap.det_comp, LinearMap.det_conj, det_mulR, det_mulR, Matrix.det_transpose, mul_comm]

end Det

theorem absV_pow {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v)ˣ) (n : ℕ) :
    absV F v (x ^ n) = absV F v x ^ n := by
  induction n with
  | zero => simp [absV]
  | succ n ih => rw [pow_succ, absV_mul, ih, pow_succ]

theorem relIndex_matrix_lattice : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a b : ℕ) (M M' : AddSubgroup (Matrix (Fin b) (Fin a) (Fv F v))), (∀ o ∈ v.adicCompletionIntegers F, ∀ m ∈ M, (o : Fv F v) • m ∈ M) → (∃ N : ℕ, 0 < N ∧ ∀ m ∈ M, ∀ i j, (N : Fv F v) * m i j ∈ v.adicCompletionIntegers F) → (∀ w : Matrix (Fin b) (Fin a) (Fv F v), ∃ N : ℕ, 0 < N ∧ N • w ∈ M) → ∀ (H : Matrix (Fin b) (Fin b) (Fv F v)) (G : Matrix (Fin a) (Fin a) (Fv F v)) (x y : (Fv F v)ˣ), G.det = x → H.det = y → (∀ m ∈ M, H * m * G ∈ M) → (∀ w, w ∈ M' ↔ H * w * G ∈ M) → ((M.relIndex M' : ℕ) : ℝ) = (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV F v x ^ b * GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV F v y ^ a)⁻¹ := by
  intro F _ _ v a b M M' hsm hbd hsp H G x y hG hH hst hM'
  have hq : ∀ n : ℕ, 0 < n → (n : Fv F v) ≠ 0 := by
    intro n hn
    rw [← map_natCast (algebraMap F (Fv F v)) n]
    exact (map_ne_zero (algebraMap F (Fv F v))).2 (Nat.cast_ne_zero.2 hn.ne')

  let MO : Submodule (v.adicCompletionIntegers F) (Matrix (Fin b) (Fin a) (Fv F v)) :=
    { toAddSubmonoid := M.toAddSubmonoid
      smul_mem' := fun c m hm => hsm c c.2 m hm }

  obtain ⟨N0, hN0, hbdN⟩ := hbd
  let φ : (Fin b → Fin a → v.adicCompletionIntegers F) →ₗ[v.adicCompletionIntegers F]
      Matrix (Fin b) (Fin a) (Fv F v) :=
    { toFun := fun c => Matrix.of fun i j => (N0 : Fv F v)⁻¹ * (c i j : Fv F v)
      map_add' := fun c d => by
        ext i j
        simp [mul_add]
      map_smul' := fun r c => by
        ext i j
        simp [Algebra.smul_def]
        ring }
  have hle : MO ≤ LinearMap.range φ := by
    intro m hm
    refine ⟨fun i j => ⟨(N0 : Fv F v) * m i j, hbdN m hm i j⟩, ?_⟩
    ext i j
    simp [φ, inv_mul_cancel_left₀ (hq N0 hN0)]
  have hfg : MO.FG := by
    have : IsNoetherian (v.adicCompletionIntegers F) MO := isNoetherian_of_le hle
    rw [← Module.Finite.iff_fg]
    infer_instance
  have htop : Submodule.span (Fv F v) (MO : Set (Matrix (Fin b) (Fin a) (Fv F v))) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨n, hn, hnw⟩ := hsp w
    have h1 : w = (n : Fv F v)⁻¹ • (n • w) := by
      rw [← Nat.cast_smul_eq_nsmul (Fv F v), inv_smul_smul₀ (hq n hn)]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hnw)
  have hlat : Submodule.IsLattice (Fv F v) MO := ⟨hfg, htop⟩

  obtain ⟨B, hBw, hBdet⟩ := exists_mul_map H G
  have hdetB : LinearMap.det B ≠ 0 := by
    rw [hBdet, hG, hH]
    exact mul_ne_zero (pow_ne_zero _ x.ne_zero) (pow_ne_zero _ y.ne_zero)
  have hBbij : Function.Bijective B := by
    obtain ⟨U, hU⟩ := (LinearMap.isUnit_iff_isUnit_det B).2 (Ne.isUnit hdetB)
    have h1 : ∀ w, U.inv (B w) = w := fun w => by
      rw [← hU]; exact LinearMap.congr_fun U.inv_val w
    have h2 : ∀ w, B (U.inv w) = w := fun w => by
      rw [← hU]; exact LinearMap.congr_fun U.val_inv w
    exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

  obtain ⟨π0, hπ0⟩ := v.valuation_exists_uniformizer' F
  set pK : Fv F v := algebraMap F (Fv F v) (π0 : F) with hpK
  have hpv : Valued.v pK = WithZero.exp (-1) := by
    have h1 : Valued.v pK = v.valuation F (π0 : F) := v.valuedAdicCompletion_eq_valuation' (π0 : F)
    rw [h1]
    exact hπ0
  have hpmem : pK ∈ v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hpv]
    exact le_of_lt (by decide)
  set p : v.adicCompletionIntegers F := ⟨pK, hpmem⟩ with hp_def
  have hirr : Irreducible p := GlobalTheory.SplitUnif.irreducible_of_valued v p hpv
  have hpK0 : pK ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hpv
    exact WithZero.zero_ne_coe hpv

  have hP : ∀ z : 𝓞 F, z ∈ v.asIdeal ↔ Valued.v (algebraMap F (Fv F v) (z : F)) < 1 := by
    intro z
    have h1 : Valued.v (algebraMap F (Fv F v) (z : F)) = v.valuation F (z : F) :=
      v.valuedAdicCompletion_eq_valuation' (z : F)
    rw [h1]
    exact (v.valuation_lt_one_iff_mem (K := F) z).symm
  have hcard : Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {p}) = Ideal.absNorm v.asIdeal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer p).1 hirr]
    exact GlobalTheory.SplitUnif.card_residueField v (algebraMap F (Fv F v)) v (fun _ => rfl) hP
  obtain ⟨m, u, hdu, hidx⟩ := relIndex_comap_lattice MO B hBbij
    (fun w hw => by rw [hBw]; exact hst w hw) hirr
  have e2 : MO.toAddSubgroup.comap B.toAddMonoidHom = M' := AddSubgroup.ext fun w => by
    rw [AddSubgroup.mem_comap, hM']
    change B w ∈ M ↔ _
    rw [hBw]
  have e1 : MO.toAddSubgroup = M := AddSubgroup.ext fun _ => Iff.rfl
  rw [e2, e1, hcard] at hidx

  have hu0 : algebraMap (v.adicCompletionIntegers F) (Fv F v) (u : v.adicCompletionIntegers F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 u.ne_zero
  set U : (Fv F v)ˣ := Units.mk0 _ hu0 with hU
  set Pu : (Fv F v)ˣ := Units.mk0 pK hpK0 with hPu
  have hunits : x ^ b * y ^ a * U = Pu ^ m := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, U, Pu, Units.val_mk0]
    rw [← hG, ← hH, ← hBdet]
    exact hdu
  have hU1 : absV F v U = 1 := by
    have hle1 : Valued.v ((U : Fv F v)) ≤ 1 := (u : v.adicCompletionIntegers F).2
    have hnot : ¬ Valued.v ((U : Fv F v)) < 1 := fun hlt =>
      (IsLocalRing.notMem_maximalIdeal.2 u.isUnit) ((GlobalTheory.SplitUnif.mem_max v _).2 hlt)
    have hv1 : Valued.v ((U : Fv F v)) = 1 := le_antisymm hle1 (not_lt.1 hnot)
    rw [absV, hv1, WithZero.log_one, zpow_zero]
  have hP1 : absV F v Pu = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
    rw [absV, hPu, Units.val_mk0, hpv, WithZero.log_exp, _root_.zpow_neg_one]
  have hkey : absV F v x ^ b * absV F v y ^ a = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ m := by
    have h1 := congrArg (absV F v) hunits
    rw [absV_mul, absV_mul, absV_pow, absV_pow, absV_pow, hU1, mul_one, hP1] at h1
    exact h1
  rw [hidx, hkey, inv_pow, inv_inv, Nat.cast_pow]

theorem off_norm {R : Type} [CommRing R] {e c x y : R} (hx : (1 - e) * x = 1 - e) (hy : (1 - c) * y = 1 - c)
    (h : e * c = 0) : (1 - (e + c)) * (x * y) = 1 - (e + c) := by
  linear_combination ((1 - c) * y) * hx + (1 - e) * hy + (1 - x * y) * h

theorem off_norm' {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (hf : Function.Injective f) {ε n : A} {b z : R}
    (h1 : b = f ε) (h2 : f n = z) (h : (1 - b) * z = 1 - b) : (1 - ε) * n = 1 - ε := by
  apply hf
  rw [map_mul, map_sub, map_one, h2, ← h1]
  exact h

theorem off_norm'' {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {ε n : A} (h1 : f ε = 0)
    (h : (1 - ε) * n = 1 - ε) : f n = 1 := by
  have h' := congrArg f h
  simpa [map_mul, map_sub, map_one, h1] using h'

section Chart

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem chart_e (he : e * e = e) (hπ : GlobalTheory.SplitHecke.Chart e v π) : π e = 1 := by
  obtain ⟨-, hz, -, -⟩ := hπ
  have h0 : π (1 - e) = 0 := (hz _).2 (by rw [mul_sub, mul_one, he, sub_self])
  rw [map_sub, map_one, sub_eq_zero] at h0
  exact h0.symm

theorem conj_off {x : AE D} (hx : (1 - e) * x = 1 - e) : (1 - cA D e) * cA D x = 1 - cA D e := by
  have h' := congrArg (cA D) hx
  simpa only [map_mul, map_sub, map_one] using h'

theorem norm_at (h2 : e * cA D e = 0) (hπ : GlobalTheory.SplitHecke.Chart e v π) {x : AE D} (hx : (1 - e) * x = 1 - e) :
    evalV D.host.F v (sndA D.host.F (Algebra.norm (AF D.host.F) x)) = π x := by
  obtain ⟨-, hz, halg, -⟩ := hπ
  have hc : π (cA D e) = 0 := (hz _).2 h2
  have hcx : π (cA D x) = 1 := by
    have h' := congrArg π (conj_off hx)
    simpa [map_mul, map_sub, map_one, hc] using h'
  rw [← halg, GlobalTheory.SplitDetCharacter.algebraMap_norm, map_mul, hcx, mul_one]

theorem norm_off (he : IsSplitIdem D e) (hπ : GlobalTheory.SplitHecke.Chart e v π) {x : AE D} (hx : (1 - e) * x = 1 - e)
    {w : HeightOneSpectrum (𝓞 D.host.F)} (hw : w ≠ v) :
    evalV D.host.F w (sndA D.host.F (Algebra.norm (AF D.host.F) x)) = 1 := by
  obtain ⟨hee, hec, v', ε, ⟨α, rfl, -, hα0⟩, hsum⟩ := he

  have hv : v' = v := by
    by_contra hne
    have h1 := hπ.2.2.1 (pairA D.host.F 0 α)
    rw [← hsum, map_add, chart_e hee hπ, (hπ.2.1 _).2 hec, add_zero] at h1
    have h2 : evalV D.host.F v (sndA D.host.F (pairA D.host.F 0 α)) = 0 := hα0 v (Ne.symm hne)
    rw [h2] at h1
    exact one_ne_zero h1
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    fun a b hab => GlobalTheory.IdemModTwo.tmul_one_inj hab
  have key : (1 - pairA D.host.F 0 α) * Algebra.norm (AF D.host.F) x = 1 - pairA D.host.F 0 α :=
    off_norm' (algebraMap (AF D.host.F) (AE D)) hinj hsum (GlobalTheory.SplitDetCharacter.algebraMap_norm x)
      (off_norm hx (conj_off hx) hec)
  have hw' : w ≠ v' := by rw [hv]; exact hw
  exact off_norm'' ((evalV D.host.F w).toRingHom.comp (sndA D.host.F).toRingHom) (hα0 w hw') key

end Chart

theorem absFin_split : ∀ (D : D7) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → GlobalTheory.SplitHecke.Chart e v π → ∀ x : (AE D)ˣ, (1 - e) * (x : AE D) = 1 - e → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v (Units.map π.toMonoidHom x) := by
  intro D e v π he hπ x hx
  have hec : e * cA D e = 0 := he.2.1
  unfold absFin
  rw [finprod_eq_single _ v]
  · congr 1
    exact Units.ext (norm_at hec hπ hx)
  · intro w hw
    have h1 : normV D w x = 1 := Units.ext (norm_off he hπ hx hw)
    rw [h1]
    simp [absV]

end GlobalTheory.SplitLinear

end
