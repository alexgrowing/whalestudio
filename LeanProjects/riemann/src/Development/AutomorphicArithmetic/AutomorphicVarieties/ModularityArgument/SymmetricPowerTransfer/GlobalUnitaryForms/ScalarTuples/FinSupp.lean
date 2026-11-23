import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GlobNegOne

open NumberField IsDedekindDomain Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

private theorem lmap_star' {K K' : Type} [Field K] [Field K'] (f : K →+* K') (Δ : K) (x : Lsq K Δ) :
    lmap f Δ (star x) = star (lmap f Δ x) := by
  ext <;> simp [lmap]

private theorem el_mk {K : Type} [Field K] {Δ : K} (a b : Lsq K Δ) (h : a * star a + b * star b = 1) :
    ∃ γ : DX Δ, mt γ = !![a, b; -star b, star a] := by
  let g : GL (Fin 2) (Lsq K Δ) := ⟨!![a, b; -star b, star a], !![star a, -b; star b, a], by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    ext1 i; fin_cases i <;> (ext1 j; fin_cases j) <;> simp <;> first | ring1 | linear_combination h, by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    ext1 i; fin_cases i <;> (ext1 j; fin_cases j) <;> simp <;> first | ring1 | linear_combination h⟩
  refine ⟨⟨g, ?_⟩, rfl⟩
  change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * ((wJ Δ)⁻¹)⁻¹
  rw [inv_inv]
  refine Units.ext ?_
  change (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) =
    !![0, -1; 1, 0] * !![a, b; -star b, star a] * !![0, 1; -1, 0]
  ext1 i j
  fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]

private theorem el_form {K : Type} [Field K] {Δ : K} (γ : DX Δ) :
    mt γ 1 1 = star (mt γ 0 0) ∧ mt γ 1 0 = -star (mt γ 0 1) := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) γ.1 = (wJ Δ)⁻¹ * γ.1 * ((wJ Δ)⁻¹)⁻¹ := γ.2
  rw [inv_inv] at h
  have h' : (mt γ).map (starRingEnd _) = !![0, -1; 1, 0] * mt γ * !![0, 1; -1, 0] := congrArg Units.val h
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] at h0 h1
  exact ⟨h0.symm, by rw [h1, neg_neg]⟩

private theorem tr_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ τ : K} (γ : DX Δ) (h : HasTr γ τ) :
    ∃ γ' : DX (f Δ), HasTr γ' (f τ) := by
  obtain ⟨s₁, s₂⟩ := el_form γ
  obtain ⟨hd, ht⟩ := h
  rw [Matrix.det_fin_two, s₁, s₂] at hd
  rw [Matrix.trace_fin_two, s₁] at ht
  generalize mt γ 0 0 = a at hd ht
  generalize mt γ 0 1 = b at hd
  have hd' : lmap f Δ a * star (lmap f Δ a) + lmap f Δ b * star (lmap f Δ b) = 1 := by
    have h1 := congrArg (lmap f Δ) hd
    rw [map_sub, map_mul, map_mul, map_neg, lmap_star', lmap_star', map_one] at h1
    linear_combination h1
  obtain ⟨γ', e⟩ := el_mk _ _ hd'
  refine ⟨γ', ?_, ?_⟩
  · rw [e, Matrix.det_fin_two_of]
    linear_combination hd'
  · rw [e, Matrix.trace_fin_two_of, ← lmap_star', ← map_add, ht]
    ext <;> simp [lmap]

private theorem conj_tr {K : Type} [Field K] {Δ τ : K} {γ : DX Δ} (h : HasTr γ τ) (y : DX Δ) :
    HasTr (y⁻¹ * γ * y) τ := by
  have e : mt (y⁻¹ * γ * y) = mt y⁻¹ * mt γ * mt y := rfl
  have e1 : mt y⁻¹ * mt y = 1 := by
    rw [show mt y⁻¹ * mt y = mt (y⁻¹ * y) from rfl, inv_mul_cancel]; rfl
  have e2 : mt y * mt y⁻¹ = 1 := by
    rw [show mt y * mt y⁻¹ = mt (y * y⁻¹) from rfl, mul_inv_cancel]; rfl
  refine ⟨?_, ?_⟩
  · rw [e, Matrix.det_mul, Matrix.det_mul, h.1, mul_one, ← Matrix.det_mul, e1, Matrix.det_one]
  · rw [e, Matrix.trace_mul_comm, ← mul_assoc, e2, one_mul]
    exact h.2

private theorem supp_el {K : Type} [Field K] [CharZero K] (O : Type) [CommRing O] [Algebra O K] {Δ : K} (hΔ : Δ ≠ 0)
    {χ : Kˣ →* ℂˣ} {S : SigData Δ} (h : SigOk O χ S) {t : Kˣ} (ht : t ∈ S.P) {τ : K} (hτ : τ ^ 2 - 4 ≠ 0)
    (hI : Ind S.H τ t) {γ : DX Δ} (hγ : HasTr γ τ) : ∃ g : DX Δ, HasTr g τ ∧ S.fS t g ≠ 0 := by
  obtain ⟨⟨j, hj⟩, -, -⟩ := embAlg K Δ τ hΔ hτ γ hγ
  have h2 : 2 + τ ≠ 0 := fun e => hτ (by linear_combination (τ - 2) * e)
  have hn : QuadraticAlgebra.norm (1 + QuadraticAlgebra.omega : Etau K τ) ≠ 0 := by
    have : QuadraticAlgebra.norm (1 + QuadraticAlgebra.omega : Etau K τ) = 2 + τ := by
      simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      ring
    rwa [this]
  obtain ⟨z, hz⟩ : IsUnit (1 + QuadraticAlgebra.omega : Etau K τ) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (isUnit_iff_ne_zero.2 hn)
  have ho := (h.D_orb t ht τ γ j hτ hγ hj z hz).2.2.1
  have hc : ((S.cS : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h.cS.ne'
  have h1 : Glob.one (Ind S.H τ t) = 1 := if_pos hI
  rw [h1, mul_one] at ho
  by_contra hne
  push_neg at hne
  apply hc
  rw [← ho]
  unfold orb wcount
  apply finsum_eq_zero_of_forall_eq_zero
  intro o
  exact mul_eq_zero_of_right _ (hne _ (conj_tr hγ (Quotient.out (Quotient.out o))))

private theorem common_den (O : Type) {K : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    {Δ : K} {T : Set (Lsq K Δ)} (hT : T.Finite) : ∃ N : O, N ≠ 0 ∧ ∀ e ∈ T, IsIntegral O (N • e) := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨N, hN, h⟩ := ih
    have ha : IsAlgebraic O a := (IsFractionRing.isAlgebraic_iff O K _).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨y, hy, hi⟩ := ha.exists_integral_multiple
    refine ⟨N * y, mul_ne_zero hN hy, ?_⟩
    rintro e (rfl | he)
    · rw [mul_smul]
      exact hi.smul N
    · rw [mul_comm, mul_smul]
      exact (h e he).smul y

private theorem den_bound (O : Type) {K : Type} [Field K] [CharZero K] [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] {Δ : K} (hΔ : Δ ≠ 0) {χ : Kˣ →* ℂˣ} {S : SigData Δ} (h : SigOk O χ S) {t : Kˣ} (ht : t ∈ S.P) :
    ∃ N : O, N ≠ 0 ∧ ∀ τ : K, τ ^ 2 - 4 ≠ 0 → Ind S.H τ t → (∃ γ : DX Δ, HasTr γ τ) →
      IsIntegral O (algebraMap O K N * τ) := by
  let T : Set (Lsq K Δ) := ⋃ x ∈ {x : SU Δ ⧸ S.J2.subgroupOf (SU Δ) | S.fS t x.out ≠ 0},
    Set.range fun p : Fin 2 × Fin 2 => mt (x.out : DX Δ) p.1 p.2
  have hT : T.Finite := (h.S_fin t ht).biUnion fun _ _ => Set.finite_range _
  obtain ⟨N, hN, hi⟩ := common_den O hT
  refine ⟨N, hN, fun τ hτ hI ⟨γ, hγ⟩ => ?_⟩
  obtain ⟨g, hg, hf⟩ := supp_el O hΔ h ht hτ hI hγ
  have hgS : g ∈ SU Δ := by
    change GeneralLinearGroup.det (g : GL (Fin 2) (Lsq K Δ)) = 1
    exact Units.ext hg.1
  let g' : SU Δ := ⟨g, hgS⟩
  let q : SU Δ ⧸ S.J2.subgroupOf (SU Δ) := QuotientGroup.mk g'
  obtain ⟨u, hu⟩ : ∃ u : S.J2.subgroupOf (SU Δ), q.out = g' * u := QuotientGroup.mk_out_eq_mul _ g'
  have hu2 : ((u : SU Δ) : DX Δ) ∈ S.J2 := u.2
  have hfx : S.fS t (q.out : DX Δ) ≠ 0 := by
    rw [hu]
    change S.fS t (g * ((u : SU Δ) : DX Δ)) ≠ 0
    rw [((h.S_inv t ht _ hu2 g).2)]
    exact hf
  have he : g = (q.out : DX Δ) * (((u : SU Δ) : DX Δ))⁻¹ := by
    rw [hu]
    change g = g * ((u : SU Δ) : DX Δ) * (((u : SU Δ) : DX Δ))⁻¹
    group
  obtain ⟨w, hw⟩ := h.levelTwoLeIntegral (S.J2.inv_mem hu2)
  have hw' : ∀ i j, IsIntegral O (mt (((u : SU Δ) : DX Δ))⁻¹ i j) := fun i j => by
    have : mt (((u : SU Δ) : DX Δ))⁻¹ i j = (w.1 i j : Lsq K Δ) := by
      exact (congrArg (fun M : GL (Fin 2) (Lsq K Δ) => (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j) hw).symm
    rw [this]
    exact (w.1 i j).2
  have hx : ∀ i j, IsIntegral O (N • mt (q.out : DX Δ) i j) := fun i j => by
    refine hi _ (Set.mem_biUnion (x := q) hfx ⟨(i, j), rfl⟩)
  have hm : mt g = mt (q.out : DX Δ) * mt (((u : SU Δ) : DX Δ))⁻¹ := by
    rw [he]; rfl
  have htr : N • (algebraMap K (Lsq K Δ) τ) =
      ∑ i, ∑ j, (N • mt (q.out : DX Δ) i j) * mt (((u : SU Δ) : DX Δ))⁻¹ j i := by
    rw [← hg.2, hm, Matrix.trace, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc]
  have hint : IsIntegral O (N • (algebraMap K (Lsq K Δ) τ)) := by
    rw [htr]
    exact IsIntegral.sum _ fun i _ => IsIntegral.sum _ fun j _ => (hx i j).mul (hw' j i)
  have e : N • (algebraMap K (Lsq K Δ) τ) = algebraMap K (Lsq K Δ) (algebraMap O K N * τ) := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  rw [e] at hint
  exact (isIntegral_algebraMap_iff (algebraMap K (Lsq K Δ)).injective).1 hint

private theorem val_small {F : Type} [Field F] [NumberField F] (v : Pl F) {x : Kv v} (hx : x ≠ 0) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ Valued.v (cv v (algebraMap (𝓞 F) F a)) ≤ Valued.v x := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := fun e => by
    rw [e, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hc : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = Valued.v x := ⟨_, WithZero.exp_log hc⟩
  refine ⟨π ^ (-m).toNat, pow_ne_zero _ hπ0, ?_⟩
  have e1 : Valued.v (cv v (algebraMap (𝓞 F) F π)) = WithZero.exp (-1 : ℤ) := by
    rw [← hπ, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [map_pow, map_pow, map_pow, e1, ← WithZero.exp_nsmul, ← hm, WithZero.exp_le_exp, nsmul_eq_mul]
  omega

theorem UpperTheory.V.Z.Sym.Glob.finSupp :
    ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ t, D.Cone t →
    {τ : F | D.Good t τ ∧ ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range}.Finite := by
  classical
  intro F _ _ Δ D hD t ht
  have := hD.real
  obtain ⟨σ₀⟩ : Nonempty (F →+* ℝ) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩
  have h0 : Δ ≠ 0 := fun h => by simpa [h] using hD.neg σ₀
  have hval : ∀ (v : Pl F) (x : F), v.valuation F x = Valued.v (cv v x) := fun v x =>
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).symm
  have hloc : ∀ v ∈ D.Sg, ∃ a : 𝓞 F, a ≠ 0 ∧ ∀ τ : F, D.Good t τ →
      Valued.v (cv v (algebraMap (𝓞 F) F a * τ)) ≤ 1 := by
    intro v hv
    have : CharZero (Kv v) := charZero_of_injective_algebraMap (cv v).injective
    obtain ⟨N, hN, hb⟩ := den_bound (Ov v) ((map_ne_zero _).2 h0) (hD.sig v hv) (ht v hv)
    have hN' : algebraMap (Ov v) (Kv v) N ≠ 0 := fun e => hN (by
      simpa using (IsFractionRing.injective (Ov v) (Kv v)) (e.trans (map_zero _).symm))
    obtain ⟨a, ha, hle⟩ := val_small v hN'
    refine ⟨a, ha, fun τ hg => ?_⟩
    have hτ0 : τ ^ 2 - 4 ≠ 0 := fun e => by
      have h1 := hg.1 σ₀
      rw [e, map_zero] at h1
      exact lt_irrefl _ h1
    obtain ⟨γ, hγ⟩ := (embEx F Δ D hD τ).1 hg.1
    obtain ⟨γ', hγ'⟩ := tr_map (cv v) γ hγ
    have hτv : cv v τ ^ 2 - 4 ≠ 0 := fun e => hτ0 ((cv v).injective (by
      rw [map_sub, map_pow, map_zero, map_ofNat]
      exact e))
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hb (cv v τ) hτv (hg.2 v hv) ⟨γ', hγ'⟩)
    have h1 : Valued.v (algebraMap (Ov v) (Kv v) N * cv v τ) ≤ 1 := by
      rw [← hy]
      exact y.2
    rw [map_mul, map_mul]
    rw [map_mul] at h1
    exact (mul_le_mul_left hle _).trans h1
  choose! a ha hb using hloc
  let A : 𝓞 F := ∏ v ∈ D.Sg, a v
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.2 ha
  have hAF : algebraMap (𝓞 F) F A ≠ 0 := fun e => hA (by
    simpa using (RingOfIntegers.coe_injective (K := F)) (e.trans (map_zero _).symm))
  have hle : ∀ (v : Pl F) (b : 𝓞 F), Valued.v (cv v (algebraMap (𝓞 F) F b)) ≤ 1 := fun v b => by
    rw [← hval]
    exact v.valuation_le_one b
  have hint : ∀ τ : F, (D.Good t τ ∧ ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) →
      algebraMap (𝓞 F) F A * τ ∈ (algebraMap (𝓞 F) F).range := fun τ ⟨hg, hoff⟩ => by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v => ?_
    rw [hval]
    by_cases hv : v ∈ D.Sg
    · have e : A = (∏ w ∈ D.Sg.erase v, a w) * a v := (Finset.prod_erase_mul _ _ hv).symm
      rw [e, map_mul (algebraMap (𝓞 F) F), mul_assoc, map_mul (cv v), map_mul Valued.v]
      exact mul_le_one' (hle v _) (hb v hv τ hg)
    · obtain ⟨y, hy⟩ := hoff v hv
      rw [map_mul, map_mul, ← hy]
      exact mul_le_one' (hle v _) y.2
  let B : ℝ := ∑ φ : F →+* ℂ, ‖φ (algebraMap (𝓞 F) F A)‖ * 2
  have hfin := Embeddings.finite_of_norm_le F ℂ B
  refine (hfin.preimage (f := fun x => algebraMap (𝓞 F) F A * x)
    (fun x _ y _ e => mul_left_cancel₀ hAF e)).subset fun τ hτ => ?_
  refine ⟨?_, fun φ => ?_⟩
  · obtain ⟨y, hy⟩ := hint τ hτ
    change IsIntegral ℤ (algebraMap (𝓞 F) F A * τ)
    rw [← hy]
    exact RingOfIntegers.isIntegral_coe y
  · have hr : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
    have h1 := hτ.1.1 hr.embedding
    simp only [map_sub, map_pow, map_ofNat] at h1
    have h2 : |hr.embedding τ| ≤ 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    have h3 : ‖φ τ‖ ≤ 2 := by
      rw [← hr.coe_embedding_apply, Complex.norm_real]
      exact h2
    change ‖φ (algebraMap (𝓞 F) F A * τ)‖ ≤ B
    rw [map_mul, norm_mul]
    calc _ ≤ ‖φ (algebraMap (𝓞 F) F A)‖ * 2 := by gcongr
      _ ≤ B := Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ (algebraMap (𝓞 F) F A)‖ * 2)
        (fun _ _ => by positivity) (Finset.mem_univ φ)
