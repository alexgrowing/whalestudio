import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhere
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Formalism.LocalToGlobal.UnitaryNorms.CharProd
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomOr

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd

private theorem expo_le {I : Type} [Fintype I] (c : I → ℝ) (hc : Function.Injective c) (m : I → ℤ) (Z : Set ℝ) (hZ : Z.Infinite)
    (h0 : ∀ z ∈ Z, ∀ i, z + c i ≠ 0) (h1 : ∀ z ∈ Z, ∏ i, (z + c i) ^ m i = 1) (j : I) : m j ≤ 0 := by
  have hPQ : (∏ i, (X + C (c i)) ^ (m i).toNat : ℝ[X]) = ∏ i, (X + C (c i)) ^ (-m i).toNat := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ (hZ.mono fun z hz => ?_)
    simp only [Set.mem_setOf_eq, eval_prod, eval_pow, eval_add, eval_X, eval_C]
    rw [← one_mul (∏ i, _ ^ (-m i).toNat), ← h1 z hz, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (h0 z hz i)]
    congr 1
    omega
  by_contra hj
  have e := congrArg (Polynomial.eval (-c j)) hPQ
  simp only [eval_prod, eval_pow, eval_add, eval_X, eval_C] at e
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [neg_add_cancel]; exact zero_pow (by omega))] at e
  refine Finset.prod_ne_zero_iff.2 (fun i _ => ?_) e.symm
  by_cases hi : i = j
  · rw [hi, show (-m j).toNat = 0 by omega, pow_zero]; exact one_ne_zero
  · exact pow_ne_zero _ fun e' => hi (hc (by linear_combination e'))

private theorem expo_zero {I : Type} [Fintype I] (c : I → ℝ) (hc : Function.Injective c) (m : I → ℤ) (Z : Set ℝ) (hZ : Z.Infinite)
    (h0 : ∀ z ∈ Z, ∀ i, z + c i ≠ 0) (h1 : ∀ z ∈ Z, ∏ i, (z + c i) ^ m i = 1) : m = 0 := by
  funext j
  have a := expo_le c hc m Z hZ h0 h1 j
  have b := expo_le c hc (-m) Z hZ h0 (fun z hz => by
    simp only [Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib, h1 z hz, inv_one]) j
  simp only [Pi.neg_apply, Pi.zero_apply] at b ⊢
  omega

private theorem norm_inf {F : Type} [Field F] [NumberField F] (χ : HChar F) (k : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 ∨ ordF v k = 0) : ‖((χ.inf k : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt F χ
  have e := (χ ^ N).val_principal ∅ (fun v _ => hu v) k
  have h1 : ‖((∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ (∅ : Finset _)), (χ ^ N).val v ^ ordF v k : ℂˣ) : ℂ)‖ = 1 := by
    refine finprod_induction (fun z : ℂˣ => ‖(z : ℂ)‖ = 1) (by simp) (fun x y hx hy => by simp [hx, hy]) fun v => ?_
    have e2 : (χ ^ N).val v = χ.val v ^ N := rfl
    rcases h v with h | h
    · simp [e2, h]
    · simp [h]
  have e2 : (χ ^ N).inf k = χ.inf k ^ N := rfl
  rw [e, Finset.prod_empty, mul_one, e2] at h1
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_inv, norm_pow, inv_eq_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1

private theorem type_zero {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (a : (F →+* ℂ) → ℤ)
    (ha : IsAlgPos χ a) (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ‖((χ.val v : ℂˣ) : ℂ)‖ = 1) : a = 0 := by
  have hS := Filter.eventually_cofinite.1 h
  let M : ℕ := ∏ v ∈ hS.toFinset, Ideal.absNorm v.asIdeal
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have hMv : ∀ v : HeightOneSpectrum (𝓞 F), ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 ∨ ((M : ℕ) : 𝓞 F) ∈ v.asIdeal := fun v => by
    by_cases hv : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1
    · exact Or.inl hv
    · obtain ⟨d, hd⟩ : Ideal.absNorm v.asIdeal ∣ M := Finset.dvd_prod_of_mem _ (hS.mem_toFinset.2 hv)
      rw [hd, Nat.cast_mul]
      exact Or.inr (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))
  obtain ⟨x₀, hx₀⟩ := Field.exists_primitive_element ℚ F
  obtain ⟨x, d, hd, hx⟩ : ∃ (x : 𝓞 F) (d : ℤ), d ≠ 0 ∧ (x : F) = d * x₀ := by
    obtain ⟨d, hd, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x₀)).exists_integral_multiple
    exact ⟨⟨d • x₀, hi⟩, d, hd, by simp⟩
  have hre : ∀ (φ : F →+* ℂ) (y : F), ((φ y).re : ℂ) = φ y := fun φ y =>
    Complex.conj_eq_iff_re.1 (RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal φ) y)
  let c : (F →+* ℂ) → ℝ := fun φ => M * (φ (x : F)).re
  have hc : Function.Injective c := fun φ φ' e => by
    have e1 : (φ (x : F)).re = (φ' (x : F)).re := mul_left_cancel₀ (by exact_mod_cast hM) e
    have e2 : φ (x : F) = φ' (x : F) := by rw [← hre φ, e1, hre]
    simp only [hx, map_mul, map_intCast] at e2
    have e3 := mul_left_cancel₀ (by exact_mod_cast hd) e2
    have := (Field.primitive_element_iff_algHom_eq_of_eval' ℚ ℂ (fun _ => IsAlgClosed.splits _) x₀).1 hx₀
      (a₁ := φ.toRatAlgHom) (a₂ := φ'.toRatAlgHom) e3
    exact RingHom.ext fun y => DFunLike.congr_fun this y
  obtain ⟨T, hT⟩ := exists_nat_gt (∑ φ : F →+* ℂ, |(φ (x : F)).re|)
  have hpos : ∀ (t : ℕ) (φ : F →+* ℂ), 0 < (1 + M * ((T + t : ℕ) : ℝ)) + c φ := fun t φ => by
    have h1 := (Finset.single_le_sum (f := fun φ : F →+* ℂ => |(φ (x : F)).re|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ φ)).trans_lt hT
    have h2 : (0 : ℝ) ≤ ((T + t : ℕ) : ℝ) + (φ (x : F)).re := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) t, neg_abs_le (φ (x : F)).re]
    have h3 := mul_nonneg (Nat.cast_nonneg (α := ℝ) M) h2
    simp only [c]
    linarith
  refine expo_zero c hc a (Set.range fun t : ℕ => 1 + M * ((T + t : ℕ) : ℝ)) (Set.infinite_range_of_injective fun s t e => ?_) ?_ ?_
  · simpa [hM] using e
  · rintro _ ⟨t, rfl⟩ φ
    exact (hpos t φ).ne'
  rintro _ ⟨t, rfl⟩
  let y : 𝓞 F := 1 + (M : 𝓞 F) * (((T + t : ℕ) : 𝓞 F) + x)
  have hy : ∀ φ : F →+* ℂ, φ (y : F) = (((1 + M * ((T + t : ℕ) : ℝ)) + c φ : ℝ) : ℂ) := fun φ => by
    simp only [y, c]
    push_cast
    simp only [hre, map_add, map_mul, map_one, map_natCast]
    ring
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hy0 : (y : F) ≠ 0 := fun e => (hpos t w.embedding).ne' (by
    have := hy w.embedding
    rw [e, map_zero] at this
    exact_mod_cast this.symm)
  have h1 := ha (Units.mk0 _ hy0) fun φ => by
    have := hy (Complex.ofRealHom.comp φ)
    simp only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_inj] at this
    rw [Units.val_mk0, this]
    exact hpos t _
  have h2 := norm_inf χ (Units.mk0 _ hy0) fun v => (hMv v).imp id fun hv => by
    have : y ∉ v.asIdeal := fun hy => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
      simpa [y] using v.asIdeal.sub_mem hy (Ideal.mul_mem_right (((T + t : ℕ) : 𝓞 F) + x) _ hv)))
    have e : v.valuation F (y : F) = 1 := (v.valuation_eq_one_iff_notMem).2 this
    simp [ordF, e]
  rw [h1, norm_prod] at h2
  refine Eq.trans (Finset.prod_congr rfl fun φ _ => ?_) h2
  rw [norm_zpow, Units.val_mk0, hy, Complex.norm_real, Real.norm_of_nonneg (hpos t φ).le]

private theorem hom_or {Γ C : Type} [Group Γ] [CommGroup C] (I : Subgroup Γ) (f g h : Γ →* C)
    (H : ∀ s ∈ I, f s = g s ∨ f s = h s) : (∀ s ∈ I, f s = g s) ∨ ∀ s ∈ I, f s = h s :=
  _root_.UpperTheory.Reformulated.B.Qk44.hom_or I f g h H

private theorem chars_of_red {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : Type} [NormedField k] (r : Γ →* GL (Fin 2) k)
    (hc : Continuous r) (h : ¬ IsIrr r) : ∃ c d : Γ →* kˣ, Continuous c ∧ Continuous d ∧
      ∀ s, (r s : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (c s : k)) * (X - C (d s : k)) := by
  simp only [IsIrr, IsIrrSub, not_and, not_forall] at h
  obtain ⟨W, -, hW, hne⟩ := h top_ne_bot (fun _ _ _ => Submodule.mem_top)
  rw [not_or] at hne
  have h2 : Module.finrank k W < 2 := by simpa using Submodule.finrank_lt hne.2
  have h0 : Module.finrank k W ≠ 0 := fun h => hne.1 (Submodule.finrank_eq_zero.mp h)
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.mp (show Module.finrank k W = 1 by omega)
  have hv0 : (v : Fin 2 → k) ≠ 0 := fun h => hv (Subtype.ext h)
  choose c₀ hc₀ using fun g => hall ⟨_, hW g v v.2⟩
  have hc1 : ∀ g, (r g : Matrix (Fin 2) (Fin 2) k) *ᵥ (v : Fin 2 → k) = c₀ g • (v : Fin 2 → k) := fun g =>
    (congrArg Subtype.val (hc₀ g)).symm
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  let c₁ : Γ →* k :=
    { toFun := c₀
      map_one' := smul_left_injective k hv0 (by simpa using (hc1 1).symm)
      map_mul' := fun s t => smul_left_injective k hv0 (by
        simp only
        rw [← hc1, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hc1, Matrix.mulVec_smul, hc1, smul_smul, mul_comm]) }
  have hcc : Continuous c₁.toHomUnits := by
    refine Units.isEmbedding_val₀.continuous_iff.2 ?_
    have : Continuous fun g => ((r g : Matrix (Fin 2) (Fin 2) k) *ᵥ (v : Fin 2 → k)) i / (v : Fin 2 → k) i :=
      ((continuous_apply i).comp ((Units.continuous_val.comp hc).matrix_mulVec continuous_const)).div_const _
    refine this.congr fun g => ?_
    rw [hc1, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hi]
    rfl
  have hdet : Continuous (Matrix.GeneralLinearGroup.det.comp r : Γ →* kˣ) :=
    Units.isEmbedding_val₀.continuous_iff.2 (Units.continuous_val.comp hc).matrix_det
  refine ⟨c₁.toHomUnits, Matrix.GeneralLinearGroup.det.comp r / c₁.toHomUnits, hcc, hdet.div' hcc, fun s => ?_⟩
  have n0 : c₀ s ≠ 0 := (c₁.toHomUnits s).ne_zero
  have e1 : ((c₁.toHomUnits s : kˣ) : k) = c₀ s := rfl
  have e2 : (((Matrix.GeneralLinearGroup.det.comp r / c₁.toHomUnits) s : kˣ) : k) =
      (r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s := by
    rw [MonoidHom.div_apply, Units.val_div_eq_div_val, e1]; rfl
  have a0 := congrFun (hc1 s) 0
  have a1 := congrFun (hc1 s) 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at a0 a1
  have q : c₀ s ^ 2 - (r s : Matrix (Fin 2) (Fin 2) k).trace * c₀ s + (r s : Matrix (Fin 2) (Fin 2) k).det = 0 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    refine mul_right_cancel₀ hi ?_
    fin_cases i
    · simp only [Fin.zero_eta, Pi.zero_apply, mul_zero]
      linear_combination (r s 1 1 - c₀ s) * a0 - r s 0 1 * a1
    · simp only [Fin.mk_one, Pi.zero_apply, mul_zero]
      linear_combination (r s 0 0 - c₀ s) * a1 - r s 1 0 * a0
  have t : (r s : Matrix (Fin 2) (Fin 2) k).trace = c₀ s + (r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s := by
    field_simp
    linear_combination -q
  have u : (r s : Matrix (Fin 2) (Fin 2) k).det = c₀ s * ((r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s) := by
    field_simp
  rw [e1, e2, Matrix.charpoly_fin_two, t]
  conv_lhs => rw [u]
  rw [← u, map_add]
  conv_lhs => enter [2]; rw [u, map_mul]
  ring

private theorem charpoly_tri {K : Type} [Field K] (g r : GL (Fin 2) K)
    (h : ∀ i j, j < i → (g * r * g⁻¹ : GL (Fin 2) K) i j = 0) :
    (r : Matrix (Fin 2) (Fin 2) K).charpoly =
      (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 0 0)) * (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 1 1)) := by
  have e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj g _
  rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem cyc_ine {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Ine (F := ℚ) A := (Ine (F := ℚ) A).pow_mem hσ N
  have hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N) := rfl
  have hinj : Function.Injective
      (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  refine ⟨g, hD, fun h => hu (N * n) (mul_ne_zero (by exact_mod_cast hN.ne') hn) (hinj ?_)⟩
  rw [map_one, ← h, cycBar, MonoidHom.comp_apply, hc, map_pow, hσu, zpow_mul, zpow_natCast, map_zpow]

private theorem inv_mem_eig {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (x : WD h) (φ : Weil h) {b : ℂ}
    (hb : (x.charPol φ⁻¹).IsRoot b) : b ≠ 0 ∧ b⁻¹ ∈ x.eig φ := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.charPol_mk, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hb
  obtain ⟨v, hv⟩ := hb.exists_hasEigenvector
  have h1 : v = b • a.ρ φ v := by
    rw [← map_smul, ← hv.apply_eq_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hv.2 (by simpa using h1)
  refine ⟨hb0, ?_⟩
  rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 ?_, hv.2⟩
  conv_rhs => rw [h1]
  rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]

private theorem norm_of_pure {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (hu : ∀ s ∈ Ine (F := F) A, r s = 1) {x : WD h} (hx : IsWDOf ι r x) {s : ℝ} (ht : (x.lpTw s).tempered) {b : Qbar l}
    (hb : (r (frob h : G F Ω)⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot b) : ‖ι b‖ = (normV w : ℝ) ^ s := by
  have e := hx.wdOf_eq hl
  obtain ⟨t, ht', φ, hφ, N, a, hN, -, -⟩ := id hx
  have hxu : x.unr := e ▸ (hN.unr_wdOf_iff hl ht' ι).2 hu
  have hc := hN.charPol_wdOf (h := h) hl ht' ι (frob h)⁻¹
  rw [e] at hc
  have hr : (x.charPol (frob h)⁻¹).IsRoot (ι b) := by
    rw [hc]
    exact hb.map (f := ι.toRingHom)
  obtain ⟨hb0, hm⟩ := inv_mem_eig x _ hr
  have h1 := (WD.tempered_unr _ ((WD.unr_tw x s).2 hxu)).1 ht ((ι b)⁻¹ * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (by
    rw [WD.frobEig_tw x s hxu]
    exact Multiset.mem_map_of_mem _ hm)
  rw [norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (GlobalTheory.WeilDeligne.one_lt_normV w)), Complex.ofReal_re,
    inv_mul_eq_one₀ (norm_ne_zero_iff.2 hb0)] at h1
  exact h1

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.ordIrr :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Sd.OrdIrr := by
  intro P F Ω _ _ _ _ _ _ l _ hl2 hs ι ξ s c m a π r hr
  by_contra hirr
  obtain ⟨c₁, c₂, hc₁, hc₂, hch⟩ := chars_of_red r hr.cont hirr

  have hI : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w →
      ∃ d : ℤ, d ≠ 0 ∧ ∀ g ∈ Ine (F := F) A, (c₁ / c₂) g = cycBar F Ω l g ^ d := by
    intro w hw A hA
    obtain ⟨κ, ⟨g, hg⟩, hκ, -⟩ := ordAbove P F Ω l hl2 hs ι ξ s c m a π r hr w hw A hA
    have hm := (hr.above w hw).2.1
    have key : ∀ t ∈ Ine (F := F) A, (X - C (c₁ t : Qbar l)) * (X - C (c₂ t : Qbar l)) =
        (X - C ((cycBar F Ω l t ^ m w 0 : (Qbar l)ˣ) : Qbar l)) * (X - C ((cycBar F Ω l t ^ m w 1 : (Qbar l)ˣ) : Qbar l)) := by
      intro t ht
      let t' : ↥(Dec (F := F) A) := ⟨t, Ine_le_Dec A ht⟩
      rw [← hch, charpoly_tri g _ (hg t').1, (hg t').2 0, (hg t').2 1, hκ 0 t' ht, hκ 1 t' ht]
    have hp : ∀ t ∈ Ine (F := F) A, c₁ t * c₂ t = cycBar F Ω l t ^ m w 0 * cycBar F Ω l t ^ m w 1 := fun t ht => by
      have := congrArg (eval 0) (key t ht)
      simp only [eval_mul, eval_sub, eval_X, eval_C, zero_sub, neg_mul_neg] at this
      exact Units.ext this
    rcases hom_or (Ine (F := F) A) c₁ (cycBar F Ω l ^ m w 0) (cycBar F Ω l ^ m w 1) (fun t ht => by
      have := congrArg (eval (c₁ t : Qbar l)) (key t ht)
      simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at this
      exact (mul_eq_zero.1 this.symm).imp (fun e => Units.ext (sub_eq_zero.1 e)) fun e => Units.ext (sub_eq_zero.1 e)) with h | h
    · refine ⟨m w 0 - m w 1, by omega, fun t ht => ?_⟩
      have h1 := hp t ht
      rw [h t ht, MonoidHom.zpow_apply, mul_right_inj] at h1
      rw [MonoidHom.div_apply, h t ht, h1, MonoidHom.zpow_apply, zpow_sub, div_eq_mul_inv]
    · refine ⟨m w 1 - m w 0, by omega, fun t ht => ?_⟩
      have h1 := hp t ht
      rw [h t ht, MonoidHom.zpow_apply, mul_comm (_ ^ m w 0), mul_right_inj] at h1
      rw [MonoidHom.div_apply, h t ht, h1, MonoidHom.zpow_apply, zpow_sub, div_eq_mul_inv]
  obtain ⟨χ, -, art, n, hart, hn, hL⟩ := (algOfCyc P F Ω l ι).1 (c₁ / c₂) (hc₁.div' hc₂) fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨d, -, hd⟩ := hI w hw A hA
    exact ⟨A, hA, d, 1, one_pos, fun t ht => by rw [hd t ht, zpow_neg, mul_inv_cancel, one_pow]⟩
  obtain ⟨χ₀, hχ₀⟩ := hr.pol
  obtain ⟨-, wt, HT, -, -, hG⟩ := exR P F Ω l ι 2 one_le_two π χ₀ hr.reg hχ₀
  have hG := hG r hr.cont hr.att
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  obtain rfl : n = 0 := type_zero χ n hn (by
    filter_upwards [hl, hr.att.2, (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1] with w hw ⟨B, _, hF⟩ hu
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨x, hx, ht⟩ := hG.pure w hw A hA
    have e1 := norm_of_pure hw (hF A hA).1 hx ht (b := c₁ (frob hA : G F Ω)⁻¹) (by rw [hch]; simp)
    have e2 := norm_of_pure hw (hF A hA).1 hx ht (b := c₂ (frob hA : G F Ω)⁻¹) (by rw [hch]; simp)
    have e3 := hL.frob_unr hart (Or.inl hw) hu hA (isFrob_frob (h := hA))
    have e4 : ((χ.val w : ℂˣ) : ℂ) = ι (c₁ (frob hA : G F Ω)⁻¹) / ι (c₂ (frob hA : G F Ω)⁻¹) := by
      rw [← map_div₀, ← Units.val_div_eq_div_val, ← MonoidHom.div_apply, map_inv, Units.val_inv_eq_inv_val, e3, inv_inv,
        RingEquiv.apply_symm_apply]
    rw [e4, norm_div, e2.trans e1.symm, div_self]
    simp)
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
    have hne : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ ⊤ := fun e => by
      have := congrArg Ideal.absNorm e
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, pow_eq_one_iff] at this
      rcases this with h | h
      · exact (Fact.out : l.Prime).ne_one h
      · exact Module.finrank_pos.ne' h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ⟨⟨M, hM.isPrime, fun e => h0 (le_bot_iff.1 (e ▸ hle))⟩, hle (Ideal.mem_span_singleton_self _)⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨d, hd0, hd⟩ := hI w hw A hA
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt F χ
  obtain ⟨g, hg, hne⟩ := cyc_ine hw hA (n := d * N) (mul_ne_zero hd0 (by exact_mod_cast hN.ne'))
  obtain ⟨x, hx, e⟩ := (hL.ine_image hart (Or.inr rfl) hA _).1 ⟨g, hg, rfl⟩
  have e2 : χ.loc w x ^ N = 1 := hu w x hx
  refine hne (Units.ext ?_)
  rw [zpow_mul, zpow_natCast, ← hd g hg, Units.val_pow_eq_pow_val, ← e, ← map_pow, ← Units.val_pow_eq_pow_val, e2]
  simp
