import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero

noncomputable section

namespace GlobalTheory.SWQ.Model

open scoped TensorProduct NNReal ENNReal Pointwise
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem null_of_finite_curve {V K : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (ρ : Measure K) [SFinite ρ] [NullSingletonClass ρ] (hρ : ρ Set.univ ≠ 0)
    (μ : Measure V) [μ.IsAddHaarMeasure] {Z : Set V} (hZ : MeasurableSet Z)
    {L : K → V} (hL : Continuous L) (h : ∀ x : V, {t : K | x + L t ∈ Z}.Finite) : μ Z = 0 := by
  have hc : Continuous (fun p : V × K => p.1 + L p.2) := by fun_prop
  have hS : MeasurableSet {p : V × K | p.1 + L p.2 ∈ Z} := hc.measurable hZ
  have h1 : (μ.prod ρ) {p : V × K | p.1 + L p.2 ∈ Z} = 0 := by
    rw [Measure.measure_prod_null hS]
    exact Filter.Eventually.of_forall fun x => (h x).measure_zero ρ
  rw [Measure.prod_apply_symm hS] at h1
  have h2 : ∀ t : K, μ ((fun x => (x, t)) ⁻¹' {p : V × K | p.1 + L p.2 ∈ Z}) = μ Z :=
    fun t => measure_preimage_add_right μ (L t) Z
  simpa only [h2, lintegral_const, mul_eq_zero, hρ, or_false] using h1

section Alg
variable (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F)

omit [NumberField F] in
theorem qd_smul (c : R) (x : Fin N → R) : qd R a (c • x) = c ^ 2 * qd R a x := by
  simp only [qd, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

omit [NumberField F] in
theorem qd_add (x y : Fin N → R) : qd R a (x + y) = qd R a x + qd R a y + Bd R a x y := by
  simp only [qd, Bd, Pi.add_apply, ← Finset.sum_add_distrib, map_mul, map_ofNat]
  exact Finset.sum_congr rfl fun l _ => by ring

omit [NumberField F] in
theorem Bd_symm (x y : Fin N → R) : Bd R a x y = Bd R a y x :=
  Finset.sum_congr rfl fun l _ => by ring

omit [NumberField F] in
theorem Bd_add (x x' y : Fin N → R) : Bd R a (x + x') y = Bd R a x y + Bd R a x' y := by
  simp only [Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

omit [NumberField F] in
theorem Bd_smul (c : R) (x y : Fin N → R) : Bd R a (c • x) y = c * Bd R a x y := by
  simp only [Bd, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

omit [NumberField F] in
theorem Bd_single (x : Fin N → R) (l : Fin N) (t : R) :
    Bd R a x (Pi.single l t) = algebraMap F R (2 * a l) * x l * t := by
  rw [Bd, Finset.sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
  simp

omit [NumberField F] in
theorem qd_single (l : Fin N) (t : R) : qd R a (Pi.single l t) = algebraMap F R (a l) * t ^ 2 := by
  rw [qd, Finset.sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem Bd_nondeg (ha : ∀ l, a l ≠ 0) (x : Fin N → R) (h : ∀ y, Bd R a x y = 0) : x = 0 := by
  funext l
  have h1 := h (Pi.single l 1)
  rw [Bd_single, mul_one] at h1
  have hu : IsUnit (algebraMap F R (2 * a l)) :=
    (IsUnit.mk0 _ (mul_ne_zero two_ne_zero (ha l))).map _
  exact (hu.mul_right_eq_zero).1 h1

omit [NumberField F] in
theorem continuous_qd [TopologicalSpace R] [IsTopologicalRing R] : Continuous (qd R a) := by
  unfold qd; fun_prop

omit [NumberField F] in
theorem continuous_Bd [TopologicalSpace R] [IsTopologicalRing R] (y : Fin N → R) :
    Continuous fun x => Bd R a x y := by
  unfold Bd; fun_prop

def bil : LinearMap.BilinForm R (Fin N → R) :=
  LinearMap.mk₂ R (Bd R a) (Bd_add R a) (Bd_smul R a)
    (fun x y y' => by rw [Bd_symm, Bd_add, Bd_symm R a y, Bd_symm R a y'])
    (fun c x y => by rw [Bd_symm, Bd_smul, Bd_symm R a y, smul_eq_mul])

end Alg

theorem exists_fin (ψ : AddChar (AF F) ℂ) [IsTotallyReal F] (hψ : IsCharAF F ψ) (a : Fin N → F)
    (ha : ∀ l, a l ≠ 0) (hN : 0 < N) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (μ : Measure (Fin N → Fv F v)) (ν : Measure (Fv F v)) (f : Fv F v → Measure (Fin N → Fv F v)),
      SelfDual μ (fun x y => psiV F ψ v (Bd (Fv F v) a x y)) ∧ SdR (Fv F v) (psiV F ψ v) ν ∧
      IsFibreFamily μ (qd (Fv F v) a) id Set.univ ν {c | c ≠ 0} f := by
  let χ : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)
  have hc : Continuous χ :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖χ t‖ = 1 := fun t => hψ.2.1 _
  have hne : ∃ t, χ t ≠ 1 := (CharLoc.char_local F ψ hψ).1 v
  obtain ⟨ν, hν, -⟩ := GlobalTheory.SelfDualFinite.existsUnique_of_bilin v χ hc hu hne (Fv F v) (LinearMap.mul _ _)
    (fun x y => mul_comm x y) (fun x hx => by simpa using hx 1)
  obtain ⟨μ, hμ, -⟩ := GlobalTheory.SelfDualFinite.existsUnique_of_bilin v χ hc hu hne (Fin N → Fv F v)
    (bil (Fv F v) a) (Bd_symm _ a) (Bd_nondeg _ a ha)
  haveI := hμ.1
  haveI := hν.1
  have e : {c : Fv F v | c ≠ 0} = {c | IsUnit c} := by ext c; exact isUnit_iff_ne_zero.symm
  obtain ⟨f, hf⟩ := FibExist.exists_fibreFamily ((nice_ainf_fv F).2 v) μ ν (qd (Fv F v) a)
    (continuous_qd _ a) (qd_smul _ a) (by
      simp only [isUnit_iff_ne_zero]
      rw [ae_iff]
      simp only [ne_eq, not_not]
      letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField _ _
      haveI : NullSingletonClass ν := inferInstance
      let l : Fin N := ⟨0, hN⟩
      refine null_of_finite_curve ν (isOpen_univ.measure_ne_zero ν Set.univ_nonempty) μ
        (isClosed_eq (continuous_qd _ a) continuous_const).measurableSet
        (L := fun t => Pi.single l t) (continuous_single (A := fun _ : Fin N => Fv F v) l) fun x => ?_
      have ha' : algebraMap F (Fv F v) (a l) ≠ 0 := (map_ne_zero _).2 (ha l)
      refine (FibExist.finite_quadratic_zeros ha' (algebraMap F _ (2 * a l) * x l)
        (qd _ a x)).subset fun t ht => ?_
      have h1 : qd (Fv F v) a (x + Pi.single l t) = 0 := ht
      rw [qd_add, qd_single, Bd_single] at h1
      rw [Set.mem_setOf_eq, ← h1]; ring)
  exact ⟨μ, ν, f, hμ, hν, e ▸ hf⟩

theorem exists_inf (ψ : AddChar (AF F) ℂ) [IsTotallyReal F] (hψ : IsCharAF F ψ) (a : Fin N → F)
    (ha : ∀ l, a l ≠ 0) (hN : 0 < N) :
    ∃ (μ : Measure (Fin N → Ainf F)) (ν : Measure (Ainf F)) (f : Ainf F → Measure (Fin N → Ainf F)),
      SelfDual μ (fun x y => psiInf F ψ (Bd (Ainf F) a x y)) ∧ SdR (Ainf F) (psiInf F ψ) ν ∧
      IsFibreFamily μ (qd (Ainf F) a) id Set.univ ν {c : Ainf F | ∀ w, c w ≠ 0} f := by
  classical
  have hnd := (CharLoc.char_local F ψ hψ).2.2
  obtain ⟨A, hA, hA'⟩ := SdInf.exists_equiv_Ainf F
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨L₀, hL₀c, hL₀a, hL₀⟩ := SdInf.exists_log_char (fun u => psiInf F ψ (A.symm u)) (hpc.comp hA')
    (fun u => hψ.2.1 _) (fun u v => by
      simp only [psiInf, map_add, ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
  let L : Ainf F → ℝ := fun x => L₀ (A x)
  have hLc : Continuous L := hL₀c.comp hA
  have hLa : ∀ x y, L (x + y) = L x + L y := fun x y => by simp only [L, map_add, hL₀a]
  have hL : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ)) :=
    fun x => by simpa using hL₀ (A x)
  have hLn : ∀ x, (∀ y, L (x * y) = 0) → x = 0 := fun x h => hnd x fun y => by simp [hL, h]
  obtain ⟨ν, hν, -⟩ := SdInf.existsUnique_of_equiv A hA hA' (fun s t => L (s * t))
    (fun x x' y => by rw [add_mul, hLa])
    (fun x y => by rw [mul_comm]) (fun y => hLc.comp (continuous_id.mul continuous_const)) hLn
  obtain ⟨μ, hμ, -⟩ := SdInf.existsUnique_of_equiv (V := Fin N → Ainf F)
    (AddEquiv.piCongrRight fun _ : Fin N => A)
    (show Continuous fun (X : Fin N → Ainf F) i => A (X i) by fun_prop)
    (show Continuous fun (X : Fin N → InfinitePlace F → ℝ) i => A.symm (X i) by fun_prop)
    (fun X Y => L (Bd (Ainf F) a X Y))
    (fun X X' Y => by rw [Bd_add, hLa]) (fun X Y => by rw [Bd_symm])
    (fun Y => hLc.comp (continuous_Bd _ a Y))
    (fun X h => Bd_nondeg _ a ha X fun Y => hLn _ fun t => by
      rw [mul_comm, Bd_symm, ← Bd_smul, Bd_symm]; exact h _)
  haveI := hμ.1
  haveI := hν.1
  have e : {c : Ainf F | ∀ w, c w ≠ 0} = {c | IsUnit c} := by
    ext c; exact (FibExist.isUnit_ainf_iff c).symm
  have hq := continuous_qd (Ainf F) a
  obtain ⟨f, hf⟩ := FibExist.exists_fibreFamily (nice_ainf_fv F).1 μ ν (qd (Ainf F) a) hq (qd_smul _ a) (by
    simp only [FibExist.isUnit_ainf_iff]
    refine ae_all_iff.2 fun w => ?_
    have hw : w.IsReal := IsTotallyReal.isReal w
    let l : Fin N := ⟨0, hN⟩
    let i := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm
    let j : ℝ → Ainf F := fun t => Pi.single (M := fun w : InfinitePlace F => w.Completion) w (i t)
    have hj : Continuous j := (continuous_single (A := fun w : InfinitePlace F => w.Completion) w).comp
      i.continuous
    have hev : Continuous fun c : Ainf F => c w := continuous_apply w
    rw [ae_iff]
    simp only [ne_eq, not_not]
    refine FibExist.null_of_finite_curve μ (isClosed_eq (hev.comp hq) continuous_const).measurableSet
      (L := fun t => Pi.single l (j t)) ((continuous_single l).comp hj) fun x => ?_
    have ha' : algebraMap F w.Completion (a l) ≠ 0 := (map_ne_zero _).2 (ha l)
    refine ((FibExist.finite_quadratic_zeros ha' ((algebraMap F (Ainf F) (2 * a l) * x l) w)
      (qd (Ainf F) a x w)).preimage i.injective.injOn).subset fun t ht => ?_
    have h1 : qd (Ainf F) a (x + Pi.single l (j t)) w = 0 := ht
    have h3 : qd (Ainf F) a (x + Pi.single l (j t)) = algebraMap F (Ainf F) (a l) * j t ^ 2 +
        algebraMap F (Ainf F) (2 * a l) * x l * j t + qd (Ainf F) a x := by
      rw [qd_add, qd_single, Bd_single]; ring
    rw [h3] at h1
    have h2 : j t w = i t := Pi.single_eq_same _ _
    rw [Set.mem_preimage, Set.mem_setOf_eq, ← h2]
    exact h1)
  refine ⟨μ, ν, f, ?_, ?_, e ▸ hf⟩
  · simpa only [hL] using hμ
  · simpa only [SdR, hL] using hν

theorem nonempty_locData (ψ : AddChar (AF F) ℂ) [IsTotallyReal F] (hψ : IsCharAF F ψ) (a : Fin N → F)
    (ha : ∀ l, a l ≠ 0) (hN : 0 < N) : Nonempty (LocData ψ a) := by
  obtain ⟨μ, ν, f, h1, h2, h3⟩ := exists_inf ψ hψ a ha hN
  choose μv νv fv g1 g2 g3 using exists_fin ψ hψ a ha hN
  exact ⟨⟨μ, ν, μv, νv, f, fv, h1, h2, g1, g2, h3, g3⟩⟩

theorem locData_rat : ∃ ψ : AddChar (AF ℚ) ℂ, IsCharAF ℚ ψ ∧ Nonempty (LocData ψ (fun _ : Fin 6 => (1 : ℚ))) := by
  obtain ⟨ψ, hψ⟩ := CharZero.exists_isCharAF ℚ
  exact ⟨ψ, hψ, nonempty_locData ψ hψ _ (fun _ => one_ne_zero) (by norm_num)⟩

theorem exists_isCov1 : ∃ ν : Measure (AF F), IsCov1 ν := by
  let Γ := (algebraMap F (AF F)).range.toAddSubgroup
  haveI : DiscreteTopology Γ := by
    obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    convert hVo.preimage (continuous_subtype_val (p := fun x => x ∈ Γ)) using 1
    ext ⟨_, x, rfl⟩
    constructor
    · intro h
      have h1 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
      have h2 : algebraMap F (AF F) x = 0 := h1
      show algebraMap F (AF F) x ∈ V
      rw [h2]; exact hV0
    · intro h
      have hx : x = 0 := h0 x (hVU h)
      subst hx
      exact Subtype.ext (map_zero _)
  obtain ⟨K, hK, h⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  obtain ⟨μ, D, hμ, hD, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (AF F) Γ K hK fun x => by
    obtain ⟨y, hy⟩ := h x
    exact ⟨_, ⟨-y, rfl⟩, by rw [map_neg, neg_add_eq_sub]; exact hy⟩).1
  obtain ⟨t, hts, htm, hae⟩ := hD.nullMeasurableSet.exists_measurable_superset_ae_eq
  refine ⟨μ, hμ, t, htm, ⟨htm.nullMeasurableSet, ?_, fun g g' hg => ?_⟩, by rw [measure_congr hae, h1]⟩
  · exact hD.ae_covers.mono fun x ⟨g, hg⟩ => ⟨g, hts hg⟩
  · have e : ∀ g : Γ, (g +ᵥ t : Set (AF F)) =ᵐ[μ] (g +ᵥ D : Set (AF F)) := fun g =>
      Measure.QuasiMeasurePreserving.vadd_ae_eq_of_ae_eq g
        (measurePreserving_add_left μ _).quasiMeasurePreserving hae
    exact (hD.aedisjoint hg).congr (e g) (e g')

theorem exists_isLam (ψ : AddChar (AF F) ℂ) [IsTotallyReal F] (hψ : IsCharAF F ψ) : ∃ lam, IsLam ψ lam := by
  classical
  have hnd := (CharLoc.char_local F ψ hψ).2.2
  let A : Ainf F ≃+* (InfinitePlace F → ℝ) := RingEquiv.piCongrRight fun v =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hA' : Continuous A.symm := continuous_pi fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous.comp
        (continuous_apply v)
  have hre : ∀ x w, re x w = A x w := fun x w => by
    show _ = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (x w)
    rw [re, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w), Complex.ofReal_re]
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨L₀, hL₀c, hL₀a, hL₀⟩ := SdInf.exists_log_char (fun u => psiInf F ψ (A.symm u)) (hpc.comp hA')
    (fun u => hψ.2.1 _) (fun u v => by
      simp only [psiInf, map_add, ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
  let L : (InfinitePlace F → ℝ) →L[ℝ] ℝ := (AddMonoidHom.mk' L₀ hL₀a).toRealLinearMap hL₀c
  have hL : ∀ u, L₀ u = ∑ w, L₀ (Pi.single w 1) * u w := fun u => by
    have : L u = ∑ w, L (Pi.single w 1) * u w := by
      conv_lhs => rw [← Finset.univ_sum_single u, map_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    exact this
  refine ⟨fun w => L₀ (Pi.single w 1), fun w hw => ?_, fun x => ?_⟩
  · have := hnd (A.symm (Pi.single w 1)) fun y => by
      have h := hL₀ (Pi.single w 1 * A y)
      rw [map_mul, A.symm_apply_apply] at h
      rw [h, hL, Finset.sum_eq_single w (fun b _ hb => by simp [hb]) (by simp)]
      simp only at hw
      simp [hw]
    have h2 := congrFun (A.symm.injective (this.trans (map_zero _).symm)) w
    simp at h2
  · have h := hL₀ (A x)
    rw [A.symm_apply_apply, hL] at h
    simpa only [hre] using h

theorem exists_ctx [hF : IsTotallyReal F] (a : Fin N → F) (ha : ∀ l, a l ≠ 0) (hN : 0 < N) :
    ∃ ψ lam ν, Ctx ψ lam ν a ∧ Nonempty (LocData ψ a) := by
  obtain ⟨ψ, hψ⟩ := CharZero.exists_isCharAF F
  obtain ⟨lam, hl⟩ := exists_isLam ψ hψ
  obtain ⟨ν, hν⟩ := exists_isCov1 (F := F)
  exact ⟨ψ, lam, ν, ⟨hF, hψ, hl, hν, ha⟩, nonempty_locData ψ hψ a ha hN⟩

example (ψ : AddChar (AF F) ℂ) [IsTotallyReal F] (hψ : IsCharAF F ψ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fv F v,
      (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F :=
  (CharLoc.char_local F ψ hψ).2.1

theorem rho_Ub (ψ : AddChar (AF F) ℂ) (a : Fin N → F) (b : AF F) (x y : Fin N → AF F)
    (Φ : (Fin N → AF F) → ℂ) : rho ψ a x y (Ub ψ a b Φ) = Ub ψ a b (rho ψ a x (b • x + y) Φ) := by
  funext u
  have h2 : algebraMap F (AF F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]; simp
  have hx : Bd (AF F) a x x = 2 * qd (AF F) a x := by
    simp only [qd, Bd, Finset.mul_sum, map_mul, map_ofNat]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [rho, Ub, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  rw [qd_add, Bd_symm _ a u (b • x + y), Bd_symm _ a x (b • x + y), Bd_add, Bd_add, Bd_smul, Bd_smul, hx,
    Bd_symm _ a x u, Bd_symm _ a y u, Bd_symm _ a y x]
  linear_combination (-(b * qd (AF F) a x)) * h2

theorem rho_Da (ψ : AddChar (AF F) ℂ) (a : Fin N → F) (t s : AF F) (h : t * s = 1) (x y : Fin N → AF F)
    (Φ : (Fin N → AF F) → ℂ) : rho ψ a x y (Da t Φ) = Da t (rho ψ a (t • x) (s • y) Φ) := by
  funext u
  have e : ∀ z, Bd (AF F) a (t • z) (s • y) = Bd (AF F) a z y := fun z => by
    rw [Bd_smul, Bd_symm, Bd_smul, ← mul_assoc, h, one_mul, Bd_symm]
  simp only [rho, Da, e, smul_add]

theorem count_ratl (a : Fin N → F) :
    (Measure.sum fun ξ : {ξ : Fin N → F // ξ ≠ 0} => Measure.dirac (rat (ξ : Fin N → F)))
      {u | ¬ ∃ β : F, qd (AF F) a u = algebraMap F (AF F) β} = 0 := by
  have hm : MeasurableSet {u : Fin N → AF F | ¬ ∃ β : F, qd (AF F) a u = algebraMap F (AF F) β} := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact ((continuous_qd (AF F) a).measurable
      (Set.countable_range (algebraMap F (AF F))).measurableSet).compl.congr (by
        ext u; simp [eq_comm])
  rw [Measure.sum_apply _ hm, ENNReal.tsum_eq_zero]
  intro ξ
  rw [Measure.dirac_apply' _ hm, Set.indicator_of_notMem]
  exact fun h => h ⟨qd F a ξ, by simp [qd, rat]⟩

end GlobalTheory.SWQ.Model
