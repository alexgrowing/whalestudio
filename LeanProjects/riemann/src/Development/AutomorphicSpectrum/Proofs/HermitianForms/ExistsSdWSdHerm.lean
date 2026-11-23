import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
import Development.AutomorphicSpectrum.Proofs.HermitianForms.IndicatorInSchrodingerSpanStatement
import Development.AutomorphicSpectrum.Proofs.HermitianForms.AdelicCharacterLocalNontrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallDualLattices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SdFin

section Lat

open GlobalTheory.JR.DualLattice

variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K]

theorem exists_of_std (ψ : AddChar K ℂ) (hψ : GlobalTheory.JR.IsStdChar ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (V : Type) [AddCommGroup V] [Module K V] [Module.Finite K V] [TopologicalSpace V]
    [IsModuleTopology K V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (β : LinearMap.BilinForm K V) (hs : β.IsSymm) (hβ : β.Nondegenerate) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) := by
  classical
  let e := Module.finBasis K V
  let e' := β.dualBasis hβ e
  have hB : ∀ x y, β x y = ∑ i, e.repr x i * e'.repr y i := by
    intro x y
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, hs.eq]
  obtain ⟨t, ht0, ht1⟩ := NormedField.exists_norm_lt_one K
  have htne : t ≠ 0 := norm_pos_iff.1 ht0
  have hz : ∀ k : ℤ, t ^ k ≠ 0 := fun k => zpow_ne_zero k htne
  have hp : ∀ k : ℤ, 0 < ‖t ^ k‖ := fun k => norm_pos_iff.2 (hz k)
  have hp' : ∀ k : ℤ, 0 < ‖(t ^ k)⁻¹‖ := fun k => norm_pos_iff.2 (inv_ne_zero (hz k))
  have hex : ∀ (b : Module.Basis (Fin (Module.finrank K V)) K V) (x : V),
      ∃ n : ℕ, ∀ i, ‖b.repr x i‖ ≤ ‖t‖⁻¹ ^ n := by
    intro b x
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ i, ‖b.repr x i‖) (one_lt_inv₀ ht0 |>.2 ht1)
    exact ⟨n, fun i => (Finset.single_le_sum (f := fun i => ‖b.repr x i‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans hn.le⟩
  refine GlobalTheory.T.self_dual_lattice_filtration_character V _ (fun k => box e ‖t ^ k‖ (norm_nonneg _))
    (fun k => box e' ‖(t ^ k)⁻¹‖ (norm_nonneg _)) (fun x x' y => ?_) (fun x y => ?_) (fun x y => hu _)
    (GlobalTheory.JR.exists_small_dual_lattices K ψ hψ V β hs hβ).1
    (fun k => ⟨(box_open_compact e _ (hp k)).1, (box_open_compact e _ (hp k)).2,
      (box_open_compact e' _ (hp' k)).1, (box_open_compact e' _ (hp' k)).2⟩) ?_ ?_ ?_ ?_
    (fun k y => box_dual hψ e e' (fun x y => β x y) hB (t ^ k) (hz k) y) (fun k x => ?_)
  · simp [AddChar.map_add_eq_mul]
  · rw [hs.eq]
  · intro a b hab x hx i
    refine (hx i).trans ?_
    rw [norm_zpow, norm_zpow]
    exact zpow_le_zpow_right_of_le_one₀ ht0 ht1.le hab
  · intro U hU
    have h0 : (coordHomeo e).symm 0 = 0 := map_zero e.equivFun.symm
    have hU' : (coordHomeo e).symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank K V) → K) :=
      (coordHomeo e).symm.continuous.continuousAt.preimage_mem_nhds (by rwa [h0])
    obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU'
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε ht1
    refine ⟨(n : ℤ), ?_⟩
    rw [box_eq]
    intro x hx
    have h2 : ‖t ^ (n : ℤ)‖ ≤ ε := by simpa using hn.le
    have := hsub (Metric.closedBall_subset_closedBall h2 hx)
    simpa using this
  · intro x
    obtain ⟨n, hn⟩ := hex e x
    refine ⟨-(n : ℤ), fun i => (hn i).trans_eq ?_⟩
    simp [norm_zpow]
  · intro y
    obtain ⟨n, hn⟩ := hex e' y
    refine ⟨(n : ℤ), fun i => (hn i).trans_eq ?_⟩
    simp
  · have := box_dual hψ e' e (fun y x => β x y)
      (fun y x => by simp only [hB, mul_comm]) (t ^ k)⁻¹ (inv_ne_zero (hz k)) x
    simpa only [inv_inv] using this

end Lat

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem properSpace_Fv : ProperSpace (Fv F v) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.tjcosets_finite v

theorem exists_of_bilin (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hne : ∃ t, ψ t ≠ 1) (V : Type) [AddCommGroup V] [Module (Fv F v) V] [Module.Finite (Fv F v) V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (β : LinearMap.BilinForm (Fv F v) V) (hs : ∀ x y, β x y = β y x)
    (hn : ∀ x, (∀ y, β x y = 0) → x = 0) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) := by
  haveI hp : ProperSpace (Fv F v) := properSpace_Fv v
  letI : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI : IsUltrametricDist (Fv F v) := inferInstance
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : IsModuleTopology (Fv F v) V := isModuleTopologyOfFiniteDimensional
  let c' := (Module.finBasis (Fv F v) V).equivFun
  have hcc : Continuous c' := IsModuleTopology.continuous_of_linearMap c'.toLinearMap
  have hcc' : Continuous c'.symm := IsModuleTopology.continuous_of_linearMap c'.symm.toLinearMap
  let eV : V ≃ₜ (Fin (Module.finrank (Fv F v) V) → Fv F v) :=
    { c'.toEquiv with continuous_toFun := hcc, continuous_invFun := hcc' }
  haveI : LocallyCompactSpace V := eV.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology V := eV.secondCountableTopology
  obtain ⟨n, hc⟩ := GlobalTheory.CharConductor.exists_exponent_of_valued ψ hψ hne
  obtain ⟨c, hcv⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hcv.symm.trans (map_zero _))
  have hstd : GlobalTheory.JR.IsStdChar (ψ.mulShift c) := by
    constructor
    · intro x hx
      exact (hc c).2 hcv.le x (Valued.toNormedField.norm_le_one_iff.1 hx)
    · obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
      have h1 : ¬ ∀ s : Fv F v, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (c * t * s) = 1 := by
        rw [hc, map_mul, hcv, ht, ← WithZero.exp_add, WithZero.exp_le_exp]
        omega
      push Not at h1
      obtain ⟨s, hs1, hs2⟩ := h1
      refine ⟨t * s, by rwa [AddChar.mulShift_apply, ← mul_assoc], fun y hy => ?_⟩
      rw [Valued.toNormedField.norm_lt_one_iff] at hy
      rw [Valued.toNormedField.norm_le_one_iff, mul_right_comm, map_mul]
      refine mul_le_one' ?_ hs1
      rw [map_mul, ht]
      rcases eq_or_ne (Valued.v y : WithZero (Multiplicative ℤ)) 0 with h | h
      · simp [h]
      · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
        rw [← WithZero.exp_log h, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
  have hn' : ∀ x, (∀ y, (c⁻¹ • β) x y = 0) → x = 0 := fun x h => hn x fun y => by
    simpa [hc0] using h y
  have hs' : ∀ x y, (c⁻¹ • β) x y = (c⁻¹ • β) y x := fun x y => by simp [hs x y]
  have key := exists_of_std (ψ.mulShift c) hstd (fun t => hu _) V (c⁻¹ • β) ⟨hs'⟩
    ⟨hn', fun y h => hn' y fun x => (hs' y x).trans (h x)⟩
  have e : ∀ x y, ψ.mulShift c ((c⁻¹ • β) x y) = ψ (β x y) := fun x y => by
    simp [AddChar.mulShift_apply, hc0]
  simpa only [e] using key

end Local

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

theorem sigR_smul (c : R) (z : R ⊗[F] E) : sigR R σ (c • z) = c • sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul a e => rfl

theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [hσ]

theorem trace_tmul [FiniteDimensional F E] (c : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (c ⊗ₜ[F] e) = c * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (c ⊗ₜ[F] e : R ⊗[F] E) = c • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_eq_mul]
  congr 1
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  ext x
  simp

theorem trace_nondeg [FiniteDimensional F E] [Algebra.IsSeparable F E] (z : R ⊗[F] E)
    (h : ∀ w, Algebra.trace R (R ⊗[F] E) (z * w) = 0) : z = 0 := by
  classical
  let b := Module.finBasis F E
  let b' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b
  have key : ∀ (k) (z : R ⊗[F] E), (Algebra.TensorProduct.basis R b').repr z k =
      Algebra.trace R (R ⊗[F] E) (z * (1 : R) ⊗ₜ[F] b k) := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_mul]
    | tmul a e =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, trace_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp [b', LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  refine (Algebra.TensorProduct.basis R b').ext_elem fun k => ?_
  rw [key, h]; simp

theorem trace_sigR [FiniteDimensional F E] (z : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ z) = Algebra.trace R (R ⊗[F] E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    show Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] σ e) = _
    rw [trace_tmul, trace_tmul]
    congr 2
    exact Algebra.trace_eq_of_algEquiv
      (AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)) e

variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

noncomputable def bilinW (n : ℕ) : LinearMap.BilinForm R (Fin n → Fin M → R ⊗[F] E) :=
  LinearMap.mk₂ R (BR R σ J)
    (fun x x' y => by
      simp [BR, hR, hform, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp [BR, hR, hform, sigR_smul, Finset.mul_sum])
    (fun x y y' => by
      simp [BR, hR, hform, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp [BR, hR, hform, Finset.mul_sum])

theorem hR_symm [FiniteDimensional F E] (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    (x y : Fin M → R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = Algebra.trace R (R ⊗[F] E) (hR R σ J y x) := by
  rw [← trace_sigR R σ]
  congr 1
  simp only [hR, hform, map_sum, map_mul, sigR_sigR R σ hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : sigR R σ (JR R J j i) = JR R J i j := by
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  rw [this]; ring

theorem BR_symm [FiniteDimensional F E] (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {n : ℕ}
    (X Y : Fin n → Fin M → R ⊗[F] E) : BR R σ J X Y = BR R σ J Y X :=
  Finset.sum_congr rfl fun a _ => hR_symm R σ J hσ hJ (X a) (Y a)

theorem BR_nondeg [FiniteDimensional F E] [Algebra.IsSeparable F E] (hσ : ∀ x, σ (σ x) = x)
    (hJ : IsHermND σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (h : ∀ Y, BR R σ J X Y = 0) : X = 0 := by
  classical
  funext a
  have h1 : Matrix.vecMul (fun i => sigR R σ (X a i)) (JR R J) = 0 := by
    funext j
    refine trace_nondeg R _ fun w => ?_
    have h2 := h (Pi.single a (Pi.single j w))
    rw [BR, Finset.sum_eq_single a (fun b _ hb => by
      simp [Pi.single_eq_of_ne hb, hR, hform]) (by simp)] at h2
    simpa [hR, hform, Pi.single_apply, Matrix.vecMul, dotProduct, Finset.sum_mul] using h2
  have hu : IsUnit (JR R J : Matrix (Fin M) (Fin M) (R ⊗[F] E)).det := by
    have : (JR R J : Matrix (Fin M) (Fin M) (R ⊗[F] E)).det = inclR R J.det :=
      ((inclR R).map_det J).symm
    rw [this]
    exact (Ne.isUnit hJ.2).map _
  have h2 := congrArg (fun v => Matrix.vecMul v (JR R J)⁻¹) h1
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one,
    Matrix.zero_vecMul] at h2
  funext i
  rw [← sigR_sigR R σ hσ (X a i), congrFun h2 i]
  simp

@[reducible] def hermSMul (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun c S => ⟨c • S.1, fun a b => by
    rw [Matrix.smul_apply, Matrix.smul_apply, sigR_smul, S.2 a b]⟩⟩

@[reducible] def hermModule (n : ℕ) : Module R (HermR R σ n) :=
  letI := hermSMul R σ n
  Function.Injective.module R (HermR R σ n).subtype Subtype.val_injective (fun _ _ => rfl)

noncomputable def bilinH (n : ℕ) :
    letI := hermModule R σ n
    LinearMap.BilinForm R (HermR R σ n) :=
  letI := hermModule R σ n
  LinearMap.mk₂ R (pairHerm R σ n)
    (fun x x' y => by
      simp [pairHerm, add_mul, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      change pairHerm R σ n ⟨c • x.1, _⟩ y = _
      simp [pairHerm, Finset.mul_sum, mul_left_comm c])
    (fun x y y' => by
      simp [pairHerm, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      change pairHerm R σ n x ⟨c • y.1, _⟩ = _
      simp [pairHerm, Finset.mul_sum, mul_left_comm c])

theorem pairHerm_symm (n : ℕ) (S T : HermR R σ n) : pairHerm R σ n S T = pairHerm R σ n T S := by
  simp only [pairHerm]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairHerm_nondeg [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero F]
    (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (S : HermR R σ n) (h : ∀ T, pairHerm R σ n S T = 0) : S = 0 := by
  classical
  apply Subtype.ext
  ext a b
  refine trace_nondeg R _ fun w => ?_
  have hT : (Matrix.single b a w + Matrix.single a b (sigR R σ w)) ∈ HermR R σ n := by
    intro i j
    simp only [Matrix.add_apply, Matrix.single_apply, map_add, apply_ite (sigR R σ), map_zero,
      sigR_sigR R σ hσ]
    rw [add_comm]
    simp only [and_comm]
  have h1 := h ⟨_, hT⟩
  have h2 : ∑ i, ∑ j, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j *
      (Matrix.single b a w + Matrix.single a b (sigR R σ w) : Matrix _ _ _) j i =
      S.1 a b * w + sigR R σ (S.1 a b * w) := by
    rw [map_mul, S.2 b a]
    simp [Matrix.single_apply, mul_add, Finset.sum_add_distrib, ite_and]
  simp only [pairHerm] at h1
  rw [h2, map_add, trace_sigR, ← two_mul, ← mul_assoc] at h1
  have h3 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; simp
  rwa [h3, one_mul] at h1

end Alg

noncomputable def psiChar {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ where
  toFun := psiV F ψ v
  map_zero_eq_one' := by
    classical
    have : pairA F 0 (singleV F v 0) = 0 :=
      Prod.ext rfl (Subtype.ext (Pi.single_zero v))
    rw [psiV, this, AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by
    classical
    have : pairA F 0 (singleV F v (a + b)) = pairA F 0 (singleV F v a) + pairA F 0 (singleV F v b) :=
      Prod.ext (add_zero 0).symm (Subtype.ext (Pi.single_add v a b))
    rw [psiV, this, AddChar.map_add_eq_mul]; rfl

theorem exists_sdW_sdHerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), (∃ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) n μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) n ν := by
  intro F E _ _ _ _ _ σ h M J hJ n ψ hψ v
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply φ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨hc, hne⟩ := (GlobalTheory.T.adelic_character_local_nontrivial F ψ hψ).1 v
  have hu : ∀ t, ‖psiChar ψ v t‖ = 1 := fun t => hψ.2.1 _
  haveI hp : ProperSpace (Fv F v) := properSpace_Fv v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
  let cE := (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)).equivFun
  let eE : (Fv F v ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Fv F v) :=
    { cE.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap cE.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap cE.symm.toLinearMap }
  haveI : T2Space (Fv F v ⊗[F] E) := eE.isEmbedding.t2Space
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eE.secondCountableTopology
  refine ⟨exists_of_bilin v (psiChar ψ v) hc hu hne _ (bilinW (Fv F v) σ J n) (BR_symm _ σ J hσ hJ)
    (BR_nondeg _ σ J hσ hJ), ?_⟩
  letI := hermModule (Fv F v) σ n
  haveI : Module.Finite (Fv F v) (HermR (Fv F v) σ n) :=
    Module.Finite.of_injective
      ({ toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
        HermR (Fv F v) σ n →ₗ[Fv F v] Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) Subtype.val_injective
  haveI : ContinuousSMul (Fv F v) (HermR (Fv F v) σ n) :=
    ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  exact exists_of_bilin v (psiChar ψ v) hc hu hne _ (bilinH (Fv F v) σ n) (pairHerm_symm _ σ n)
    (pairHerm_nondeg _ σ hσ n)

end GlobalTheory.CompanionTheory.SdFin
