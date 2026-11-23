import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem et_point (E K C : Type) [Field E] [Field K] [Algebra E K] [IsAlgClosed K] [CommRing C] [Algebra E C]
    [Algebra.FiniteType E C] (m : Ideal C) [m.IsMaximal] :
    ∃ ι : (C ⧸ m) →ₐ[E] K, Function.Injective ι := by
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite E (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing E (C ⧸ m)
  let ι : (C ⧸ m) →ₐ[E] K := IsAlgClosed.lift
  exact ⟨ι, ι.toRingHom.injective⟩

private theorem et_unram (O K C : Type) [CommRing O] [Field K] [Algebra O K] [CommRing C] [Algebra O C]
    [Algebra.FiniteType O C]
    (hp : ∀ m : Ideal C, m.IsMaximal → ∃ ι : (C ⧸ m) →ₐ[O] K, Function.Injective ι)
    (hD : ∀ ξ : C →ₐ[O] K, PtDer ξ K = ⊥) : Algebra.FormallyUnramified O C := by
  have key : ∀ m : Ideal C, m.IsMaximal → (⊤ : Submodule C Ω[C⁄O]) ≤ m • ⊤ := by
    intro m hm x _
    by_contra hx
    letI : Field (C ⧸ m) := Ideal.Quotient.field m
    obtain ⟨ι, hι⟩ := hp m hm
    have hq : Submodule.Quotient.mk (p := m • (⊤ : Submodule C Ω[C⁄O])) x ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (C ⧸ m) (Ω[C⁄O] ⧸ m • (⊤ : Submodule C Ω[C⁄O])),
        φ (Submodule.Quotient.mk x) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hq ((Module.forall_dual_apply_eq_zero_iff (C ⧸ m) _).mp hall)
    let f : Ω[C⁄O] →ₗ[C] C ⧸ m := (φ.restrictScalars C).comp (m • (⊤ : Submodule C Ω[C⁄O])).mkQ
    let D : Derivation O C (C ⧸ m) := f.compDer (KaehlerDifferential.D O C)
    let ξ : C →ₐ[O] K := ι.comp (Ideal.Quotient.mkₐ O m)
    let L : C →ₗ[O] K := ι.toLinearMap.comp (D : C →ₗ[O] C ⧸ m)
    have hL : L ∈ PtDer ξ K := by
      intro a b
      show ι (D (a * b)) = ι (Ideal.Quotient.mk m a) • ι (D b) + ι (Ideal.Quotient.mk m b) • ι (D a)
      rw [Derivation.leibniz, Algebra.smul_def, Algebra.smul_def, map_add, map_mul, map_mul,
        smul_eq_mul, smul_eq_mul]
      rfl
    rw [hD ξ, Submodule.mem_bot] at hL
    have hDz : ∀ c, D c = 0 := by
      intro c
      apply hι
      rw [map_zero]
      exact LinearMap.congr_fun hL c
    have hf : f = 0 := by
      apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation O C)
      intro c
      simpa [D] using hDz c
    apply hφ
    have h2 := LinearMap.congr_fun hf x
    simpa [f] using h2
  have hfg : (⊤ : Submodule C Ω[C⁄O]).FG := Module.finite_def.mp inferInstance
  have hann : Module.annihilator C Ω[C⁄O] = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ hfg (key m hm)
    have hrJ : r ∈ Module.annihilator C Ω[C⁄O] := Module.mem_annihilator.mpr (fun n => hr n trivial)
    have h3 := m.sub_mem (hle hrJ) hr1
    rw [sub_sub_cancel] at h3
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr h3)
  have h1 : (1 : C) ∈ Module.annihilator C Ω[C⁄O] := by
    rw [hann]
    exact Submodule.mem_top
  have h0 : ∀ n : Ω[C⁄O], n = 0 := by
    intro n
    rw [← one_smul C n]
    exact Module.mem_annihilator.mp h1 n
  exact ⟨⟨fun a b => (h0 a).trans (h0 b).symm⟩⟩

theorem UpperTheory.V.Alg.M.et_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (C : Type) [CommRing C] [Algebra O C] [Algebra.FiniteType O C], (∀ c : O, c ≠ 0 → IsUnit (algebraMap O C c)) →
      (∀ ξ : C →ₐ[O] K, PtDer ξ K = ⊥) → Finite (C →ₐ[O] K) ∧ ∀ h : C, (∀ ξ : C →ₐ[O] K, ξ h = 0) → h = 0 := by
  intro O _ _ _ _ _ K _ _ _ _ C _ _ _ hunit hD
  have huC : ∀ y : nonZeroDivisors O, IsUnit (algebraMap O C y) :=
    fun y => hunit y (nonZeroDivisors.ne_zero y.2)
  have hinjK : Function.Injective (algebraMap O K) := FaithfulSMul.algebraMap_injective O K
  have huK : ∀ y : nonZeroDivisors O, IsUnit (algebraMap O K y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr (fun h0 => nonZeroDivisors.ne_zero y.2 (hinjK ?_))
    rw [h0, map_zero]
  letI : Algebra (FractionRing O) C :=
    (IsLocalization.lift (M := nonZeroDivisors O) (S := FractionRing O) huC).toAlgebra
  letI : Algebra (FractionRing O) K :=
    (IsLocalization.lift (M := nonZeroDivisors O) (S := FractionRing O) huK).toAlgebra
  haveI : IsScalarTower O (FractionRing O) C := IsScalarTower.of_algebraMap_eq
    (fun r => (IsLocalization.lift_eq (M := nonZeroDivisors O) (S := FractionRing O) huC r).symm)
  haveI : IsScalarTower O (FractionRing O) K := IsScalarTower.of_algebraMap_eq
    (fun r => (IsLocalization.lift_eq (M := nonZeroDivisors O) (S := FractionRing O) huK r).symm)
  haveI : Algebra.FiniteType (FractionRing O) C :=
    Algebra.FiniteType.of_restrictScalars_finiteType O (FractionRing O) C
  have hpt : ∀ m : Ideal C, m.IsMaximal → ∃ ι : (C ⧸ m) →ₐ[O] K, Function.Injective ι := by
    intro m hm
    haveI := hm
    obtain ⟨ι, hι⟩ := et_point (FractionRing O) K C m
    exact ⟨ι.restrictScalars O, hι⟩
  haveI : Algebra.FormallyUnramified O C := et_unram O K C hpt hD
  haveI : Algebra.FormallyUnramified (FractionRing O) C :=
    Algebra.FormallyUnramified.of_restrictScalars O (FractionRing O) C
  haveI : Module.Finite (FractionRing O) C := Algebra.FormallyUnramified.finite_of_free (FractionRing O) C
  haveI : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field (FractionRing O) C
  refine ⟨?_, ?_⟩
  · have hcompat : ∀ ξ : C →ₐ[O] K, ∀ r : FractionRing O,
        ξ (algebraMap (FractionRing O) C r) = algebraMap (FractionRing O) K r := by
      intro ξ r
      have hc : ξ.toRingHom.comp (algebraMap (FractionRing O) C) = algebraMap (FractionRing O) K := by
        apply IsLocalization.ringHom_ext (nonZeroDivisors O)
        apply RingHom.ext
        intro a
        rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
        exact ξ.commutes a
      exact RingHom.congr_fun hc r
    let up : (C →ₐ[O] K) → (C →ₐ[FractionRing O] K) := fun ξ => { ξ.toRingHom with commutes' := hcompat ξ }
    have hup : Function.Injective up := by
      intro ξ₁ ξ₂ h
      ext c
      exact AlgHom.congr_fun h c
    haveI : Finite (C →ₐ[FractionRing O] K) := (linearIndependent_toLinearMap (FractionRing O) C K).finite
    exact Finite.of_injective up hup
  · intro h hh
    haveI : IsJacobsonRing C := isJacobsonRing_of_finiteType (A := FractionRing O)
    have hrad : (⊥ : Ideal C).IsRadical := by
      intro x hx
      obtain ⟨n, hn⟩ := hx
      rw [Ideal.mem_bot] at hn ⊢
      exact IsNilpotent.eq_zero ⟨n, hn⟩
    have hj := IsJacobsonRing.out' (⊥ : Ideal C) hrad
    rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
    rintro J ⟨-, hJ⟩
    haveI := hJ
    obtain ⟨ι, hι⟩ := hpt J hJ
    have h5 := hh (ι.comp (Ideal.Quotient.mkₐ O J))
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← map_zero ι] at h5
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hι h5)
