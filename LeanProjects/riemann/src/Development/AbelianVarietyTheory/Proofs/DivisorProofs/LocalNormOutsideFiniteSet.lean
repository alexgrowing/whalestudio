import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNorms
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FixedNormCls

theorem map_one_tmul {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) (z : L) :
    (Algebra.TensorProduct.map (AlgHom.id K K) c) ((1 : K) ⊗ₜ[ℚ] z) = (1 : K) ⊗ₜ[ℚ] c z := by
  simp
theorem algebraMap_rat_tmul {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] (q : ℚ) :
    algebraMap K (K ⊗[ℚ] L) (algebraMap ℚ K q) = (1 : K) ⊗ₜ[ℚ] algebraMap ℚ L q := by
  rw [← IsScalarTower.algebraMap_apply ℚ K (K ⊗[ℚ] L),
      ← (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := L)).commutes q,
      Algebra.TensorProduct.includeRight_apply]
theorem key_tmul {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] (a x y q : L) :
    ((1 : K) ⊗ₜ[ℚ] a) * ((1 : K) ⊗ₜ[ℚ] q * ((1 : K) ⊗ₜ[ℚ] x * (1 : K) ⊗ₜ[ℚ] y)) - 1 = (1 : K) ⊗ₜ[ℚ] (a * (q * (x * y)) - 1) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, one_mul, TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]

theorem isOpen_valued_lt_one (v : HeightOneSpectrum ℤ) : IsOpen {x : v.adicCompletion ℚ | Valued.v x < 1} := by
  simpa using (Valued.isClopen_ball (v.adicCompletion ℚ) 1).isOpen

theorem valued_algebraMap (v : HeightOneSpectrum ℤ) (x : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) x) = v.valuation ℚ x :=
  v.valuedAdicCompletion_eq_valuation' x

theorem exists_rat_approx (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (v : HeightOneSpectrum ℤ)
    (a : L) (ha : a ≠ 0) (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ)
    (h : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a =
      algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
        ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y)) :
    ∃ (q : ℚ) (z : L), ∀ j, v.valuation ℚ ((integralBasis L).repr (a⁻¹ * (algebraMap ℚ L q * (z * c z)) - 1) j) < 1 := by
  classical
  let K := v.adicCompletion ℚ
  let A := K ⊗[ℚ] L
  letI : TopologicalSpace A := moduleTopology K A
  haveI : IsModuleTopology K A := ⟨rfl⟩
  haveI : IsTopologicalRing A := IsModuleTopology.isTopologicalRing K A
  let b := integralBasis L
  let bA := Algebra.TensorProduct.basis K b
  let mc : A →ₗ[K] A := (Algebra.TensorProduct.map (AlgHom.id K K) c).toLinearMap
  let Y : (Module.Free.ChooseBasisIndex ℤ (𝓞 L) → K) → A := fun t => ∑ i, t i • bA i
  let F : K × (Module.Free.ChooseBasisIndex ℤ (𝓞 L) → K) → A :=
    fun p => ((1 : K) ⊗ₜ[ℚ] a⁻¹) * (algebraMap K A p.1 * (Y p.2 * mc (Y p.2))) - 1
  have hY : Continuous Y := continuous_finset_sum _ (fun i _ => (continuous_apply i).smul continuous_const)
  have hmc : Continuous mc := IsModuleTopology.continuous_of_linearMap mc
  have hal : Continuous (algebraMap K A) := IsModuleTopology.continuous_of_linearMap (Algebra.linearMap K A)
  have hF : Continuous F :=
    (continuous_const.mul ((hal.comp continuous_fst).mul
      ((hY.comp continuous_snd).mul (hmc.comp (hY.comp continuous_snd))))).sub continuous_const
  let U : Set (K × (Module.Free.ChooseBasisIndex ℤ (𝓞 L) → K)) :=
    ⋂ j, (fun p => bA.coord j (F p)) ⁻¹' {x | Valued.v x < 1}
  have hU : IsOpen U := isOpen_iInter_of_finite fun j =>
    (isOpen_valued_lt_one v).preimage ((IsModuleTopology.continuous_of_linearMap (bA.coord j)).comp hF)
  have hp0 : ((r : K), fun i => bA.repr y i) ∈ U := by
    have hY0 : Y (fun i => bA.repr y i) = y := bA.sum_repr y
    have hF0 : F ((r : K), fun i => bA.repr y i) = 0 := by
      simp only [F, hY0]
      have e : mc y = Algebra.TensorProduct.map (AlgHom.id ℚ K) c y := rfl
      rw [e, ← h, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ha, Algebra.TensorProduct.one_def, sub_self]
    simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, hF0, map_zero]
    intro j
    exact zero_lt_one
  have hd : DenseRange (Prod.map (algebraMap ℚ K) (Pi.map fun (_ : Module.Free.ChooseBasisIndex ℤ (𝓞 L)) => algebraMap ℚ K)) :=
    (HeightOneSpectrum.denseRange_algebraMap ℚ v).prodMap
      (DenseRange.piMap fun _ => HeightOneSpectrum.denseRange_algebraMap ℚ v)
  obtain ⟨⟨q, t⟩, hqt⟩ := hd.exists_mem_open hU ⟨_, hp0⟩
  let z : L := ∑ i, t i • b i
  refine ⟨q, z, fun j => ?_⟩
  have hYz : Y (fun i => algebraMap ℚ K (t i)) = (1 : K) ⊗ₜ[ℚ] z := by
    simp only [Y, z, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, algebraMap_smul, TensorProduct.tmul_smul]
  have hq : algebraMap K A (algebraMap ℚ K q) = (1 : K) ⊗ₜ[ℚ] algebraMap ℚ L q := algebraMap_rat_tmul q
  have key : F (Prod.map (algebraMap ℚ K) (Pi.map fun _ => algebraMap ℚ K) (q, t)) =
      (1 : K) ⊗ₜ[ℚ] (a⁻¹ * (algebraMap ℚ L q * (z * c z)) - 1) := by
    show F (algebraMap ℚ K q, fun i => algebraMap ℚ K (t i)) = _
    simp only [F]
    have hmz : mc ((1 : K) ⊗ₜ[ℚ] z) = (1 : K) ⊗ₜ[ℚ] c z := map_one_tmul c z
    rw [hYz, hq, hmz, key_tmul]
  have hc := Set.mem_iInter.1 hqt j
  simp only [Set.mem_preimage, Set.mem_setOf_eq, key, Module.Basis.coord_apply, bA,
    Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply] at hc
  rwa [valued_algebraMap] at hc

def ord {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (x : L) : ℤ :=
  -WithZero.log (w.valuation L x)

theorem ord_mul {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {x y : L} (hx : x ≠ 0)
    (hy : y ≠ 0) : ord w (x * y) = ord w x + ord w y := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem ord_eq_zero_iff {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {x : L} (hx : x ≠ 0) :
    ord w x = 0 ↔ w.valuation L x = 1 := by
  constructor
  · intro h
    have h' : WithZero.log (w.valuation L x) = 0 := by simp only [ord] at h; omega
    have hne : w.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    rw [← WithZero.exp_log hne, h', WithZero.exp_zero]
  · intro h
    simp [ord, h]

theorem valuation_eq_one_of_coord (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (ε : L)
    (hε : ∀ j, v.valuation ℚ ((integralBasis L).repr (ε - 1) j) < 1) : w.valuation L ε = 1 := by
  classical
  have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 := by
    intro he
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have h1 : w.valuation L (algebraMap (𝓞 L) L (algebraMap ℤ (𝓞 L) m)) < 1 := by
      rw [HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact (Ideal.mem_of_liesOver w.asIdeal v.asIdeal m).1 hm
    have h2 := HeightOneSpectrum.valuation_liesOver L v w (m : ℚ)
    rw [he, pow_zero] at h2
    have e : algebraMap ℚ L (m : ℚ) = algebraMap (𝓞 L) L (algebraMap ℤ (𝓞 L) m) := by simp
    rw [← e, ← h2] at h1
    exact lt_irrefl _ h1
  have hrat : ∀ x : ℚ, v.valuation ℚ x < 1 → w.valuation L (algebraMap ℚ L x) < 1 := by
    intro x hx
    rw [← HeightOneSpectrum.valuation_liesOver L v w x]
    exact pow_lt_one₀ zero_le' hx he
  have hsum : ε - 1 = ∑ j, (integralBasis L).repr (ε - 1) j • integralBasis L j := ((integralBasis L).sum_repr _).symm
  have hlt : w.valuation L (ε - 1) < 1 := by
    rw [hsum]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Algebra.smul_def, map_mul, integralBasis_apply]
    exact (mul_le_mul' le_rfl (HeightOneSpectrum.valuation_le_one _ _)).trans_lt
      (by rw [mul_one]; exact hrat _ (hε j))
  have := Valuation.map_eq_of_sub_lt (w.valuation L) (x := 1) (y := ε) (by rwa [map_one])
  rwa [map_one] at this

theorem exists_local (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (v : HeightOneSpectrum ℤ)
    (a : L) (ha : a ≠ 0) (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ)
    (h : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a =
      algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
        ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y)) :
    ∃ (q : ℚ) (z : L), q ≠ 0 ∧ z ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      w.valuation L a = w.valuation L (algebraMap ℚ L q * (z * c z)) := by
  by_cases hw : ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal
  · obtain ⟨w₀, hw₀⟩ := hw
    obtain ⟨q, z, hqz⟩ := exists_rat_approx L c v a ha r y h
    have hε : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
        w.valuation L (a⁻¹ * (algebraMap ℚ L q * (z * c z))) = 1 := fun w hw =>
      valuation_eq_one_of_coord L v w _ hqz
    have hε0 : a⁻¹ * (algebraMap ℚ L q * (z * c z)) ≠ 0 := by
      intro h0
      have := hε w₀ hw₀
      rw [h0, map_zero] at this
      exact zero_ne_one this
    refine ⟨q, z, ?_, ?_, fun w hw => ?_⟩
    · rintro rfl; simp at hε0
    · rintro rfl; simp at hε0
    · have e : algebraMap ℚ L q * (z * c z) = a * (a⁻¹ * (algebraMap ℚ L q * (z * c z))) := by
        rw [← mul_assoc a, mul_inv_cancel₀ ha, one_mul]
      rw [e, map_mul, hε w hw, mul_one]
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun w hw' => (hw ⟨w, hw'⟩).elim⟩

def primeUnit {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

theorem count_finprod_primeUnit {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (n : HeightOneSpectrum R → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0)
    (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v ((∏ᶠ w, primeUnit (K := K) w ^ n w : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)
      = n v := by
  have hfin : (Function.mulSupport fun w ↦ primeUnit (K := K) w ^ n w).Finite :=
    (Filter.eventually_cofinite.1 hn).subset fun w hw h ↦ hw (by simp only [h, zpow_zero])
  rw [← Units.coeHom_apply, map_finprod _ hfin]
  have e : ∏ᶠ w, (Units.coeHom (FractionalIdeal R⁰ K)) (primeUnit (K := K) w ^ n w) =
      ∏ᶠ w : HeightOneSpectrum R, (w.asIdeal : FractionalIdeal R⁰ K) ^ n w :=
    finprod_congr fun w ↦ by simp [primeUnit, Units.val_zpow_eq_zpow_val]
  rw [e, FractionalIdeal.count_finprod K v n hn]

theorem count_spanSingleton {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {a : K} (ha : a ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a) = -WithZero.log (v.valuation K a) := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at ha
  have hI : FractionalIdeal.spanSingleton R⁰ (algebraMap R K n / algebraMap R K d) =
      FractionalIdeal.spanSingleton R⁰ (algebraMap R K d)⁻¹ * ↑(Ideal.span {n} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton, div_eq_mul_inv,
      mul_comm]
  rw [FractionalIdeal.count_well_defined K v ((FractionalIdeal.spanSingleton_ne_zero_iff).2 ha) hI, map_div₀,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ hn0, HeightOneSpectrum.intValuation_if_neg _ hd0, ← WithZero.exp_sub,
    WithZero.log_exp]
  ring

theorem exists_rat_of_divisor (n : HeightOneSpectrum ℤ → ℤ) (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    ∃ Q : ℚ, Q ≠ 0 ∧ ∀ v : HeightOneSpectrum ℤ, -WithZero.log (v.valuation ℚ Q) = n v := by
  let J : (FractionalIdeal ℤ⁰ ℚ)ˣ := ∏ᶠ w, primeUnit (K := ℚ) w ^ n w
  let g : ℚ := Submodule.IsPrincipal.generator ((J : FractionalIdeal ℤ⁰ ℚ) : Submodule ℤ ℚ)
  have hJ : (J : FractionalIdeal ℤ⁰ ℚ) = FractionalIdeal.spanSingleton ℤ⁰ g := by
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [FractionalIdeal.coe_spanSingleton, Submodule.IsPrincipal.span_singleton_generator]
  have hg : g ≠ 0 := by
    intro h0
    apply J.ne_zero
    rw [hJ, h0, FractionalIdeal.spanSingleton_zero]
  refine ⟨g, hg, fun v => ?_⟩
  rw [← count_spanSingleton v hg, ← hJ, count_finprod_primeUnit n hn]

theorem exists_finset_divisor_cover (L : Type) [Field L] [NumberField L] :
    ∃ F : Finset (HeightOneSpectrum (𝓞 L) → ℤ), ∀ n : HeightOneSpectrum (𝓞 L) → ℤ,
      (∀ᶠ w in Filter.cofinite, n w = 0) → ∃ f ∈ F, ∃ z : L, z ≠ 0 ∧ ∀ w, n w = f w + ord w z := by
  classical
  have hsurj : Function.Surjective (ClassGroup.mk (R := 𝓞 L) L) := fun κ =>
    ClassGroup.induction L (P := fun κ => ∃ I, ClassGroup.mk L I = κ) (fun I => ⟨I, rfl⟩) κ
  let rep := Function.surjInv hsurj
  refine ⟨Finset.univ.image (fun κ w => FractionalIdeal.count L w ((rep κ : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    FractionalIdeal (𝓞 L)⁰ L)), fun n hn => ?_⟩
  let J : (FractionalIdeal (𝓞 L)⁰ L)ˣ := ∏ᶠ w, primeUnit (K := L) w ^ n w
  let J₀ := rep (ClassGroup.mk L J)
  have hJ₀ : ClassGroup.mk L J₀ = ClassGroup.mk L J := Function.surjInv_eq hsurj _
  have h1 : ClassGroup.mk L (J * J₀⁻¹) = 1 := by rw [map_mul, map_inv, hJ₀, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  let z : L := Submodule.IsPrincipal.generator (((J * J₀⁻¹ : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    FractionalIdeal (𝓞 L)⁰ L) : Submodule (𝓞 L) L)
  have hz : ((J * J₀⁻¹ : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) =
      FractionalIdeal.spanSingleton (𝓞 L)⁰ z := by
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [FractionalIdeal.coe_spanSingleton, Submodule.IsPrincipal.span_singleton_generator]
  have hz0 : z ≠ 0 := by
    intro h0
    apply (J * J₀⁻¹).ne_zero
    rw [hz, h0, FractionalIdeal.spanSingleton_zero]
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (ClassGroup.mk L J)), z, hz0, fun w => ?_⟩
  have hJ : (J : FractionalIdeal (𝓞 L)⁰ L) = FractionalIdeal.spanSingleton (𝓞 L)⁰ z * (J₀ : FractionalIdeal (𝓞 L)⁰ L) := by
    rw [← hz, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have e := congrArg (FractionalIdeal.count L w) hJ
  rw [count_finprod_primeUnit n hn, FractionalIdeal.count_mul L w
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hz0) J₀.ne_zero, count_spanSingleton w hz0] at e
  simp only [ord]
  rw [e]
  ring

theorem finite_valuation_ne_one (L : Type) [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    {w : HeightOneSpectrum (𝓞 L) | w.valuation L x ≠ 1}.Finite := by
  have h := FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 L)⁰ x)
  refine (Filter.eventually_cofinite.1 h).subset fun w hw h0 => hw ?_
  rw [count_spanSingleton w hx] at h0
  exact (ord_eq_zero_iff w hx).1 h0

theorem mem_under_iff (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (m : ℤ) :
    m ∈ (w.under ℤ).asIdeal ↔ w.valuation L (m : L) < 1 := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
  simp

theorem finite_under (L : Type) [Field L] [NumberField L] (T : Finset (HeightOneSpectrum ℤ)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under ℤ ∈ T}.Finite := by
  have h : ∀ v : HeightOneSpectrum ℤ, {w : HeightOneSpectrum (𝓞 L) | w.under ℤ = v}.Finite := by
    intro v
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have hm0' : (m : L) ≠ 0 := by exact_mod_cast hm0
    refine (finite_valuation_ne_one L hm0').subset fun w hw => ?_
    simp only [Set.mem_setOf_eq] at hw ⊢
    have := (mem_under_iff L w m).1 (by rw [hw]; exact hm)
    exact ne_of_lt this
  refine (Set.Finite.biUnion T.finite_toSet fun v _ => h v).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw
  exact Set.mem_biUnion hw rfl

def conjEquiv {L : Type} [Field L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) (hc : ∀ x, c (c x) = x) : L ≃ₐ[ℚ] L :=
  AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)

theorem valuation_conj (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (hc : ∀ x, c (c x) = x)
    (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    w.valuation L (c x) = (conjEquiv c hc • w).valuation L x := by
  have h := GroundTheory.Global.SemiLocal.valuation_smul (conjEquiv c hc) (conjEquiv c hc • w) x
  have e : conjEquiv c hc • conjEquiv c hc • w = w := by
    rw [smul_smul]
    have : conjEquiv c hc * conjEquiv c hc = 1 := AlgEquiv.ext hc
    rw [this, one_smul]
  rw [e] at h
  exact h

theorem under_conj (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (hc : ∀ x, c (c x) = x)
    (w : HeightOneSpectrum (𝓞 L)) : (conjEquiv c hc • w).under ℤ = w.under ℤ := by
  apply HeightOneSpectrum.ext
  ext m
  rw [mem_under_iff, mem_under_iff, ← valuation_conj L c hc, map_intCast]

theorem ord_conj (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (hc : ∀ x, c (c x) = x)
    (w : HeightOneSpectrum (𝓞 L)) (x : L) : ord w (c x) = ord (conjEquiv c hc • w) x := by
  simp only [ord, valuation_conj L c hc]

theorem valuation_rat_eq (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {Q q : ℚ}
    (h : (w.under ℤ).valuation ℚ Q = (w.under ℤ).valuation ℚ q) :
    w.valuation L (algebraMap ℚ L Q) = w.valuation L (algebraMap ℚ L q) := by
  haveI : w.asIdeal.LiesOver (w.under ℤ).asIdeal := ⟨HeightOneSpectrum.under_asIdeal ℤ w⟩
  rw [← HeightOneSpectrum.valuation_liesOver L (w.under ℤ) w Q, ← HeightOneSpectrum.valuation_liesOver L (w.under ℤ) w q, h]

theorem log_injective {x y : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : WithZero.log x = WithZero.log y) : x = y := by
  rw [← WithZero.exp_log hx, ← WithZero.exp_log hy, h]

theorem exists_finset_classes (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (hc : ∀ x, c (c x) = x)
    (S : Finset (HeightOneSpectrum ℤ)) (X : Set L)
    (hX : ∀ a ∈ X, a ≠ 0 ∧ c a = a ∧ ∀ v ∉ S, ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a =
            algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y)) :
    ∃ R : Finset L, ∀ a ∈ X, ∃ b ∈ R, ∃ (q : ℚ) (z : L), q ≠ 0 ∧ z ≠ 0 ∧
      a = algebraMap ℚ L q * b * (z * c z) := by
  classical
  let WS : Finset (HeightOneSpectrum (𝓞 L)) := (finite_under L S).toFinset
  obtain ⟨F, hF⟩ := exists_finset_divisor_cover L
  obtain ⟨S₆, hS₆⟩ := GlobalTheory.units_fixed_eq_mul_mul_conj L c hc
  let Φ : Finset (HeightOneSpectrum (𝓞 L) → ℤ) := (WS.powerset ×ˢ F).image
    (fun p w => (if w ∈ p.1 then 1 else 0) + p.2 w + p.2 (conjEquiv c hc • w))
  let P : (HeightOneSpectrum (𝓞 L) → ℤ) → L → Prop := fun φ b => b ≠ 0 ∧ c b = b ∧ ∀ w, ord w b = φ w
  let B : (HeightOneSpectrum (𝓞 L) → ℤ) → L := fun φ => if h : ∃ b, P φ b then h.choose else 1
  have hB : ∀ φ b, P φ b → P φ (B φ) := fun φ b hb => by
    have h : ∃ b, P φ b := ⟨b, hb⟩
    simp only [B, dif_pos h]
    exact h.choose_spec
  refine ⟨(Φ ×ˢ S₆).image (fun p => B p.1 * p.2), fun a ha => ?_⟩
  obtain ⟨ha0, hca, hloc⟩ := hX a ha
  have hl : ∀ v : HeightOneSpectrum ℤ, v ∉ S → ∃ (q : ℚ) (z : L), q ≠ 0 ∧ z ≠ 0 ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
        w.valuation L a = w.valuation L (algebraMap ℚ L q * (z * c z)) := by
    intro v hv
    obtain ⟨r, y, h⟩ := hloc v hv
    exact exists_local L c v a ha0 r y h
  choose! qv zv hqv hzv hval using hl
  have hTfin : ((fun w : HeightOneSpectrum (𝓞 L) => w.under ℤ) '' {w | w.valuation L a ≠ 1}).Finite :=
    (finite_valuation_ne_one L ha0).image _
  let T : Finset (HeightOneSpectrum ℤ) := hTfin.toFinset
  have hT : ∀ w : HeightOneSpectrum (𝓞 L), w.under ℤ ∉ T → w.valuation L a = 1 := by
    intro w hw
    by_contra h
    exact hw (hTfin.mem_toFinset.2 ⟨w, h, rfl⟩)
  let k : HeightOneSpectrum ℤ → ℤ := fun v =>
    if v ∈ T ∧ v ∉ S then -WithZero.log (v.valuation ℚ (qv v)) else 0
  have hk : ∀ᶠ v in Filter.cofinite, k v = 0 := by
    refine Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => ?_)
    by_contra h
    exact hv (if_neg (fun h' => h h'.1))
  obtain ⟨Q, hQ0, hQ⟩ := exists_rat_of_divisor k hk
  let n : HeightOneSpectrum (𝓞 L) → ℤ := fun w =>
    if w.under ℤ ∈ S then ord w a / 2 else if w.under ℤ ∈ T then ord w (zv (w.under ℤ)) else 0
  have hn : ∀ᶠ w in Filter.cofinite, n w = 0 := by
    refine Filter.eventually_cofinite.2 ((finite_under L (S ∪ T)).subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, Finset.mem_union] at hw ⊢
    by_contra h
    push_neg at h
    exact hw (by simp only [n, if_neg h.1, if_neg h.2])
  obtain ⟨f, hfF, z₁, hz₁, hnf⟩ := hF n hn
  let Δ : Finset (HeightOneSpectrum (𝓞 L)) := WS.filter (fun w => ord w a % 2 = 1)
  let φ : HeightOneSpectrum (𝓞 L) → ℤ := fun w => (if w ∈ Δ then 1 else 0) + f w + f (conjEquiv c hc • w)
  have hφ : φ ∈ Φ := Finset.mem_image.2 ⟨(Δ, f), Finset.mem_product.2
    ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), hfF⟩, rfl⟩
  have hQw : ∀ w : HeightOneSpectrum (𝓞 L), ord w (algebraMap ℚ L Q) =
      if w.under ℤ ∈ T ∧ w.under ℤ ∉ S then ord w (algebraMap ℚ L (qv (w.under ℤ))) else 0 := by
    intro w
    have h := hQ (w.under ℤ)
    simp only [k] at h
    split_ifs with hc'
    · rw [if_pos hc'] at h
      have hq0 := hqv _ hc'.2
      have e : (w.under ℤ).valuation ℚ Q = (w.under ℤ).valuation ℚ (qv (w.under ℤ)) :=
        log_injective ((Valuation.ne_zero_iff _).2 hQ0) ((Valuation.ne_zero_iff _).2 hq0) (by omega)
      simp only [ord, valuation_rat_eq L w e]
    · rw [if_neg hc'] at h
      have e : (w.under ℤ).valuation ℚ Q = (w.under ℤ).valuation ℚ 1 := by
        rw [map_one]
        exact log_injective ((Valuation.ne_zero_iff _).2 hQ0) one_ne_zero (by rw [WithZero.log_one]; omega)
      simp only [ord, valuation_rat_eq L w e, map_one, WithZero.log_one, neg_zero]
  have hQ0' : algebraMap ℚ L Q ≠ 0 := by simpa using hQ0
  have hkey : ∀ w : HeightOneSpectrum (𝓞 L), ord w a = ord w (algebraMap ℚ L Q) + n w +
      n (conjEquiv c hc • w) + (if w ∈ Δ then 1 else 0) := by
    intro w
    have hu := under_conj L c hc w
    have hσa : ord (conjEquiv c hc • w) a = ord w a := by rw [← ord_conj L c hc, hca]
    rw [hQw w]
    by_cases hS : w.under ℤ ∈ S
    · have hWS : w ∈ WS := (finite_under L S).mem_toFinset.2 hS
      rw [if_neg (fun h => h.2 hS)]
      simp only [n, hu, if_pos hS, hσa, Δ, Finset.mem_filter, hWS, true_and, not_true, and_false, if_false]
      split_ifs with h2 <;> omega
    · have hnWS : w ∉ Δ := fun h => hS ((finite_under L S).mem_toFinset.1 (Finset.mem_filter.1 h).1)
      by_cases hT' : w.under ℤ ∈ T
      · haveI : w.asIdeal.LiesOver (w.under ℤ).asIdeal := ⟨HeightOneSpectrum.under_asIdeal ℤ w⟩
        have hv := hval (w.under ℤ) hS w inferInstance
        have hq0 : algebraMap ℚ L (qv (w.under ℤ)) ≠ 0 := by simpa using hqv _ hS
        have hz0 := hzv _ hS
        have hcz0 : c (zv (w.under ℤ)) ≠ 0 := fun h => hz0 (by rw [← hc (zv _), h, map_zero])
        have e : ord w a = ord w (algebraMap ℚ L (qv (w.under ℤ))) + ord w (zv (w.under ℤ)) +
            ord w (c (zv (w.under ℤ))) := by
          simp only [ord] at *
          rw [hv, map_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hq0)
            (mul_ne_zero ((Valuation.ne_zero_iff _).2 hz0) ((Valuation.ne_zero_iff _).2 hcz0)),
            WithZero.log_mul ((Valuation.ne_zero_iff _).2 hz0) ((Valuation.ne_zero_iff _).2 hcz0)]
          ring
        rw [e, ord_conj L c hc, if_pos ⟨hT', hS⟩]
        simp only [n, hu, if_neg hS, if_pos hT', hnWS, if_false, hT', not_false_eq_true, and_self, if_true]
        ring
      · have h1 := hT w hT'
        have e : ord w a = 0 := (ord_eq_zero_iff w ha0).2 h1
        rw [if_neg (fun h => hT' h.1)]
        simp only [n, hu, if_neg hS, if_neg hT', hnWS, if_false, e]
        ring

  have hcz₁ : c z₁ ≠ 0 := fun h => hz₁ (by rw [← hc z₁, h, map_zero])
  have hden : algebraMap ℚ L Q * (z₁ * c z₁) ≠ 0 := mul_ne_zero hQ0' (mul_ne_zero hz₁ hcz₁)
  set b : L := a / (algebraMap ℚ L Q * (z₁ * c z₁)) with hbdef
  have hb0 : b ≠ 0 := div_ne_zero ha0 hden
  have hab : a = b * (algebraMap ℚ L Q * (z₁ * c z₁)) := by rw [hbdef, div_mul_cancel₀ _ hden]
  have hPb : P φ b := by
    refine ⟨hb0, ?_, fun w => ?_⟩
    · rw [hbdef, map_div₀, map_mul, map_mul, hca, hc, AlgHom.commutes, mul_comm (c z₁) z₁]
    · have e := hkey w
      rw [hab, ord_mul w hb0 hden, ord_mul w hQ0' (mul_ne_zero hz₁ hcz₁), ord_mul w hz₁ hcz₁,
        ord_conj L c hc, hnf w, hnf (conjEquiv c hc • w)] at e
      simp only [φ]
      linarith
  obtain ⟨hb₀0, hcb₀, hordb₀⟩ := hB φ b hPb

  set ε : L := b / B φ with hεdef
  have hε0 : ε ≠ 0 := div_ne_zero hb0 hb₀0
  have hεv : ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L ε = 1 := by
    intro w
    rw [← ord_eq_zero_iff w hε0]
    have e : b = ε * B φ := by rw [hεdef, div_mul_cancel₀ _ hb₀0]
    have e2 := congrArg (ord w) e
    rw [ord_mul w hε0 hb₀0, hPb.2.2 w, hordb₀ w] at e2
    linarith
  let εu : Lˣ := Units.mk0 ε hε0
  have hint : ∀ x : L, (∀ w : HeightOneSpectrum (𝓞 L), w.valuation L x = 1) → IsIntegral ℤ x := by
    intro x hx
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L x (fun w => (hx w).le)
    rw [← hy]
    exact y.isIntegral_coe
  have hε1 : IsIntegral ℤ (εu : L) := hint ε hεv
  have hε2 : IsIntegral ℤ ((εu⁻¹ : Lˣ) : L) := by
    refine hint _ fun w => ?_
    simp only [εu, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hεv w, inv_one]
  have hεc : c (εu : L) = εu := by
    simp only [εu, Units.val_mk0, hεdef, map_div₀, hPb.2.1, hcb₀]
  obtain ⟨f₆, hf₆, η, -, -, hεf⟩ := hS₆ εu hε1 hε2 hεc
  refine ⟨B φ * f₆, Finset.mem_image.2 ⟨(φ, f₆), Finset.mem_product.2 ⟨hφ, hf₆⟩, rfl⟩, Q, z₁ * η, hQ0,
    mul_ne_zero hz₁ η.ne_zero, ?_⟩
  have hε' : ε = f₆ * ((η : L) * c η) := hεf
  have hb' : b = ε * B φ := by rw [hεdef, div_mul_cancel₀ _ hb₀0]
  rw [hab, hb', hε', map_mul]
  ring

theorem finite_classes_mod_rat_norms : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∀ (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) (X : Set L),
    (∀ a ∈ X, a ≠ 0 ∧ c a = a ∧ ∀ v ∉ S, ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y)) →
    ∃ R : Finset L, ∀ a ∈ X, ∃ b ∈ R, ∃ (q : ℚ) (z : L), q ≠ 0 ∧ z ≠ 0 ∧ a = algebraMap ℚ L q * b * (z * c z) :=
  fun L _ _ c hc S X hX => exists_finset_classes L c hc S X hX

end GlobalTheory.FixedNormCls
