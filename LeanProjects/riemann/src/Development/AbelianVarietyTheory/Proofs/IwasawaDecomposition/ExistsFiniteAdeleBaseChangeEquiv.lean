import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFiniteAdeleCompleteSeparated
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV Formalism.UG Formalism.UG.P
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_locMap (F : Type) [Field F] [NumberField F] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) :
    ∃ φ : (P.under (𝓞 F)).adicCompletion F →+* P.adicCompletion E,
      (∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ (n : ℕ) (a : (P.under (𝓞 F)).adicCompletion F), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
        Valued.v (φ a) ≤ WithZero.exp (-(n : ℤ)) := by
  have : P.asIdeal.LiesOver (P.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E (P.under (𝓞 F))
    P).continuous
  let φ : (P.under (𝓞 F)).adicCompletion F →+* P.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E P).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv F (P.under (𝓞 F))).toRingHom
  have hφ : ∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E P).comp
      ((UniformSpace.Completion.continuous_map (f := algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion F (P.under (𝓞 F))))
  refine ⟨φ, hφ, fun n a ha => ?_⟩
  have hd : Dense (Set.range (algebraMap F ((P.under (𝓞 F)).adicCompletion F))) :=
    HeightOneSpectrum.denseRange_algebraMap (K := F) (P.under (𝓞 F))
  have h1 := hd.open_subset_closure_inter
    (GlobalTheory.Idele.isOpen_valued_le (K := F) (P.under (𝓞 F)) (-(n : ℤ))) ha
  have hcl := (GlobalTheory.Idele.isClosed_valued_le (K := E) P (-(n : ℤ))).preimage hcont
  refine closure_minimal ?_ hcl h1
  rintro _ ⟨hx, x, rfl⟩
  change Valued.v (φ _) ≤ _
  replace hx : Valued.v (algebraMap F ((P.under (𝓞 F)).adicCompletion F) x) ≤ _ := hx
  rw [hφ, levelaf_valued_algebraMap]
  rw [levelaf_valued_algebraMap] at hx
  obtain ⟨e, he, h⟩ := (GlobalTheory.QNorm.places_over F E).2.2 P
  rw [h]
  refine le_trans ?_ hx
  refine pow_le_of_le_one zero_le' (hx.trans ?_) he.ne'
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

variable (F) in

def locMap (P : HeightOneSpectrum (𝓞 E)) :
    (P.under (𝓞 F)).adicCompletion F →+* P.adicCompletion E := (exists_locMap F P).choose

theorem locMap_algebraMap (P : HeightOneSpectrum (𝓞 E)) (x : F) :
    locMap F P (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) :=
  (exists_locMap F P).choose_spec.1 x

theorem locMap_valued (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (a : (P.under (𝓞 F)).adicCompletion F)
    (ha : Valued.v a ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (locMap F P a) ≤ WithZero.exp (-(n : ℤ)) :=
  (exists_locMap F P).choose_spec.2 n a ha

theorem locMap_int (P : HeightOneSpectrum (𝓞 E)) (a : (P.under (𝓞 F)).adicCompletion F)
    (ha : a ∈ (P.under (𝓞 F)).adicCompletionIntegers F) :
    locMap F P a ∈ P.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
  simpa using locMap_valued P 0 a (by simpa using ha)

variable (F E) in

def adMap : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E where
  toFun a := ⟨fun P => locMap F P (a (P.under (𝓞 F))), by
    have h : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
      Filter.eventually_cofinite.1 a.2
    refine Filter.eventually_cofinite.2 ((h.biUnion
      (fun v _ => GlobalTheory.QNorm.finite_places_over F E v)).subset fun P hP => ?_)
    simp only [Set.mem_iUnion]
    exact ⟨P.under (𝓞 F), fun hh => hP (locMap_int P _ hh), rfl⟩⟩
  map_one' := FiniteAdeleRing.ext _ fun P => map_one (locMap F P)
  map_mul' a b := FiniteAdeleRing.ext _ fun P => map_mul (locMap F P) _ _
  map_zero' := FiniteAdeleRing.ext _ fun P => map_zero (locMap F P)
  map_add' a b := FiniteAdeleRing.ext _ fun P => map_add (locMap F P) _ _

theorem adMap_apply (a : FiniteAdeleRing (𝓞 F) F) (P : HeightOneSpectrum (𝓞 E)) :
    adMap F E a P = locMap F P (a (P.under (𝓞 F))) := rfl

theorem adMap_algebraMap (x : F) :
    adMap F E (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) :=
  FiniteAdeleRing.ext _ fun P => locMap_algebraMap P x

theorem adMap_int {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ intAd F) : adMap F E a ∈ intAd E :=
  fun P => locMap_int P _ (ha _)

variable (F E) in
theorem exists_toAd : ∃ ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E,
    ∀ x a, ι (x ⊗ₜ[F] a) = algebraMap E _ x * adMap F E a := by
  letI : Algebra F (FiniteAdeleRing (𝓞 E) E) :=
    ((algebraMap E (FiniteAdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] FiniteAdeleRing (𝓞 E) E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : FiniteAdeleRing (𝓞 F) F →ₐ[F] FiniteAdeleRing (𝓞 E) E :=
    ⟨adMap F E, fun x => adMap_algebraMap x⟩
  exact ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun x a => rfl⟩

theorem exists_nat_mul_integral {K : Type} [Field K] [NumberField K] (s : Finset K) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ s, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = D • x := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := K) s
  refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), fun x hx => ?_⟩
  have hi : IsIntegral ℤ ((y * y).natAbs • x) := by
    rw [← natCast_zsmul, Int.natAbs_of_nonneg (mul_self_nonneg y), mul_smul]
    exact (h x hx).smul y
  exact ⟨⟨_, hi⟩, rfl⟩

theorem exists_int_of_mem {K : Type} [Field K] [NumberField K] {x : K}
    (hx : algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ intAd K) :
    ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = x := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K x fun v => ?_
  rw [← levelaf_valued_algebraMap]
  exact hx v

theorem algebraMap_int_mem {K : Type} [Field K] [NumberField K] (r : 𝓞 K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K r) ∈ intAd K :=
  levelaf_int_mem r

theorem exists_approx (y : AfE F E) : ∃ x : E, ∃ r ∈ RInt F E, y = x ⊗ₜ[F] 1 + r := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add y y' hy hy' =>
    obtain ⟨x, r, hr, rfl⟩ := hy
    obtain ⟨x', r', hr', rfl⟩ := hy'
    exact ⟨x + x', r + r', add_mem hr hr', by rw [TensorProduct.add_tmul]; abel⟩
  | tmul e a =>
    obtain ⟨m, hm, h⟩ := exists_nat_mul_integral ({e} : Finset E)
    obtain ⟨o, ho⟩ := h e (Finset.mem_singleton_self e)
    obtain ⟨k, a', ha', rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F m hm).1 a
    refine ⟨k • e, _, levelaf_tmul_mem o ha', ?_⟩
    rw [TensorProduct.tmul_add, ho, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]

def coord (i : Fin (Module.finrank F E)) : AfE F E →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
  (TensorProduct.lid F _).toLinearMap ∘ₗ LinearMap.rTensor _ ((Module.finBasis F E).coord i)

theorem coord_tmul (i : Fin (Module.finrank F E)) (x : E) (a : FiniteAdeleRing (𝓞 F) F) :
    coord i (x ⊗ₜ[F] a) = (Module.finBasis F E).repr x i • a := by
  simp [coord]

theorem sum_coord (y : AfE F E) : ∑ i, Module.finBasis F E i ⊗ₜ[F] coord i y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hy']
  | tmul x a =>
    simp only [coord_tmul, ← TensorProduct.smul_tmul]
    rw [← TensorProduct.sum_tmul, Module.Basis.sum_repr]

variable (F E) in
theorem exists_coord_denom : ∃ D : ℕ, 0 < D ∧ ∀ y ∈ RInt F E, ∀ i, D • coord i y ∈ intAd F := by
  classical
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨D, hD, h⟩ := exists_nat_mul_integral (Finset.univ.image
    fun p : Fin m × Fin (Module.finrank F E) =>
      (Module.finBasis F E).repr (algebraMap (𝓞 E) E (g p.1)) p.2)
  refine ⟨D, hD, fun y hy i => ?_⟩
  obtain ⟨r, hr, rfl⟩ := levelaf_decomp g hg hy
  rw [map_sum, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  obtain ⟨o, ho⟩ := h _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, i)))
  rw [coord_tmul, ← smul_assoc, ← ho, Algebra.smul_def]
  exact mul_mem (algebraMap_int_mem o) (hr j)

theorem eq_zero_of_nsmul_eq_zero {K A : Type} [Field K] [CharZero K] [AddCommGroup A] [Module K A]
    {D : ℕ} (hD : 0 < D) {a : A} (h : D • a = 0) : a = 0 := by
  rw [← Nat.cast_smul_eq_nsmul K] at h
  exact (smul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hD.ne')

theorem eq_zero_of_divisible (y : AfE F E)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ RInt F E, y = N • w) : y = 0 := by
  obtain ⟨D, hD, hc⟩ := exists_coord_denom F E
  rw [← sum_coord y]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : D • coord i y = 0 := by
    refine (GlobalTheory.AdLat.integral_finiteAdele_complete_separated F).1 _ fun N hN => ?_
    obtain ⟨w, hw, rfl⟩ := h N hN
    exact ⟨_, hc w hw i, by rw [map_nsmul, smul_comm]⟩
  rw [eq_zero_of_nsmul_eq_zero (K := F) hD this, TensorProduct.tmul_zero]

theorem exists_limit (x : ℕ → AfE F E) (hx : ∀ N, x N ∈ RInt F E)
    (h : ∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ RInt F E, x (N * m) = x N + N • w) :
    ∃ D : ℕ, 0 < D ∧ ∃ y : AfE F E, ∀ N : ℕ, 0 < N → ∃ w ∈ RInt F E, y = D • x N + N • w := by
  classical
  obtain ⟨D, hD, hc⟩ := exists_coord_denom F E
  obtain ⟨M, hM, hb⟩ := exists_nat_mul_integral (Finset.univ.image (Module.finBasis F E))
  choose o ho using fun i => hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have key : ∀ i, ∃ y : FiniteAdeleRing (𝓞 F) F, ∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = D • coord i (x N) + N • a := by
    intro i
    refine (GlobalTheory.AdLat.integral_finiteAdele_complete_separated F).2 (fun N => D • coord i (x N))
      (fun N => hc _ (hx N) i) fun N k hN hk => ?_
    obtain ⟨w, hw, e⟩ := h N k hN hk
    exact ⟨_, hc w hw i, by rw [e, map_add, map_nsmul, smul_add, smul_comm D N]⟩
  choose y hy using key
  refine ⟨M * D, Nat.mul_pos hM hD, ∑ i, algebraMap (𝓞 E) E (o i) ⊗ₜ[F] y i, fun N hN => ?_⟩
  choose a ha hya using fun i => hy i N hN
  refine ⟨∑ i, algebraMap (𝓞 E) E (o i) ⊗ₜ[F] a i,
    sum_mem fun i _ => levelaf_tmul_mem _ (ha i), ?_⟩
  conv_rhs => rw [← sum_coord (x N)]
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hya i, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ho,
    ← TensorProduct.smul_tmul', smul_smul, mul_comm D M]

section
variable {ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E}
  (hι : ∀ x a, ι (x ⊗ₜ[F] a) = algebraMap E _ x * adMap F E a)
include hι

theorem map_tmul_one (x : E) : ι (x ⊗ₜ[F] 1) = algebraMap E _ x := by
  rw [hι, map_one, mul_one]

theorem map_mem_int {y : AfE F E} (hy : y ∈ RInt F E) : ι y ∈ intAd E := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨r, hr, rfl⟩ := levelaf_decomp g hg hy
  rw [map_sum]
  refine sum_mem fun j _ => ?_
  rw [hι]
  exact mul_mem (algebraMap_int_mem _) (adMap_int (hr j))

theorem mem_int_of_map {y : AfE F E} (hy : ι y ∈ intAd E) : y ∈ RInt F E := by
  obtain ⟨x, r, hr, rfl⟩ := exists_approx y
  rw [map_add, map_tmul_one hι] at hy
  have h1 := sub_mem hy (map_mem_int hι hr)
  rw [add_sub_cancel_right] at h1
  obtain ⟨o, rfl⟩ := exists_int_of_mem h1
  exact add_mem (levelaf_tmul_mem o (one_mem _)) hr

theorem map_injective : Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  refine eq_zero_of_divisible y fun N hN => ⟨(N : E)⁻¹ ⊗ₜ[F] 1 * y, mem_int_of_map hι ?_, ?_⟩
  · rw [map_mul, hy, mul_zero]; exact zero_mem _
  · rw [← smul_mul_assoc, TensorProduct.smul_tmul', nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), ← Algebra.TensorProduct.one_def, one_mul]

theorem exists_map_eq_of_int {s : FiniteAdeleRing (𝓞 E) E} (hs : s ∈ intAd E) : ∃ y, ι y = s := by
  have h0 : ∀ N : ℕ, ∃ (x : 𝓞 E) (a : FiniteAdeleRing (𝓞 E) E), a ∈ intAd E ∧
      (0 < N → s = algebraMap E _ (algebraMap (𝓞 E) E x) + N • a) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0, 0, zero_mem _, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨x, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E N hN).2 s hs
      exact ⟨x, a, ha, fun _ => e⟩
  choose x a ha hxa using h0
  have hinv : ∀ N : ℕ, 0 < N → ∀ z : FiniteAdeleRing (𝓞 E) E,
      algebraMap E _ (N : E)⁻¹ * (N • z) = z := by
    intro N hN z
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)),
      ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one, one_mul]
  obtain ⟨D, hD, y, hy⟩ := exists_limit (F := F)
    (fun N => algebraMap (𝓞 E) E (x N) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
    (fun N => levelaf_tmul_mem _ (one_mem _)) (fun N m hN hm => by
      have e1 := hxa N hN
      have e2 := hxa (N * m) (Nat.mul_pos hN hm)
      have e3 : algebraMap E (FiniteAdeleRing (𝓞 E) E) ((N : E)⁻¹ *
          (algebraMap (𝓞 E) E (x (N * m)) - algebraMap (𝓞 E) E (x N))) = a N - m • a (N * m) := by
        rw [map_mul, ← hinv N hN (a N - m • a (N * m)), map_sub]
        congr 1
        rw [smul_sub, smul_smul]
        linear_combination e1 - e2
      obtain ⟨o, ho⟩ := exists_int_of_mem (e3 ▸ sub_mem (ha N) (nsmul_mem (ha (N * m)) m))
      refine ⟨_, levelaf_tmul_mem o (one_mem _), ?_⟩
      rw [TensorProduct.smul_tmul', ← TensorProduct.add_tmul, ho, nsmul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), one_mul, add_sub_cancel])
  have hz : ι y - D • s = 0 := by
    refine (GlobalTheory.AdLat.integral_finiteAdele_complete_separated E).1 _ fun N hN => ?_
    obtain ⟨w, hw, e⟩ := hy N hN
    refine ⟨ι w - D • a N, sub_mem (map_mem_int hι hw) (nsmul_mem (ha N) D), ?_⟩
    rw [e, map_add, map_nsmul, map_nsmul, map_tmul_one hι]
    conv_lhs => rw [hxa N hN]
    rw [smul_add, smul_sub, smul_comm D N]
    abel
  refine ⟨(D : E)⁻¹ ⊗ₜ[F] 1 * y, ?_⟩
  rw [map_mul, map_tmul_one hι, sub_eq_zero.1 hz, hinv D hD]

theorem map_surjective : Function.Surjective ι := by
  intro z
  obtain ⟨x, a, ha, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E 1 one_pos).1 z
  obtain ⟨y, rfl⟩ := exists_map_eq_of_int hι ha
  exact ⟨x ⊗ₜ[F] 1 + y, by rw [map_add, map_tmul_one hι, one_smul]⟩

theorem map_eps_mul_apply (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E)
    (P : HeightOneSpectrum (𝓞 E)) :
    ι (afsplitEps E v * z) P = locMap F P (afsplitI v 1 (P.under (𝓞 F))) * ι z P := by
  rw [map_mul, afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul, hι, map_one, one_mul]
  rfl

theorem prV_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E) :
    prV (E := E) v z = 0 ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → ι z P = 0 := by
  constructor
  · intro h P hP
    subst hP
    have h1 := map_eps_mul_apply hι (P.under (𝓞 F)) z P
    rw [← afsplit_decomp, h, map_zero, map_zero, afsplitI_self, map_one, one_mul] at h1
    exact h1.symm
  · intro h
    have h1 : afsplitEps E v * z = 0 := by
      apply map_injective hι
      rw [map_zero]
      refine FiniteAdeleRing.ext _ fun P => ?_
      rw [map_eps_mul_apply hι]
      by_cases hP : P.under (𝓞 F) = v
      · rw [h P hP, mul_zero]; rfl
      · rw [afsplitI_ne v _ hP, map_zero, zero_mul]; rfl
    rw [← afsplit_prV_IE v (prV (E := E) v z), afsplit_decomp, h1, map_zero]

theorem prV_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E) :
    prV (E := E) v z = 1 ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → ι z P = 1 := by
  rw [← sub_eq_zero, ← map_one (prV (E := E) v), ← map_sub, prV_eq_zero_iff hι]
  refine forall_congr' fun P => imp_congr_right fun _ => ?_
  rw [map_sub, map_one, afsplit_sub_apply, afsplit_one_apply, sub_eq_zero]

end

theorem exists_finiteAdele_baseChange_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E, (∀ x : E, ι (x ⊗ₜ[F] 1) = algebraMap E _ x) ∧ (∀ y, y ∈ RInt F E ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι y P) ≤ 1) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (y : (AfE F E)ˣ), y ∈ suppAt E v ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ≠ v → ι (y : AfE F E) P = 1) ∧ ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ), Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) := by
  intro F E _ _ _ _ _
  obtain ⟨ι, hι⟩ := exists_toAd F E
  refine ⟨RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩, map_tmul_one hι,
    fun y => ⟨fun hy => map_mem_int hι hy, fun hy => mem_int_of_map hι hy⟩, fun v y => ?_,
    fun a k P n h => ?_⟩
  · have h1 : y ∈ suppAt E v ↔ ∀ v', v' ≠ v → prV (E := E) v' (y : AfE F E) = 1 := by
      simp only [suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]
      rfl
    rw [h1]
    simp only [prV_eq_one_iff hι]
    exact ⟨fun h P hP => h _ hP P rfl, fun h v' hv P hP => h P (hP ▸ hv)⟩
  · change Valued.v (ι (1 ⊗ₜ[F] a) P - _) ≤ _
    rw [hι, map_one, one_mul, adMap_apply, ← locMap_algebraMap, ← map_sub]
    exact locMap_valued P n _ h

end GlobalTheory.AdeleBaseChange
