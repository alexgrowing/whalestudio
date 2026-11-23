import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticesIdempotentPositionBoundedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeIdempotentPositionInvolutionStableStatement

noncomputable section
namespace GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Classical

theorem isIntegral_trace_of_isIntegral'
    (U L Ω : Type) [CommRing U] [Field L] [CommRing Ω] [Algebra U L] [Algebra L Ω] [Algebra U Ω]
    [IsScalarTower U L Ω] [Module.Finite L Ω] (ω : Ω) (h : IsIntegral U ω) :
    IsIntegral U (Algebra.trace L Ω ω) := by
  classical
  let b := Module.finBasis L Ω
  let A := AlgebraicClosure L
  let f : Ω →ₐ[U] Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A :=
    (((Algebra.ofId L A).mapMatrix).comp (Algebra.leftMulMatrix b)).restrictScalars U
  have hM : IsIntegral U (f ω) := h.map f
  have htr : algebraMap L A (Algebra.trace L Ω ω) = (f ω).trace := by
    rw [Algebra.trace_eq_matrix_trace b]
    simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := L) (B := A) (algebraMap L A).injective, htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (f ω).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum A (f ω) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (f ω) (p.map (algebraMap U A)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (f ω) (p.map (algebraMap U A)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

variable {K : UQ} (B : InvAlg K)

theorem trace_mem_of_isIntegral (x : B.A) (hx : IsIntegral K.O x) :
    Algebra.trace K.E B.A x ∈ (algebraMap K.O K.E).range :=
  IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_trace_of_isIntegral' K.O K.E B.A x hx)

theorem trace_idem_ne_zero (e : B.A) (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    Algebra.trace K.E B.A e ≠ 0 := by
  rw [Algebra.trace_apply]
  have hid : IsIdempotentElem (Algebra.lmul K.E B.A e) := by
    unfold IsIdempotentElem; ext y; simp [← mul_assoc, he.eq]
  intro h
  have := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hid).1 h
  apply h0
  have h1 := LinearMap.congr_fun this 1
  simpa using h1

theorem exists_lb (a : K.O) (ha : K.Small a) (T : K.E) (hT : T ≠ 0) :
    ∃ L : ℤ, ∀ n : ℤ, al K a ^ n * T ∈ (algebraMap K.O K.E).range → L ≤ n := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := K.O) T
  have hy0 : algebraMap K.O K.E y ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hT
  have hα : al K a ≠ 0 := by
    simpa [al] using (IsFractionRing.injective K.O K.E).ne ha.1
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal K.O)
    (IsLocalRing.maximalIdeal.isMaximal K.O).ne_top
  obtain ⟨m0, hm0⟩ : ∃ m : ℕ, x ∉ IsLocalRing.maximalIdeal K.O ^ m := by
    by_contra h
    push_neg at h
    apply hx0
    rw [← Ideal.mem_bot, ← hinf, Ideal.mem_iInf]
    exact h
  refine ⟨1 - m0, fun n hn => ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat (show n ≤ 0 by omega)
  obtain ⟨o, ho⟩ := hn
  have hinv : al K a ^ (-(m : ℤ)) * al K a ^ m = 1 := by
    rw [zpow_neg, zpow_natCast]; exact inv_mul_cancel₀ (pow_ne_zero _ hα)
  have hxe : algebraMap K.O K.E x = algebraMap K.O K.E (o * y * a ^ m) := by
    rw [map_mul, map_mul, ho, map_pow]
    have e1 : al K a ^ (-(m : ℤ)) * (algebraMap K.O K.E x / algebraMap K.O K.E y) * algebraMap K.O K.E y *
        al K a ^ m = (al K a ^ (-(m : ℤ)) * al K a ^ m) * algebraMap K.O K.E x := by
      field_simp
    simp only [al] at e1 hinv ⊢
    rw [e1, hinv, one_mul]
  have hxm : x = o * y * a ^ m := IsFractionRing.injective K.O K.E hxe
  apply hm0
  have : x ∈ IsLocalRing.maximalIdeal K.O ^ m := by
    rw [hxm]; exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow ha.2.1 m)
  exact Ideal.pow_le_pow_right (by omega) this

theorem exists_int_mul (a : K.O) (ha : K.Small a) (y : B.A) :
    ∃ c : ℕ, IsIntegral K.O (al K a ^ (c : ℤ) • y) := by
  have hyE : IsIntegral K.E y := Algebra.IsIntegral.isIntegral y
  obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors K.O) (Rₘ := K.E) y hyE
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨n, u, hmu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hm0 hϖ
  have ha' : a ∈ Ideal.span {ϖ} := hϖ.maximalIdeal_eq ▸ ha.2.1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 ha'
  refine ⟨n, ?_⟩
  have hc : a ^ n = (((u⁻¹ : K.Oˣ) : K.O) * b ^ n) * m := by
    rw [hmu, ← hb, mul_pow]
    calc b ^ n * ϖ ^ n = ((u⁻¹ : K.Oˣ) : K.O) * u * (b ^ n * ϖ ^ n) := by simp
      _ = _ := by ring
  have h1 : al K a ^ (n : ℤ) • y = (((u⁻¹ : K.Oˣ) : K.O) * b ^ n) • (m • y) := by
    rw [zpow_natCast, smul_smul, ← hc]
    simp only [al, ← map_pow, algebraMap_smul]
  have h2 : (m • y) = (⟨m, hm⟩ : nonZeroDivisors K.O) • y := rfl
  rw [h1, Algebra.smul_def, h2]
  exact (isIntegral_algebraMap).mul hmi

end GlobalTheory.UnitLemma.Desc

noncomputable section
namespace GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Classical

variable {K : UQ} (B : InvAlg K)

theorem exists_ub (a : K.O) (ha : K.Small a) (e : B.A) (he : IsIdempotentElem e) (he0 : e ≠ 0)
    (y : B.A) : ∃ H : ℤ, IsUnit y → ∀ n : ℤ, IsIntegral K.O (al K a ^ (-n) • (e * y)) → n ≤ H := by
  by_cases hy : IsUnit y
  swap
  · exact ⟨0, fun h => absurd h hy⟩
  have hα : al K a ≠ 0 := by
    simpa [al] using (IsFractionRing.injective K.O K.E).ne ha.1
  obtain ⟨w, hw⟩ := hy.exists_right_inv
  obtain ⟨c, hc⟩ := exists_int_mul B a ha w
  obtain ⟨L, hL⟩ := exists_lb a ha _ (trace_idem_ne_zero B e he he0)
  refine ⟨c - L, fun _ n hn => ?_⟩
  have hi := hn.mul hc
  have heq : al K a ^ (-n) • (e * y) * (al K a ^ (c : ℤ) • w) = al K a ^ (-n + c) • e := by
    rw [smul_mul_smul_comm, mul_assoc, hw, mul_one, ← zpow_add₀ hα]
  rw [heq] at hi
  have ht := trace_mem_of_isIntegral B _ hi
  rw [map_smul, smul_eq_mul] at ht
  have := hL _ ht
  omega

theorem exists_lb' (a : K.O) (ha : K.Small a) (e : B.A) (he : IsIdempotentElem e) (he0 : e ≠ 0) (N : ℕ)
    (s : B.A) : ∃ L0 : ℤ, IsUnit s → ∀ (M : Submodule K.O B.A) (n : ℤ),
      (∀ r : B.A, IsIntegral K.O r → al K a ^ (n + N) • (e * r) ∈ M) → InDual B s M → L0 ≤ n := by
  by_cases hs : IsUnit s
  swap
  · exact ⟨0, fun h => absurd h hs⟩
  have hα : al K a ≠ 0 := by
    simpa [al] using (IsFractionRing.injective K.O K.E).ne ha.1
  obtain ⟨w, hw⟩ := hs.exists_right_inv
  obtain ⟨c, hc⟩ := exists_int_mul B a ha w
  obtain ⟨L, hL⟩ := exists_lb a ha _ (trace_idem_ne_zero B e he he0)
  refine ⟨L - N - c, fun _ M n hM hD => ?_⟩
  have hz := hD _ (hM _ hc)
  have heq : s * (al K a ^ (n + N) • (e * (al K a ^ (c : ℤ) • w))) = al K a ^ (n + N + c) • e := by
    rw [mul_smul_comm, mul_smul_comm, mul_smul_comm, smul_smul, ← zpow_add₀ hα, mul_left_comm, hw, mul_one]
  rw [heq, map_smul, smul_eq_mul] at hz
  have := hL _ hz
  omega

theorem small_card (K : UQ) : K.Small (Nat.card (IsLocalRing.ResidueField K.O) : K.O) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h' : ((Nat.card (IsLocalRing.ResidueField K.O) : ℕ) : K.E) = 0 := by
      rw [← map_natCast (algebraMap K.O K.E), h, map_zero]
    rw [Nat.cast_eq_zero] at h'
    exact (Nat.card_pos (α := IsLocalRing.ResidueField K.O)).ne' h'
  · rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    haveI := Fintype.ofFinite (IsLocalRing.ResidueField K.O)
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  · rw [map_natCast, map_natCast]

theorem finite_term_ne_zero : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι),
    B.P.Separable → IsFrame B e π S → ∀ (I I' : Finset ι), I ⊆ S → I' ⊆ S → ∀ u s : B.A, IsUnit u → IsUnit s →
    {M ∈ B.Lin | term B π I I' u s M ≠ 0}.Finite := by
  intro K B ι _ e π S hsep hF I I' hI hI' u s hu hs
  set a : K.O := (Nat.card (IsLocalRing.ResidueField K.O) : K.O)
  have ha : K.Small a := small_card K
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_lattice_idempotent_position_involution_stable K B ι e π S a hsep ha hF
  obtain ⟨C, hC⟩ := GlobalTheory.T.card_lattices_idempotent_position_bounded K B ι e π S a hsep ha hF N
  have he : ∀ i, IsIdempotentElem (e i) := fun i => hF.1.1.idem i
  have he0 : ∀ i, e i ≠ 0 := by
    intro i
    obtain ⟨f, hf, hf0, -, hS, hnS⟩ := hF.1.2 i
    by_cases hi : i ∈ S
    · rw [(hS hi).1]; exact hf0
    · obtain ⟨h1, h2⟩ := hnS hi
      intro h
      apply hf0
      have : f * e i = f := by rw [h2, mul_add, hf.eq, h1, add_zero]
      rw [h, mul_zero] at this
      exact this.symm
  have hπ : ∀ J ⊆ S, IsUnit (∏ j ∈ J, π j) := fun J hJ =>
    Finset.prod_induction _ IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one
      (fun j hj => (hF.2 j (hJ hj)).1.1)
  choose H hH using fun i y => exists_ub B a ha (e i) (he i) (he0 i) y
  choose Lo hLo using fun i t => exists_lb' B a ha (e i) (he i) (he0 i) N t
  let Ys := I.powerset.image (fun J => (∏ j ∈ J, π j) * u)
  let Ss := I'.powerset.image (fun J => (∏ j ∈ J, π j) * s)
  let P : Set (ι → ℤ) := ⋃ y ∈ (Ys : Set B.A), ⋃ t ∈ (Ss : Set B.A),
    Set.pi Set.univ (fun i => Set.Icc (Lo i t) (H i y))
  have hP : P.Finite := Set.Finite.biUnion Ys.finite_toSet fun y _ =>
    Set.Finite.biUnion Ss.finite_toSet fun t _ => Set.Finite.pi (fun i => Set.finite_Icc _ _)
  refine (hP.biUnion fun p _ => (hC p).1).subset ?_
  rintro M ⟨hML, hMt⟩
  obtain ⟨p, hp⟩ := hN M hML
  have h1 : dlt π I (indM B M) u ≠ 0 := left_ne_zero_of_mul hMt
  have h2 : dlt π I' (indD B M) s ≠ 0 := right_ne_zero_of_mul hMt
  obtain ⟨J, hJ, hJ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨J', hJ', hJ0'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  have hyM : (∏ j ∈ J, π j) * u ∈ M := by
    by_contra h; apply hJ0; simp [indM, h]
  have htD : InDual B ((∏ j ∈ J', π j) * s) M := by
    by_contra h; apply hJ0'; simp [indD, h]
  have hyU : IsUnit ((∏ j ∈ J, π j) * u) :=
    (hπ J ((Finset.mem_powerset.1 hJ).trans hI)).mul hu
  have htU : IsUnit ((∏ j ∈ J', π j) * s) :=
    (hπ J' ((Finset.mem_powerset.1 hJ').trans hI')).mul hs
  refine Set.mem_biUnion (x := p) ?_ hp
  refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hJ))
    (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hJ')) ?_)
  intro i _
  exact ⟨hLo i _ htU M (p i) (hp i).1 htD, hH i _ hyU (p i) ((hp i).2 _ hyM)⟩

end GlobalTheory.UnitLemma.Desc
