import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.SmulBasisMemHatIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFiniteAdeleCompleteSeparated

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Complete

theorem baer_fractionField (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Module.Baer R K := by
  intro I g
  by_cases hI : ∃ a ∈ I, a ≠ 0
  · obtain ⟨a, ha, ha0⟩ := hI
    have ha' : algebraMap R K a ≠ 0 := by
      simpa using ha0
    refine ⟨LinearMap.toSpanSingleton R K (g ⟨a, ha⟩ / algebraMap R K a), fun x hx => ?_⟩
    have h : a • g ⟨x, hx⟩ = x • g ⟨a, ha⟩ := by
      rw [← map_smul, ← map_smul]
      congr 1
      ext
      simp [mul_comm]
    rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
    rw [Algebra.smul_def, Algebra.smul_def] at h
    field_simp
    rw [← h]
  · refine ⟨0, fun x hx => ?_⟩
    have : x = 0 := by
      by_contra h
      exact hI ⟨x, hx, h⟩
    subst this
    have : (⟨0, hx⟩ : I) = 0 := rfl
    rw [this, map_zero, map_zero]

theorem exists_frame (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (M : Submodule R V) [Module.Finite R M] :
    ∃ (m : ℕ) (e : Fin m → V) (t : Fin m → (V →ₗ[K] K)), (∀ i, e i ∈ M) ∧
      (∀ i, ∀ v ∈ M, t i v ∈ (algebraMap R K).range) ∧ ∀ v ∈ M, ∑ i, t i v • e i = v := by
  classical
  have : Module.IsTorsionFree R V := Module.IsTorsionFree.trans_faithfulSMul R K V
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite _ _
  have : Module.Projective R M := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have h : ∀ i, ∃ s : V →ₗ[R] K, s ∘ₗ M.subtype = Algebra.linearMap R K ∘ₗ LinearMap.proj i ∘ₗ g :=
    fun i => (baer_fractionField R K).extension_property _ M.injective_subtype _
  choose s hs using h
  have hs' : ∀ i v (hv : v ∈ M), s i v = algebraMap R K (g ⟨v, hv⟩ i) := fun i v hv =>
    LinearMap.congr_fun (hs i) ⟨v, hv⟩
  refine ⟨m, fun i => f (Pi.single i 1), fun i => (s i).extendScalarsOfIsLocalization R⁰ K,
    fun i => (f _).2, fun i v hv => ⟨_, (hs' i v hv).symm⟩, fun v hv => ?_⟩
  have h1 : f (g ⟨v, hv⟩) = ⟨v, hv⟩ := LinearMap.congr_fun hfg _
  have h2 : ∑ i, g ⟨v, hv⟩ i • f (Pi.single i 1) = ⟨v, hv⟩ := by
    conv_rhs => rw [← h1, pi_eq_sum_univ' (g _), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  have h3 := congrArg Subtype.val h2
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h3
  rw [LinearMap.extendScalarsOfIsLocalization_apply', hs' i v hv, algebraMap_smul]

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

noncomputable def comb {m : ℕ} (e : Fin m → Fin n → E) :
    (Fin m → FiniteAdeleRing (𝓞 F) F) →+ (Fin n → RA F E) where
  toFun a := ∑ i, fun j => a i ⊗ₜ[F] e i j
  map_zero' := by funext j; simp
  map_add' a b := by funext j; simp [TensorProduct.add_tmul, Finset.sum_add_distrib]

end

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem comb_apply_eq_sum_tmul {m : ℕ} (e : Fin m → Fin n → E)
    (a : Fin m → FiniteAdeleRing (𝓞 F) F) :
    _root_.GlobalTheory.AdLat.Complete.comb e a = ∑ k, fun j => a k ⊗ₜ[F] e k j := rfl

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem exists_integral_comb_of_mem_hat {m : ℕ} {e : Fin m → Fin n → E}
    {L : Set (Fin n → E)} (he : ∀ x ∈ L, ∃ c : Fin m → ℤ, ∑ k, c k • e k = x)
    {w : Fin n → _root_.GlobalTheory.AdLat.RA F E} (hw : w ∈ _root_.GlobalTheory.AdLat.hat F L) :
    ∃ a : Fin m → FiniteAdeleRing (𝓞 F) F, (∀ k v, a k v ∈ v.adicCompletionIntegers F) ∧
      w = _root_.GlobalTheory.AdLat.Complete.comb e a := by
  unfold _root_.GlobalTheory.AdLat.hat at hw
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨c, rfl⟩ := he x hx
    refine ⟨fun k => c k • a, fun k v => zsmul_mem (ha v) _, ?_⟩
    funext j
    simp only [comb_apply_eq_sum_tmul, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Int.cast_smul_eq_zsmul F, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      Int.cast_smul_eq_zsmul]
  | zero =>
    refine ⟨0, fun k v => zero_mem _, ?_⟩
    simp
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, fun k v => add_mem (ha k v) (hb k v), (map_add _ a b).symm⟩
  | neg x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨-a, fun k v => neg_mem (ha k v), (map_neg _ a).symm⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem eq_zero_of_forall_nsmul_mem_hat [FiniteDimensional F E] {m : ℕ}
    {e : Fin m → Fin n → E} {L : Set (Fin n → E)}
    (he : ∀ x ∈ L, ∃ c : Fin m → ℤ, ∑ k, c k • e k = x)
    (z : Fin n → _root_.GlobalTheory.AdLat.RA F E)
    (hz : ∀ N : ℕ, 0 < N → ∃ w ∈ _root_.GlobalTheory.AdLat.hat F L, z = N • w) : z = 0 := by
  classical
  set b := Module.finBasis F E
  set B := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F)) (S := F)
    Finset.univ (fun t : Fin m × Fin n × Fin (Module.finrank F E) => b.repr (e t.1 t.2.1) t.2.2)
  set δ : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d)
  have hδ : IsUnit δ :=
    (IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)).map
      (algebraMap F (FiniteAdeleRing (𝓞 F) F))
  have hint : ∀ w ∈ _root_.GlobalTheory.AdLat.hat F L, ∀ i ℓ v,
      (δ * B.repr (w i) ℓ) v ∈ v.adicCompletionIntegers F := by
    intro w hw i ℓ
    obtain ⟨a, ha, rfl⟩ := exists_integral_comb_of_mem_hat he hw
    simp only [comb_apply_eq_sum_tmul, Finset.sum_apply, map_sum, Finsupp.coe_finset_sum,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_induction _ (fun y : FiniteAdeleRing (𝓞 F) F =>
      ∀ v, y v ∈ v.adicCompletionIntegers F) (fun x y hx hy v => add_mem (hx v) (hy v))
      (fun v => zero_mem _) fun k _ => ?_
    obtain ⟨r, hr⟩ := hd ⟨k, i, ℓ⟩ (Finset.mem_univ _)
    have hterm : δ * (a k * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr (e k i) ℓ)) =
        a k * algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r) := by
      rw [hr, Algebra.smul_def, map_mul]
      ring
    have hB : (B.repr (a k ⊗ₜ[F] e k i)) ℓ =
        a k * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr (e k i) ℓ) := by
      simp [B, Algebra.TensorProduct.basis_repr_tmul]
    rw [hB, hterm]
    intro v
    exact mul_mem (ha k v) ((_root_.GlobalTheory.AdLat.Model.integral_iff _).mpr ⟨r, rfl⟩ v)
  have hcoord : ∀ i ℓ, B.repr (z i) ℓ = 0 := by
    intro i ℓ
    refine (hδ.mul_right_eq_zero).mp ?_
    refine (_root_.GlobalTheory.AdLat.integral_finiteAdele_complete_separated F).1 _ fun N hN => ?_
    obtain ⟨w, hw, rfl⟩ := hz N hN
    refine ⟨δ * B.repr (w i) ℓ, hint w hw i ℓ, ?_⟩
    simp only [Pi.smul_apply, map_nsmul, Finsupp.smul_apply, mul_smul_comm]
  funext i
  refine B.repr.injective ?_
  ext ℓ
  simp [hcoord i ℓ]

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem comb_mem_hat_of_integral {m : ℕ} {e : Fin m → Fin n → E}
    {L : Set (Fin n → E)} (he : ∀ k, e k ∈ L) {a : Fin m → FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ k v, a k v ∈ v.adicCompletionIntegers F) :
    _root_.GlobalTheory.AdLat.Complete.comb e a ∈ _root_.GlobalTheory.AdLat.hat F L := by
  rw [comb_apply_eq_sum_tmul]
  refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ?_
  exact ⟨a k, ha k, e k, he k, rfl⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem exists_limit_in_hat_of_cauchy_nsmul {m : ℕ} {e : Fin m → Fin n → E}
    {L : Set (Fin n → E)} (he : ∀ x ∈ L, ∃ c : Fin m → ℤ, ∑ k, c k • e k = x)
    (hmem : ∀ k, e k ∈ L) (x : ℕ → (Fin n → _root_.GlobalTheory.AdLat.RA F E))
    (hx : ∀ N, x N ∈ _root_.GlobalTheory.AdLat.hat F L)
    (hstep : ∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ _root_.GlobalTheory.AdLat.hat F L,
      x (N * m) = x N + N • w) :
    ∃ z ∈ _root_.GlobalTheory.AdLat.hat F L, ∀ N : ℕ, 0 < N →
      ∃ w ∈ _root_.GlobalTheory.AdLat.hat F L, z = x N + N • w := by
  classical
  have hfact : ∀ t : ℕ, (t + 1 + 1).factorial = (t + 1).factorial * (t + 2) := fun t => by
    rw [Nat.factorial_succ (t + 1)]
    ring
  have hs : ∀ t : ℕ, ∃ c : Fin m → FiniteAdeleRing (𝓞 F) F,
      (∀ k v, c k v ∈ v.adicCompletionIntegers F) ∧
      x (t + 1 + 1).factorial = x (t + 1).factorial +
        (t + 1).factorial • _root_.GlobalTheory.AdLat.Complete.comb e c := by
    intro t
    obtain ⟨w, hw, hxw⟩ := hstep (t + 1).factorial (t + 2) (Nat.factorial_pos _) (by omega)
    obtain ⟨c, hc, rfl⟩ := exists_integral_comb_of_mem_hat he hw
    exact ⟨c, hc, by rw [hfact, hxw]⟩
  choose c hc hcx using hs
  obtain ⟨a₀, ha₀, hxa₀⟩ := exists_integral_comb_of_mem_hat he (hx (0 + 1).factorial)
  let A : ℕ → Fin m → FiniteAdeleRing (𝓞 F) F :=
    fun t => a₀ + ∑ j ∈ Finset.range t, (j + 1).factorial • c j
  have hA : ∀ t, _root_.GlobalTheory.AdLat.Complete.comb e (A t) = x (t + 1).factorial := by
    intro t
    induction t with
    | zero =>
      show _root_.GlobalTheory.AdLat.Complete.comb e
        (a₀ + ∑ j ∈ Finset.range 0, (j + 1).factorial • c j) = _
      rw [Finset.sum_range_zero, add_zero]
      exact hxa₀.symm
    | succ t ih =>
      show _root_.GlobalTheory.AdLat.Complete.comb e
        (a₀ + ∑ j ∈ Finset.range (t + 1), (j + 1).factorial • c j) = _
      rw [Finset.sum_range_succ, ← add_assoc, map_add,
        show a₀ + ∑ j ∈ Finset.range t, (j + 1).factorial • c j = A t from rfl, ih, map_nsmul,
        hcx t]
  have hAint : ∀ t k v, A t k v ∈ v.adicCompletionIntegers F := by
    intro t k
    simp only [A, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    intro v
    refine add_mem (ha₀ k v) ?_
    revert v
    refine Finset.sum_induction _ (fun y : FiniteAdeleRing (𝓞 F) F =>
      ∀ v, y v ∈ v.adicCompletionIntegers F) (fun y y' hy hy' v => add_mem (hy v) (hy' v))
      (fun v => zero_mem _) fun j _ v => ?_
    exact nsmul_mem (hc j k v) _
  have hcauchy : ∀ k, ∀ N m' : ℕ, 0 < N → 0 < m' → ∃ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ A (N * m') k = A N k + N • a := by
    intro k N m' hN hm'
    have hle : N ≤ N * m' := Nat.le_mul_of_pos_right _ hm'
    have hdvd : ∀ j ∈ Finset.Ico N (N * m'), N ∣ (j + 1).factorial := fun j hj =>
      Nat.dvd_factorial hN (by simp only [Finset.mem_Ico] at hj; omega)
    refine ⟨∑ j ∈ Finset.Ico N (N * m'), ((j + 1).factorial / N) • c j k, ?_, ?_⟩
    · refine Finset.sum_induction _ (fun y : FiniteAdeleRing (𝓞 F) F =>
        ∀ v, y v ∈ v.adicCompletionIntegers F) (fun y y' hy hy' v => add_mem (hy v) (hy' v))
        (fun v => zero_mem _) fun j _ v => ?_
      exact nsmul_mem (hc j k v) _
    · simp only [A, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
      rw [← Finset.sum_range_add_sum_Ico _ hle, add_assoc, Finset.smul_sum]
      congr 2
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [smul_smul, Nat.mul_div_cancel' (hdvd j hj)]
  choose y hy using fun k => (_root_.GlobalTheory.AdLat.integral_finiteAdele_complete_separated F).2
    (fun N => A N k) (fun N v => hAint N k v) (hcauchy k)
  have hyint : ∀ k v, y k v ∈ v.adicCompletionIntegers F := by
    intro k v
    obtain ⟨a, ha, h⟩ := hy k 1 one_pos
    rw [h]
    exact add_mem (hAint 1 k v) (nsmul_mem (ha v) 1)
  refine ⟨_root_.GlobalTheory.AdLat.Complete.comb e y,
    comb_mem_hat_of_integral hmem hyint, fun N hN => ?_⟩
  choose a ha hya using fun k => hy k N hN
  have hyA : y = A N + N • a := funext fun k => hya k
  have hdN : N ∣ (N + 1).factorial := Nat.dvd_factorial hN (by omega)
  obtain ⟨w, hw, hxw⟩ := hstep N ((N + 1).factorial / N) hN
    (Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) hdN) hN)
  rw [Nat.mul_div_cancel' hdN] at hxw
  refine ⟨w + _root_.GlobalTheory.AdLat.Complete.comb e a,
    add_mem hw (comb_mem_hat_of_integral hmem ha), ?_⟩
  rw [hyA, map_add, map_nsmul, hA, hxw, smul_add, add_assoc]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in

theorem _root_.GlobalTheory.AdLat.Complete.hat_separated_complete : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ z : Fin n → _root_.GlobalTheory.AdLat.RA F E, (∀ N : ℕ, 0 < N →
      ∃ w ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), z = N • w) → z = 0) ∧
    ∀ x : ℕ → (Fin n → _root_.GlobalTheory.AdLat.RA F E),
      (∀ N, x N ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)))) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        x (N * m) = x N + N • w) →
      ∃ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), ∀ N : ℕ, 0 < N →
        ∃ w ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), z = x N + N • w := by
  intro F E _ _ _ _ _ n L hL
  obtain ⟨m, e, he⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (hL.restrictScalars (R := ℤ))
  have hgen : ∀ x ∈ (L : Set (Fin n → E)), ∃ c : Fin m → ℤ, ∑ k, c k • e k = x := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (Set.range e) := by
      rw [he]
      exact hx
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx'
  have hmem : ∀ k, e k ∈ (L : Set (Fin n → E)) := by
    intro k
    have hk : e k ∈ Submodule.span ℤ (Set.range e) := Submodule.subset_span ⟨k, rfl⟩
    rw [he] at hk
    exact hk
  exact ⟨eq_zero_of_forall_nsmul_mem_hat hgen,
    fun x hx hstep => exists_limit_in_hat_of_cauchy_nsmul hgen hmem x hx hstep⟩

end GlobalTheory.AdLat.Complete
