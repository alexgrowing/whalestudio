import Formalism.GaussJetBounds.StatementN
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp
import Formalism.GaussJetBounds.MonoShapeTop
import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
import Formalism.GaussJetBounds.GaussJetProofs.MfactEqProdUniv

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial

section Slices

variable {R : Type u} [CommRing R] {T σ ρ : Type}

def bSlice (e : T × σ → ρ) (he : Function.Injective e) (t : T) (κ : ρ →₀ ℕ) : σ →₀ ℕ :=
  κ.comapDomain (fun y => e (t, y)) (fun _ _ _ _ h => (Prod.mk.inj (he h)).2)

lemma bSlice_apply (e : T × σ → ρ) (he : Function.Injective e) (t : T) (κ : ρ →₀ ℕ) (y : σ) :
    bSlice e he t κ y = κ (e (t, y)) := rfl

lemma bSlice_add (e : T × σ → ρ) (he : Function.Injective e) (t : T) (a b : ρ →₀ ℕ) :
    bSlice e he t (a + b) = bSlice e he t a + bSlice e he t b := by
  ext y
  simp [bSlice_apply]

lemma bSlice_zero (e : T × σ → ρ) (he : Function.Injective e) (t : T) :
    bSlice e he t 0 = 0 := by
  ext y
  simp [bSlice_apply]

lemma injective_apply_prodMk_of_injective (e : T × σ → ρ) (he : Function.Injective e) (t : T) :
    Function.Injective (fun y : σ => e (t, y)) :=
  fun _ _ h => (Prod.mk.inj (he h)).2

lemma bSlice_mapDomain_same (e : T × σ → ρ) (he : Function.Injective e) (t : T) (u : σ →₀ ℕ) :
    bSlice e he t (u.mapDomain (fun y => e (t, y))) = u := by
  ext y
  rw [bSlice_apply]
  exact Finsupp.mapDomain_apply (injective_apply_prodMk_of_injective e he t) u y

lemma bSlice_mapDomain_ne (e : T × σ → ρ) (he : Function.Injective e) {t t' : T} (h : t ≠ t')
    (u : σ →₀ ℕ) : bSlice e he t (u.mapDomain (fun y => e (t', y))) = 0 := by
  ext y
  rw [bSlice_apply, Finsupp.mapDomain_of_notMem_range]
  · rfl
  · rintro ⟨y', hy'⟩
    exact h (Prod.mk.inj (he hy')).1.symm

lemma slice_prod (e : T × σ → ρ) (he : Function.Injective e) (Q : T → MvPolynomial σ R)
    (s : Finset T) :
    ∀ κ ∈ (∏ t ∈ s, rename (fun y => e (t, y)) (Q t)).support,
      (∀ t ∈ s, bSlice e he t κ ∈ (Q t).support) ∧ ∀ t, t ∉ s → bSlice e he t κ = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro κ hm
    simp only [Finset.prod_empty] at hm
    have hz : κ = 0 := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff] at hm
      apply hm
      rw [MvPolynomial.coeff_one, if_neg (Ne.symm hne)]
    subst hz
    exact ⟨fun t ht => absurd ht (Finset.notMem_empty t), fun t _ => bSlice_zero e he t⟩
  | insert c s hc ih =>
    intro κ hm
    rw [Finset.prod_insert hc] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [support_rename_of_injective (injective_apply_prodMk_of_injective e he c), Finset.mem_image] at hm1
    obtain ⟨u, hu, rfl⟩ := hm1
    obtain ⟨ih1, ih2⟩ := ih m2 hm2
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rw [bSlice_add]
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · rw [bSlice_mapDomain_same, ih2 t hc, add_zero]
        exact hu
      · have hne : t ≠ c := fun h => hc (h ▸ ht')
        rw [bSlice_mapDomain_ne e he hne, zero_add]
        exact ih1 t ht'
    · rw [Finset.mem_insert, not_or] at ht
      rw [bSlice_add, bSlice_mapDomain_ne e he ht.1, ih2 t ht.2, add_zero]

end Slices

section Rows

lemma count_pred {J : Type} [Fintype J] [DecidableEq J] {N1 p : ℕ} (τ : Fin p → J)
    (I : Fin p → Fin N1) (Pr : J → Prop) [DecidablePred Pr] :
    (∑ y ∈ Finset.univ.filter (fun y : J × Fin N1 => Pr y.1),
      (∑ i, Finsupp.single (τ i, I i) 1 : J × Fin N1 →₀ ℕ) y) =
      (Finset.univ.filter (fun i => Pr (τ i))).card := by
  classical
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_comm, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter, Finset.sum_eq_single (τ i, I i)]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma firstRow_minor_degree_le_one {R : Type u} [CommRing R] {m N1 p : ℕ} (A : Fin p → Fin m → R)
    (I : Fin p → Fin N1) (mono : Fin m × Fin N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (Fin m × Fin N1) R)).det.support) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin m × Fin N1 => y.1.val = 0), mono y) ≤ 1 := by
  classical
  obtain ⟨τ, hτ, _, rfl⟩ := shape_minor_mem A I mono hm
  rw [count_pred τ I (fun j => j.val = 0)]
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hτ (Fin.ext (ha.trans hb.symm))

lemma firstRow_minor_degree_eq_one {R : Type u} [CommRing R] {m N1 p : ℕ} (hp1 : 1 ≤ p) (hpm : p ≤ m)
    (I : Fin p → Fin N1) (mono : Fin m × Fin N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C ((1 : Matrix (Fin m) (Fin m) R) ⟨r.val, lt_of_lt_of_le r.isLt hpm⟩ j) * X (j, I r') :
        MvPolynomial (Fin m × Fin N1) R)).det.support) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin m × Fin N1 => y.1.val = 0), mono y) = 1 := by
  classical
  obtain ⟨τ, hτ, ⟨π, hπ⟩, rfl⟩ := shape_minor_mem _ I mono hm
  rw [count_pred τ I (fun j => j.val = 0)]
  have hv : ∀ i, (τ i).val = (π i).val := by
    intro i
    have := hπ i
    beta_reduce at this
    rw [Matrix.one_apply] at this
    by_contra hne
    apply this
    rw [if_neg]
    intro h
    exact hne (by rw [← h])
  refine Finset.card_eq_one.mpr ⟨π.symm ⟨0, hp1⟩, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hv]
  constructor
  · intro h
    rw [Equiv.eq_symm_apply]
    exact Fin.ext h
  · intro h
    rw [h, Equiv.apply_symm_apply]

lemma low_shape {R : Type u} [CommRing R] {N0 N1 Cn : ℕ} (T : Fin N0 → Fin N0 → R)
    (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    ∀ mono ∈ (minorProd (oldRowLow (N1 := N1) T) p hp I).support,
      (∑ y, mono y) = ∑ c, p c ∧
      (∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), mono y) ≤ Cn := by
  intro mono hmono
  classical
  refine ⟨?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    exact (monoShapeLow R N0 N1 N0 Cn T p hp I mono hmono).1
  · unfold minorProd at hmono
    have := shape_prod_le (R := R) (fun mono : Fin N0 × Fin N1 →₀ ℕ =>
      ∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), mono y) (by simp)
      (fun a b => by simp [Finset.sum_add_distrib]) _
      (fun _ => 1) Finset.univ (fun c _ mono hm => firstRow_minor_degree_le_one (R := R) (N1 := N1)
        (fun (r : Fin (p c)) k => T ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ k) (I c) mono hm)
      mono hmono
    simpa using this

lemma id_shape {R : Type u} [CommRing R] {N0 N1 Cn : ℕ}
    (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0) (hp1 : ∀ c, 1 ≤ p c) (I : ∀ c, Fin (p c) → Fin N1) :
    ∀ mono ∈ (minorProd (oldRowLow (N1 := N1) (1 : Matrix (Fin N0) (Fin N0) R)) p hp I).support,
      (∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), mono y) = Cn := by
  intro mono hmono
  classical
  unfold minorProd at hmono
  have := shape_prod_eq (R := R) (fun mono : Fin N0 × Fin N1 →₀ ℕ =>
    ∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), mono y) (by simp)
    (fun a b => by simp [Finset.sum_add_distrib]) _
    (fun _ => 1) Finset.univ (fun c _ mono hm => firstRow_minor_degree_eq_one (R := R) (N1 := N1) (hp1 c) (hp c)
      (I c) mono hm) mono hmono
  simpa using this

lemma min_sum_le {σ : Type} [Fintype σ] (u u' : σ →₀ ℕ) :
    (∑ y, min (u y) (u' y)) ≤ ∑ y, u y :=
  Finset.sum_le_sum fun _ _ => min_le_left _ _

lemma min_sum_le' {σ : Type} [Fintype σ] (Pr : σ → Prop) [DecidablePred Pr] (u u' : σ →₀ ℕ) :
    (∑ y, min (u y) (u' y)) + ∑ y ∈ Finset.univ.filter Pr, u y ≤
      (∑ y ∈ Finset.univ.filter Pr, u' y) + ∑ y, u y := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ Pr (fun y => min (u y) (u' y)),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ Pr (fun y => u y)]
  have h1 : (∑ y ∈ Finset.univ.filter Pr, min (u y) (u' y)) ≤ ∑ y ∈ Finset.univ.filter Pr, u' y :=
    Finset.sum_le_sum fun _ _ => min_le_right _ _
  have h2 : (∑ y ∈ Finset.univ.filter (fun y => ¬ Pr y), min (u y) (u' y)) ≤
      ∑ y ∈ Finset.univ.filter (fun y => ¬ Pr y), u y :=
    Finset.sum_le_sum fun _ _ => min_le_left _ _
  linarith

end Rows

section Jets

lemma jetPair_monomial_left {K : Type u} [Field K] {ι : Type} (κ : ι →₀ ℕ)
    (F : MvPowerSeries ι K) :
    jetPair (monomial κ (1 : K)) F = ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F := by
  classical
  rw [jetPair_eq_sum _ _ {κ} (MvPolynomial.support_monomial_subset)]
  simp

lemma norm_jetPair_le {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type}
    (P : MvPolynomial ι K) (hP : P ∈ opInt K ι) (F : MvPowerSeries ι K) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ κ ∈ P.support, ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F‖ ≤ B) :
    ‖jetPair P F‖ ≤ B := by
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB fun κ hκ => ?_
  rw [mul_assoc, norm_mul]
  calc ‖coeff κ P‖ * ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F‖ ≤ 1 * B :=
        mul_le_mul (hP κ) (h κ hκ) (norm_nonneg _) zero_le_one
    _ = B := one_mul B

lemma C_mul_X_mem_opInt {K : Type u} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : K)
    (hc : ‖c‖ ≤ 1) (j : σ) : C c * X j ∈ opInt K σ := by
  classical
  intro κ
  rw [coeff_C_mul, coeff_X, norm_mul]
  refine mul_le_one₀ hc (norm_nonneg _) ?_
  split_ifs <;> simp

lemma jetsIntegral_subst {K : Type u} [NormedField K] [IsUltrametricDist K] {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (A : ι → ι' → K) (hA : ∀ i j, ‖A i j‖ ≤ 1) (sg : MvPowerSeries ι' K)
    (hsg : JetsIntegral sg) :
    JetsIntegral (MvPowerSeries.subst
      (fun j : ι' => (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K))
      sg) := by
  intro κ
  rw [← jetPair_monomial_left, jet_pair_linearity K ι ι' A]
  refine norm_jetPair_le _ ?_ _ 1 zero_le_one fun μ _ => hsg μ
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
  refine Subring.prod_mem _ fun i _ => Subring.pow_mem _ ?_ _
  exact Subring.sum_mem _ fun j _ => C_mul_X_mem_opInt _ (hA i j) j

end Jets

section Sums

lemma sum_block_slice {T : Type} [Fintype T] [DecidableEq T] {N0 N1 : ℕ} {M : Type*}
    [AddCommMonoid M] (s : T) (b : Fin N1) (f : T × Fin N0 × Fin N1 → M)
    (hf : ∀ y, ¬ (y.1 = s ∧ y.2.2 = b) → f y = 0) :
    ∑ y, f y = ∑ k, f (s, k, b) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single b]
    · intro b' _ hb'
      exact hf _ fun h => hb' h.2
    · intro h
      exact absurd (Finset.mem_univ b) h
  · intro s' _ hs'
    exact Finset.sum_eq_zero fun y _ => hf _ fun h => hs' h.1
  · intro h
    exact absurd (Finset.mem_univ s) h

lemma pair_sum {K : Type u} [Field K] {R' : Type*} [CommSemiring R'] {n : Type} [Fintype n]
    [DecidableEq n] (c : K →+* R') (Mf Mt : Matrix n n K) (h : Mf * Mt.transpose = 1)
    (Y Y' : n → R') :
    (∑ a, (∑ i, c (Mf i a) * Y i) * (∑ i, c (Mt i a) * Y' i)) = ∑ i, Y i * Y' i := by
  have h1 : ∀ i i', (∑ a, Mf i a * Mt i' a) = if i = i' then 1 else 0 := by
    intro i i'
    have := congrFun (congrFun h i) i'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [Matrix.transpose_apply] using this
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have h2 : ∀ i', (∑ a, c (Mf i a) * Y i * (c (Mt i' a) * Y' i')) =
      (if i = i' then 1 else 0) * (Y i * Y' i') := by
    intro i'
    have : (c (∑ a, Mf i a * Mt i' a) : R') = if i = i' then 1 else 0 := by
      rw [h1]
      split_ifs <;> simp
    rw [← this, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul]
    ring
  simp only [h2]
  simp

end Sums

section Frames

variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}

def bM (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (τ : Bool × H) : Matrix (Fin N0) (Fin N0) K :=
  if τ.1 = true then ((x (false, τ.2))⁻¹).transpose else x (false, τ.2)

def bT (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (τ : Bool × H) : Matrix (Fin N0) (Fin N0) K :=
  if τ.1 = true then x τ * (x (false, τ.2)).transpose else 1

lemma bT_mul_bM (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ, (x τ).det ≠ 0)
    (τ : Bool × H) : bT x τ * bM x τ = x τ := by
  obtain ⟨e, t⟩ := τ
  cases e
  · simp [bT, bM]
  · simp only [bT, bM, if_true]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hx (false, t))), Matrix.transpose_one,
      Matrix.mul_one]

lemma bM_pair (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ, (x τ).det ≠ 0) (t : H) :
    bM x (false, t) * (bM x (true, t)).transpose = 1 := by
  simp only [bM, if_true, Matrix.transpose_transpose]
  simpa using Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hx (false, t)))

def bE (H : Type) (N0 N1 : ℕ) : (Bool × H) × (Fin N0 × Fin N1) → Bool × H × Fin N0 × Fin N1 :=
  fun w => (w.1.1, w.1.2, w.2)

lemma bE_inj (H : Type) (N0 N1 : ℕ) : Function.Injective (bE H N0 N1) := by
  rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
  simp only [bE, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

def bA [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K) :
    (Bool × H × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → K :=
  fun y z => if z.1 = (y.1, y.2.1) ∧ z.2.2 = y.2.2.2 then bM x z.1 y.2.2.1 z.2.1 else 0

lemma sum_bE [Fintype H] {N1 : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Bool × H × Fin N0 × Fin N1 → M) : ∑ y, f y = ∑ w, f (bE H N0 N1 w) :=
  (Equiv.sum_comp (Equiv.prodAssoc Bool H (Fin N0 × Fin N1)) f).symm

lemma aa_eq [Fintype H] [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K)
    (z : (Bool × H) × Fin N0 × Fin N1) :
    (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
      MvPowerSeries (Bool × H × Fin N0 × Fin N1) K) =
      ∑ i, MvPowerSeries.C (bM x z.1 i z.2.1) * MvPowerSeries.X (z.1.1, z.1.2, i, z.2.2) := by
  rw [sum_bE, sum_block_slice z.1 z.2.2]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [bA, bE]
  · intro w hw
    have : ¬ (z.1 = (w.1.1, w.1.2) ∧ z.2.2 = w.2.2) := fun h => hw ⟨h.1.symm, h.2.symm⟩
    simp [bA, bE, this]

lemma phi_eq [Fintype H] [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K)
    (τ : Bool × H) (k : Fin N0) (b : Fin N1) :
    (∑ z, C (bA x (bE H N0 N1 (τ, k, b)) z) * X z :
      MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K) =
      ∑ a, C (bM x τ k a) * X (τ, a, b) := by
  rw [sum_block_slice τ b]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [bA, bE]
  · intro w hw
    have : ¬ (w.1 = (τ.1, τ.2) ∧ w.2.2 = b) := hw
    simp [bA, bE, this]

lemma op_change [Fintype H] [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K)
    (hx : ∀ τ, (x τ).det ≠ 0) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
    (hp : ∀ τ c, p τ c ≤ N0) (I : ∀ τ c, Fin (p τ c) → Fin N1) :
    (∏ τ : Bool × H, minorProd
        (fun (i : Fin N0) (b : Fin N1) => (∑ a, C (x τ i a) * X (τ, a, b) :
          MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ)) =
      aeval (fun y : Bool × H × Fin N0 × Fin N1 =>
          (∑ z, C (bA x y z) * X z : MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K))
        (∏ τ : Bool × H, rename (fun y => bE H N0 N1 (τ, y))
          (minorProd (oldRowLow (N1 := N1) (bT x τ)) (p τ) (hp τ) (I τ))) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← AlgHom.comp_apply, map_minorProd]
  congr 1
  funext i b
  simp only [AlgHom.comp_apply, oldRowLow, map_sum, map_mul, rename_C, rename_X, aeval_C, aeval_X,
    algebraMap_eq, phi_eq]
  conv_lhs => rw [← bT_mul_bM x hx τ]
  simp only [Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  ring

lemma beta_change [Fintype H] [DecidableEq H] {N1 : ℕ}
    (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ, (x τ).det ≠ 0) (u : H → K) :
    MvPowerSeries.subst (fun z : (Bool × H) × Fin N0 × Fin N1 =>
        (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
          MvPowerSeries (Bool × H × Fin N0 × Fin N1) K))
      (∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
        MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)) =
      ∑ i : H × Fin N0 × Fin N1, MvPowerSeries.C (u i.1) * MvPowerSeries.X (false, i) *
        MvPowerSeries.X (true, i) := by
  have hs : MvPowerSeries.HasSubst (fun z : (Bool × H) × Fin N0 × Fin N1 =>
        (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
          MvPowerSeries (Bool × H × Fin N0 × Fin N1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by simp
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_sum]
  simp only [map_mul, MvPowerSeries.substAlgHom_X]
  simp only [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_comm (f := fun (k : Fin N0) (b : Fin N1) => MvPowerSeries.C (u t) *
      MvPowerSeries.X (false, t, k, b) * MvPowerSeries.X (true, t, k, b))]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [aa_eq]
  have h := pair_sum (R' := MvPowerSeries (Bool × H × Fin N0 × Fin N1) K)
    (MvPowerSeries.C (σ := Bool × H × Fin N0 × Fin N1) (R := K)) (bM x (false, t)) (bM x (true, t))
    (bM_pair x hx t)
    (fun i => (MvPowerSeries.X (false, t, i, b) : MvPowerSeries (Bool × H × Fin N0 × Fin N1) K))
    (fun i => (MvPowerSeries.X (true, t, i, b) : MvPowerSeries (Bool × H × Fin N0 × Fin N1) K))
  exact h

end Frames

section Norms

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {H : Type} {N0 : ℕ}

lemma bM_norm_le (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ i a, ‖x τ i a‖ ≤ 1)
    (hdet : ∀ τ, ‖(x τ).det‖ = 1) (τ : Bool × H) (i a : Fin N0) : ‖bM x τ i a‖ ≤ 1 := by
  unfold bM
  split_ifs
  · rw [Matrix.transpose_apply]
    exact norm_inv_entry_le_one _ (hx _) (hdet _) _ _
  · exact hx _ _ _

lemma bT_norm_le (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ i a, ‖x τ i a‖ ≤ 1)
    (τ : Bool × H) (i a : Fin N0) : ‖bT x τ i a‖ ≤ 1 := by
  unfold bT
  split_ifs
  · rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul, Matrix.transpose_apply]
    exact mul_le_one₀ (hx _ _ _) (norm_nonneg _) (hx _ _ _)
  · rw [Matrix.one_apply]
    split_ifs <;> simp

lemma bA_norm_le [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K)
    (hx : ∀ τ i a, ‖x τ i a‖ ≤ 1) (hdet : ∀ τ, ‖(x τ).det‖ = 1)
    (y : Bool × H × Fin N0 × Fin N1) (z : (Bool × H) × Fin N0 × Fin N1) : ‖bA x y z‖ ≤ 1 := by
  unfold bA
  split_ifs
  · exact bM_norm_le x hx hdet _ _ _
  · simp

lemma rename_mem_opInt {σ ρ : Type} (f : σ → ρ) (P : MvPolynomial σ K)
    (hP : P ∈ opInt K σ) : rename f P ∈ opInt K ρ := by
  classical
  rw [P.as_sum, map_sum]
  refine Subring.sum_mem _ fun μ _ => ?_
  rw [rename_monomial]
  intro κ
  rw [coeff_monomial]
  split_ifs
  · exact hP μ
  · simp

end Norms

theorem thmB_of : PairJet.{u} → ThmB.{u} := by
  intro hPJ K _ _ _ pi hpi0 hpi1 H _ _ N0 N1 S u hS hu sg hsg x hx hdet TT colN p hp hp1 I nu1 nu2
    size hn1 hn2 hsz
  classical
  have hdet0 : ∀ τ, (x τ).det ≠ 0 := by
    intro τ h
    have := hdet τ
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set Q : Bool × H → MvPolynomial (Fin N0 × Fin N1) K := fun τ =>
    minorProd (oldRowLow (N1 := N1) (bT x τ)) (p τ) (hp τ) (I τ) with hQ
  have hs : MvPowerSeries.HasSubst (fun z : (Bool × H) × Fin N0 × Fin N1 =>
        (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
          MvPowerSeries (Bool × H × Fin N0 × Fin N1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by simp
  have hQint : (∏ τ : Bool × H, rename (fun y => bE H N0 N1 (τ, y)) (Q τ)) ∈
      opInt K (Bool × H × Fin N0 × Fin N1) := by
    refine Subring.prod_mem _ fun τ _ => rename_mem_opInt _ _ ?_
    refine minorProd_mem_opInt _ (fun i b => ?_) _ _ _
    exact Subring.sum_mem _ fun k _ => C_mul_X_mem_opInt _ (bT_norm_le x hx τ i k) _
  rw [op_change x hdet0 colN p hp I, ← jet_pair_linearity K _ _ (bA x), MvPowerSeries.subst_mul hs,
    subst_mvExp hs _ (by simp [MvPowerSeries.smul_eq_C_mul]), MvPowerSeries.subst_smul hs,
    beta_change x hdet0 u]
  refine norm_jetPair_le _ hQint _ _ (Real.rpow_nonneg hpi0.le _) fun κ hκ => ?_
  refine (hPJ K pi hpi0 hpi1 (H × Fin N0 × Fin N1) S (fun i => u i.1) hS (fun i => hu i.1) _
    (jetsIntegral_subst _ (bA_norm_le x hx hdet) sg hsg) κ).trans ?_
  apply Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le
  have hsl := (slice_prod (bE H N0 N1) (bE_inj H N0 N1) Q Finset.univ κ hκ).1
  have key : (∑ i : H × Fin N0 × Fin N1, (min (κ (false, i)) (κ (true, i)) : ℝ)) ≤
      ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun t _ => ?_
    set uf := bSlice (bE H N0 N1) (bE_inj H N0 N1) (false, t) κ with huf
    set ut := bSlice (bE H N0 N1) (bE_inj H N0 N1) (true, t) κ with hut
    have hf := low_shape _ _ _ _ uf (hsl (false, t) (Finset.mem_univ _))
    have hf0 : (∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), uf y) =
        colN (false, t) := by
      refine id_shape (R := K) (p (false, t)) (hp (false, t)) (hp1 (false, t)) (I (false, t)) uf ?_
      have := hsl (false, t) (Finset.mem_univ _)
      simpa [hQ, bT] using this
    have ht := (low_shape _ _ _ _ ut (hsl (true, t) (Finset.mem_univ _))).2
    have e1 : (∑ y : Fin N0 × Fin N1, (min (κ (false, t, y)) (κ (true, t, y)) : ℝ)) =
        ((∑ y, min (uf y) (ut y) : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [e1]
    by_cases h : t ∈ TT
    · simp only [if_pos h]
      have h1 := min_sum_le' (fun y : Fin N0 × Fin N1 => y.1.val = 0) uf ut
      rw [hf0, hf.1, ← hsz, ← hn1] at h1
      have h2 : (∑ y, min (uf y) (ut y)) + nu1 (false, t) ≤ nu1 (true, t) + size (false, t) := by
        rw [hn1 (true, t)]
        omega
      have h3 : ((∑ y, min (uf y) (ut y) : ℕ) : ℝ) + nu1 (false, t) ≤
          nu1 (true, t) + size (false, t) := by exact_mod_cast h2
      have h4 : (0 : ℝ) ≤ nu2 (false, t) := Nat.cast_nonneg _
      linarith
    · simp only [if_neg h]
      have h1 := min_sum_le uf ut
      rw [hf.1, ← hsz] at h1
      have h3 : ((∑ y, min (uf y) (ut y) : ℕ) : ℝ) ≤ size (false, t) := by exact_mod_cast h1
      linarith
  linarith

theorem theorem_B : ThmB.{u} := thmB_of pair_jet_bound

end Formalism.DworkPowerSeriesWeights
