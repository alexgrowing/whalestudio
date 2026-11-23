import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PointHeightDegreeHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)

noncomputable section

namespace OneBlockPoints

section Denominators

variable {K : Type} [Field K] [NumberField K]

theorem exists_nat_mul_isIntegral (x : K) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : K) * x) := by
  have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ x)
  obtain ⟨m, s, hm, hs⟩ := hx.exists_nsmul_eq (𝓞 K)
  refine ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
  rw [← nsmul_eq_mul, hs]
  exact RingOfIntegers.isIntegral_coe s

theorem exists_nat_mul_isIntegral_fin {ι : Type*} [Fintype ι] (x : ι → K) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : K) * x i) := by
  choose m hm hi using fun i ↦ exists_nat_mul_isIntegral (x i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ ↦ hm i, fun i ↦ ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (m i : K), mul_assoc]
  have hc' : IsIntegral ℤ (c : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (c : ℤ)))
  exact hc'.mul (hi i)

theorem exists_nat_lattice_integral {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (hL : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ v ∈ L, ∀ j, IsIntegral ℤ ((D : K) * v j) := by
  obtain ⟨S, hS⟩ := hL
  obtain ⟨D, hD, hi⟩ := exists_nat_mul_isIntegral_fin (fun p : S × Fin m ↦ (p.1 : Fin m → K) p.2)
  refine ⟨D, hD, fun v hv ↦ ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem u hu => exact fun j ↦ hi (⟨u, hu⟩, j)
  | zero => intro j; simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | add a b _ _ ha hb => intro j; simpa [mul_add] using (ha j).add (hb j)
  | smul c a _ ha =>
    intro j
    have h := (RingOfIntegers.isIntegral_coe c).mul (ha j)
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
    exact h

theorem isIntegral_of_mem_standard {n : ℕ} {v : Fin n → K}
    (hv : v ∈ (HermLattice.standard K n).lattice) (j : Fin n) : IsIntegral ℤ (v j) := by
  induction hv using Submodule.span_induction generalizing j with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    by_cases h : j = i
    · subst h
      simpa using (isIntegral_one : IsIntegral ℤ (1 : K))
    · simpa [Pi.single_apply, h] using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | add a b _ _ ha hb => exact (ha j).add (hb j)
  | smul c a _ ha =>
    rw [Pi.smul_apply, Algebra.smul_def]
    exact (RingOfIntegers.isIntegral_coe c).mul (ha j)

end Denominators

section Forms

variable {K : Type} [Field K] [NumberField K] {e r : ℕ}

omit [NumberField K] in

theorem sum_smul_oneBlockForms_apply (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (f : Fin (oneBlockSize e r + 1) → ℤ) (j : Fin (r + 1)) :
    (∑ b, f b • oneBlockForms om b) j = ∑ a, f ((oneBlockIndex e r).symm (a, j)) • ((om a : 𝓞 K) : K) := by
  rw [Finset.sum_apply, ← (oneBlockIndex e r).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp [oneBlockForms]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    simp [oneBlockForms, Ne.symm hj']
  · simp

omit [NumberField K] in

theorem sum_mul_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (g : Fin (oneBlockSize e r + 1) → ℂ) (τ : K →+* ℂ) (j : Fin (r + 1)) :
    ∑ b, g b * τ (oneBlockForms om b j) = ∑ a, g ((oneBlockIndex e r).symm (a, j)) * τ ((om a : 𝓞 K) : K) := by
  rw [← (oneBlockIndex e r).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp [oneBlockForms]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    simp [oneBlockForms, Ne.symm hj']
  · simp

omit [NumberField K] in

theorem exists_int_comb_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (u : Fin (r + 1) → K) (hu : ∀ j, IsIntegral ℤ (u j)) :
    ∃ c : Fin (oneBlockSize e r + 1) → ℤ, ∑ p, c p • oneBlockForms om p = u := by
  let s : Fin (r + 1) → 𝓞 K := fun j ↦ ⟨u j, hu j⟩
  refine ⟨fun p ↦ om.repr (s (oneBlockIndex e r p).2) (oneBlockIndex e r p).1, ?_⟩
  funext j
  rw [sum_smul_oneBlockForms_apply]
  simp only [Equiv.apply_symm_apply]
  have h := congrArg (algebraMap (𝓞 K) K) (om.sum_repr (s j))
  simp only [map_sum, map_zsmul] at h
  exact h

theorem isDualBasis_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    IsDualBasis (HermLattice.standard K (r + 1)).lattice (oneBlockForms (r := r) om) := by
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hj := congrFun hg (oneBlockIndex e r p).2
    rw [sum_smul_oneBlockForms_apply] at hj
    have h0 : ∑ a, g ((oneBlockIndex e r).symm (a, (oneBlockIndex e r p).2)) • om a = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      simpa [map_sum, map_zsmul] using hj
    have := (Fintype.linearIndependent_iff.mp om.linearIndependent) _ h0 (oneBlockIndex e r p).1
    simpa using this
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩ v hv
    obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp
      (isIntegral_of_mem_standard hv (oneBlockIndex e r p).2)
    refine ⟨om (oneBlockIndex e r p).1 * t, ?_⟩
    rw [map_mul, ht]
    simp [oneBlockForms]
  · intro χ hχ
    have hi : ∀ j, IsIntegral ℤ (χ j) := by
      intro j
      obtain ⟨a, ha⟩ := hχ (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
      have h1 : χ ⬝ᵥ (Pi.single j 1 : Fin (r + 1) → K) = χ j := by simp
      rw [← h1, ← ha]
      exact RingOfIntegers.isIntegral_coe a
    obtain ⟨c, hc⟩ := exists_int_comb_oneBlockForms om χ hi
    rw [← hc]
    exact Submodule.sum_mem _ fun p _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

omit [NumberField K] in
theorem latticeForm_single {m : ℕ} (j : Fin m) (x : K) :
    latticeForm (Pi.single j x : Fin m → K) = C x * X j := by
  rw [latticeForm, Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj'])
    (by simp), Pi.single_eq_same]

omit [NumberField K] in

theorem latticeMap_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    latticeMap (oneBlockForms (r := r) om) = Heights.oneBlockMap om := by
  refine MvPolynomial.ringHom_ext (fun a ↦ by simp [latticeMap, Heights.oneBlockMap]) fun v ↦ ?_
  simp only [latticeMap, Heights.oneBlockMap, coe_eval₂Hom, eval₂_X, oneBlockForms]
  exact latticeForm_single _ _

omit [NumberField K] in
theorem latticeIdeal_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    latticeIdeal (oneBlockForms (r := r) om) = Heights.oneBlockIdeal om := by
  rw [latticeIdeal, Heights.oneBlockIdeal, latticeMap_oneBlockForms]

omit [NumberField K] in
theorem latticePoint_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (σ : K →+* ℂ)
    (w : Fin (r + 1) → ℂ) : latticePoint (oneBlockForms om) σ w = Heights.oneBlockPoint om σ w := by
  funext u p
  rw [latticePoint, Finset.sum_eq_single (oneBlockIndex e r p).2
    (fun j _ hj ↦ by simp [oneBlockForms, hj]) (by simp)]
  simp [oneBlockForms, Heights.oneBlockPoint]

omit [NumberField K] in

theorem eq_latticePoint_iff (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (y : Cone (oneBlockSizes e r) ℂ)
    (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    y = latticePoint (oneBlockForms om) σ w ↔
      ∀ m j, coneToPairs y ⟨(), (m, j)⟩ = σ (om m : K) * w j := by
  rw [latticePoint_oneBlockForms]
  constructor
  · rintro rfl m j
    simp [coneToPairs, Heights.oneBlockPoint]
  · intro h
    funext u v
    have := h (oneBlockIndex e r v).1 (oneBlockIndex e r v).2
    simpa [coneToPairs, Heights.oneBlockPoint] using this

omit [NumberField K] in

def pairsToCone (z : (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) → ℂ) : Cone (oneBlockSizes e r) ℂ :=
  fun _ v ↦ z ⟨(), oneBlockIndex e r v⟩

omit [NumberField K] in
theorem coneToPairs_pairsToCone (z : (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) → ℂ) :
    coneToPairs (pairsToCone z) = z := by
  funext p
  rcases p with ⟨⟨⟩, q⟩
  simp [coneToPairs, pairsToCone]

end Forms

section OfLattice

variable {K : Type} [Field K] [NumberField K]

open Classical in

theorem recover {d i : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (Minv : Matrix (K →+* ℂ) (Fin d) ℂ)
    (hM : Minv * embMat om = 1) (z : (Σ _ : Unit, Fin d × Fin (i + 1)) → ℂ) (σ : K →+* ℂ)
    (w : Fin (i + 1) → ℂ) (hz : ∀ m j, z ⟨(), (m, j)⟩ = σ (om m : K) * w j) (j : Fin (i + 1)) :
    w j = ∑ m, Minv σ m * z ⟨(), (m, j)⟩ := by
  have h := congrFun (congrFun hM σ) σ
  simp only [Matrix.mul_apply, embMat, Matrix.of_apply, Matrix.one_apply_eq] at h
  simp_rw [hz, ← mul_assoc, ← Finset.sum_mul, h, one_mul]

def embEquiv {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) : Fin d ≃ (K →+* ℂ) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, NumberField.Embeddings.card K ℂ, ← RingOfIntegers.rank,
      Module.finrank_eq_card_basis om, Fintype.card_fin])

open Classical in

theorem of_lattice (hA : Heights.OneBlockPoints.Statement) : OneBlockPoints.Statement := by
  intro K _ _ d om i
  obtain _ | e := d
  · exact absurd om.index_nonempty (not_nonempty_iff.mpr inferInstance)
  obtain ⟨h1, -, h3⟩ := hA K i (oneBlockSize e i) (HermLattice.standard K (i + 1))
    (oneBlockForms om) (isDualBasis_oneBlockForms om)
  choose R hR using h3
  let Minv : Matrix (K →+* ℂ) (Fin (e + 1)) ℂ := Matrix.of fun σ m ↦ R σ 0 ((oneBlockIndex e i).symm (m, 0))
  have hM : Minv * embMat om = 1 := by
    ext σ τ
    have h := hR σ 0 τ 0
    rw [sum_mul_oneBlockForms] at h
    simp only [Matrix.mul_apply, embMat, Matrix.of_apply, Minv, Matrix.one_apply]
    rw [h]
    by_cases hστ : σ = τ
    · subst hστ; simp
    · simp [hστ, Ne.symm hστ]
  refine ⟨fun z hz ↦ ?_, ⟨Minv, hM, (mul_eq_one_comm_of_equiv (embEquiv om).symm).mp hM⟩, recover om⟩
  rw [← coneToPairs_pairsToCone z, ← mem_conePoints_iff, ← latticeIdeal_oneBlockForms] at hz
  obtain ⟨σ, ⟨w, hw, hzw⟩, huniq⟩ := h1 _ hz
  refine ⟨σ, ⟨w, hw, ?_⟩, fun τ ⟨w', hw', hzw'⟩ ↦ huniq τ ⟨w', hw', ?_⟩⟩
  · have := (eq_latticePoint_iff om _ σ w).mp hzw
    rwa [coneToPairs_pairsToCone] at this
  · rw [eq_latticePoint_iff, coneToPairs_pairsToCone]
    exact hzw'

end OfLattice

section OfStandard

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem sum_intCast_mul_apply {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℤ) (u : ι → Fin m → K)
    (τ : K →+* ℂ) (j : Fin m) : ∑ i, (c i : ℂ) * τ (u i j) = τ ((∑ i, c i • u i) j) := by
  simp [Finset.sum_apply, map_sum, zsmul_eq_mul]

omit [NumberField K] in
theorem sum_zsmul_sum_mul {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℤ) (u : ι → Fin m → K)
    (τ : K →+* ℂ) (w : Fin m → ℂ) :
    ∑ i, c i • ∑ j, τ (u i j) * w j = ∑ j, τ ((∑ i, c i • u i) j) * w j := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← sum_intCast_mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [zsmul_eq_mul, mul_assoc]

theorem sum_comb_comb {M : Type*} [AddCommGroup M] {ι κ : Type*} [Fintype ι] [Fintype κ] (q : κ → ℤ)
    (c : κ → ι → ℤ) (x : ι → M) :
    ∑ b, (∑ p, q p * c p b) • x b = ∑ p, q p • ∑ b, c p b • x b := by
  simp_rw [Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

omit [NumberField K] in
theorem latticeForm_sum_zsmul {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℤ) (u : ι → Fin m → K) :
    ∑ i, c i • latticeForm (u i) = latticeForm (∑ i, c i • u i) := by
  simp only [latticeForm, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul,
    Finset.sum_mul, smul_mul_assoc]
  exact Finset.sum_comm

omit [NumberField K] in
theorem evalCone_eq {N : ℕ} (z : Cone (fun _ : Unit ↦ N) ℂ) (f : MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ) :
    evalCone z f = eval₂Hom (Int.castRingHom ℂ) (fun v ↦ z v.1 v.2) f := rfl

omit [NumberField K] in

theorem linear_relation {r N : ℕ} {φ : Fin (N + 1) → Fin (r + 1) → K} {z : Cone (fun _ : Unit ↦ N) ℂ}
    (hz : z ∈ Heights.conePoints (latticeIdeal φ) ℂ) (c c' : Fin (N + 1) → ℤ)
    (hc : ∑ b, c b • φ b = ∑ b, c' b • φ b) : ∑ b, c b • z () b = ∑ b, c' b • z () b := by
  have hmem : (∑ b, (c b - c' b) • X ⟨(), b⟩ : MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ) ∈
      latticeIdeal φ := by
    rw [latticeIdeal, RingHom.mem_ker, map_sum]
    simp only [map_zsmul, latticeMap, coe_eval₂Hom, eval₂_X]
    rw [latticeForm_sum_zsmul]
    simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]
    simp [latticeForm]
  have h := hz.2 _ hmem
  rw [evalCone_eq] at h
  simp only [sub_smul, Finset.sum_sub_distrib, map_sub, map_sum, map_zsmul, eval₂Hom_X'] at h
  exact sub_eq_zero.mp h

theorem of_standard (hB : OneBlockPoints.Statement) : Heights.OneBlockPoints.Statement := by
  intro K _ _ r N F φ hφ
  classical
  obtain ⟨e, he⟩ : ∃ e, Module.finrank ℤ (𝓞 K) = e + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℤ) (M := 𝓞 K)).ne'
  let om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K) := (Module.finBasis ℤ (𝓞 K)).reindex (finCongr he)
  obtain ⟨hP1, ⟨Minv, hM, -⟩, hP3⟩ := hB K (e + 1) om r
  set ψ := oneBlockForms (r := r) om with hψ

  obtain ⟨D, hD, hDint⟩ := exists_nat_lattice_integral F.lattice F.fg
  have hC : ∀ p, ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = (D : ℤ) • ψ p := by
    intro p
    have hmem : (D : ℤ) • ψ p ∈ Submodule.span ℤ (Set.range φ) := by
      rw [hφ.span_eq, Submodule.restrictScalars_mem]
      intro v hv
      obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp
        (hDint v hv (oneBlockIndex e r p).2)
      refine ⟨om (oneBlockIndex e r p).1 * t, ?_⟩
      rw [map_mul, ht, smul_dotProduct, hψ]
      simp only [oneBlockForms, single_dotProduct, zsmul_eq_mul, Int.cast_natCast,
        ← RingOfIntegers.coe_eq_algebraMap]
      ring
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  choose Cm hCm using hC

  have hQ : ∀ b, ∃ E : ℕ, 0 < E ∧ ∃ q : Fin (oneBlockSize e r + 1) → ℤ,
      ∑ p, q p • ψ p = (E : ℤ) • φ b := by
    intro b
    obtain ⟨E, hE, hi⟩ := exists_nat_mul_isIntegral_fin (φ b)
    obtain ⟨q, hq⟩ := exists_int_comb_oneBlockForms om ((E : ℤ) • φ b) (fun j ↦ by simpa using hi j)
    exact ⟨E, hE, q, hq⟩
  choose E hE Q hQ using hQ
  have hD0 : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'

  let zz : Cone (fun _ : Unit ↦ N) ℂ → Cone (oneBlockSizes e r) ℂ := fun z _ p ↦ ∑ b, Cm p b • z () b
  have hzzpt : ∀ τ w, zz (latticePoint φ τ w) = latticePoint ψ τ ((D : ℂ) • w) := by
    intro τ w
    funext u p
    simp only [zz, latticePoint]
    rw [sum_zsmul_sum_mul, hCm p]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [zsmul_eq_mul]
    ring

  have hrec : ∀ z ∈ Heights.conePoints (latticeIdeal φ) ℂ, ∀ b,
      ((D : ℤ) * E b) • z () b = ∑ p, Q b p • zz z () p := by
    intro z hz b
    have h := linear_relation hz (fun b' ↦ ((D : ℤ) * E b) * if b' = b then 1 else 0)
      (fun b' ↦ ∑ p, Q b p * Cm p b') (by
        rw [sum_comb_comb]
        simp_rw [hCm, smul_comm (Q b _) ((D : ℤ)), ← Finset.smul_sum, hQ b, smul_smul]
        simp [mul_smul])
    rw [sum_comb_comb] at h
    simpa [mul_smul, zz] using h
  have hzzmem : ∀ z ∈ Heights.conePoints (latticeIdeal φ) ℂ,
      zz z ∈ Heights.conePoints (Heights.oneBlockIdeal om) ℂ := by
    intro z hz
    refine ⟨fun u hu ↦ hz.1 () ?_, fun g hg ↦ ?_⟩
    · funext b
      have h := hrec z hz b
      have hu' : zz z () = 0 := hu
      simp only [hu', Pi.zero_apply, smul_zero, Finset.sum_const_zero] at h
      have hDE : ((D : ℤ) * E b) ≠ 0 := mul_ne_zero (by exact_mod_cast hD.ne') (by exact_mod_cast (hE b).ne')
      exact (smul_eq_zero.mp h).resolve_left hDE
    · let Θ : MvPolynomial (Coord (oneBlockSizes e r)) ℤ →+* MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ :=
        eval₂Hom (Int.castRingHom _) fun v ↦ ∑ b, Cm v.2 b • X ⟨(), b⟩
      let sc : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial (Fin (r + 1)) K :=
        eval₂Hom C fun j ↦ C (D : K) * X j
      have hΘ : (latticeMap φ).comp Θ = sc.comp (Heights.oneBlockMap om) := by
        refine MvPolynomial.ringHom_ext (fun a ↦ by simp [Θ, sc]) fun v ↦ ?_
        simp only [RingHom.comp_apply, Θ, sc, coe_eval₂Hom, eval₂_X, map_sum, map_zsmul,
          Heights.oneBlockMap, eval₂_mul, eval₂_C]
        simp only [latticeMap, coe_eval₂Hom, eval₂_X]
        rw [latticeForm_sum_zsmul, hCm, hψ]
        simp only [oneBlockForms]
        rw [← Pi.single_smul', latticeForm_single, zsmul_eq_mul, Int.cast_natCast, C_mul]
        ring
      have hev : evalCone z (Θ g) = evalCone (zz z) g := by
        rw [evalCone_eq, evalCone_eq, ← RingHom.comp_apply]
        congr 1
        refine MvPolynomial.ringHom_ext (fun a ↦ by simp [Θ]) fun v ↦ ?_
        rw [RingHom.comp_apply]
        simp only [Θ, eval₂Hom_X', map_sum, map_zsmul]
        rfl
      rw [← hev]
      refine hz.2 _ ?_
      rw [latticeIdeal, RingHom.mem_ker, ← RingHom.comp_apply, hΘ, RingHom.comp_apply]
      rw [Heights.oneBlockIdeal, RingHom.mem_ker] at hg
      rw [hg, map_zero]
  refine ⟨fun z hz ↦ ?_, fun σ w hw ↦ ⟨fun u hu ↦ hw ?_, fun f hf ↦ ?_⟩, fun σ j₀ ↦ ?_⟩
  ·
    have hm := hzzmem z hz
    rw [mem_conePoints_iff] at hm
    obtain ⟨σ, ⟨w, hw, hzw⟩, huniq⟩ := hP1 _ hm
    rw [← eq_latticePoint_iff] at hzw
    refine ⟨σ, ⟨(D : ℂ)⁻¹ • w, smul_ne_zero (inv_ne_zero hD0) hw, ?_⟩,
      fun τ ⟨w', hw', hzw'⟩ ↦ huniq τ ⟨(D : ℂ) • w', smul_ne_zero hD0 hw', ?_⟩⟩
    · funext u b
      have h1 := hrec z hz b
      rw [hzw] at h1
      simp only [latticePoint] at h1 ⊢
      rw [sum_zsmul_sum_mul, hQ b] at h1
      have hS : ∑ j, σ ((((E b : ℕ) : ℤ) • φ b) j) * w j = (E b : ℂ) * ∑ j, σ (φ b j) * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp [zsmul_eq_mul]
        ring
      rw [hS, zsmul_eq_mul] at h1
      push_cast at h1
      have hE0 : (E b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hE b).ne'
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm _ (D : ℂ)⁻¹]
      rw [← Finset.mul_sum, eq_inv_mul_iff_mul_eq₀ hD0]
      apply mul_left_cancel₀ hE0
      linear_combination h1
    · rw [← eq_latticePoint_iff, hzw', hzzpt]
  ·
    have h0 : zz (latticePoint φ σ w) = 0 := by
      funext u' p
      have hu' : latticePoint φ σ w () = 0 := hu
      simp [zz, hu']
    have hform := (eq_latticePoint_iff om _ σ _).mp (hzzpt σ w)
    funext j
    have := hP3 Minv hM _ σ _ hform j
    rw [h0] at this
    simp only [coneToPairs, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Pi.smul_apply,
      smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left hD0
  ·
    have hval : ∀ f' : MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ,
        evalCone (latticePoint φ σ w) f' = eval w (map σ (latticeMap φ f')) := by
      intro f'
      have hh : (eval₂Hom (Int.castRingHom ℂ) fun v ↦ latticePoint φ σ w v.1 v.2) =
          ((eval w).comp (MvPolynomial.map σ)).comp (latticeMap φ) :=
        MvPolynomial.ringHom_ext (fun a ↦ by simp) fun v ↦ by
          simp [latticeMap, latticeForm, latticePoint]
      rw [evalCone_eq, hh]
      rfl
    rw [hval, latticeIdeal, RingHom.mem_ker] at *
    rw [hf, map_zero, map_zero]
  ·
    refine ⟨fun b ↦ (D : ℂ)⁻¹ * ∑ a, Minv σ a * (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ),
      fun τ j ↦ ?_⟩
    have hstep : ∀ a, ∑ b, (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ) * τ (φ b j) =
        (D : ℂ) * τ (ψ ((oneBlockIndex e r).symm (a, j₀)) j) := by
      intro a
      rw [sum_intCast_mul_apply, hCm]
      simp [zsmul_eq_mul]
    calc ∑ b, ((D : ℂ)⁻¹ * ∑ a, Minv σ a * (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ)) * τ (φ b j)
        = (D : ℂ)⁻¹ * ∑ a, Minv σ a *
            ∑ b, (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ) * τ (φ b j) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
          ring
      _ = ∑ a, Minv σ a * τ (ψ ((oneBlockIndex e r).symm (a, j₀)) j) := by
          simp_rw [hstep, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          field_simp
      _ = if τ = σ ∧ j = j₀ then 1 else 0 := by
          have hM' := congrFun (congrFun hM σ) τ
          simp only [Matrix.mul_apply, embMat, Matrix.of_apply, Matrix.one_apply] at hM'
          by_cases hj : j = j₀
          · subst hj
            simp only [hψ, oneBlockForms, Equiv.apply_symm_apply, Pi.single_eq_same]
            rw [hM']
            by_cases hστ : σ = τ
            · subst hστ; simp
            · simp [hστ, Ne.symm hστ]
          · simp [hψ, oneBlockForms, hj]

end OfStandard

end OneBlockPoints

theorem OneBlockPoints.equiv :
    GroundTheory.Heights₂.Heights.OneBlockPoints.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.OneBlockPoints.Statement :=
  ⟨OneBlockPoints.of_lattice, OneBlockPoints.of_standard⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
