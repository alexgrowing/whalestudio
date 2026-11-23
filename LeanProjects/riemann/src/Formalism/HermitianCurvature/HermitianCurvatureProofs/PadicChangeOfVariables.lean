import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralLatticeRefinementIdentity

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A6x9

theorem nat_tri (m : ℕ) : m * (m + 1) / 2 = m * (m - 1) / 2 + m := by
  cases m with
  | zero => simp
  | succ k =>
    have : (k + 1) * (k + 1 + 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num)]

theorem modK_pow {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
    {ψ : AddChar K ℂ} (hd : LocalDatum K R ψ) {x : K} (hx : IsUnit x) (n : ℕ) :
    modK R (x ^ n) = modK R x ^ n := by
  induction n with
  | zero => simp [A5x5.modK_one]
  | succ n ih => rw [pow_succ, A5x5.modK_mul' hd (hx.pow n) hx, ih, pow_succ]

section GroundTheory

variable {K : Type} [CommRing K]

theorem vnr [IsArtinianRing K] [IsReduced K] (a : K) : ∃ y, a = a ^ 2 * y := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : K)
  have hy' : a ^ (n + 1) * y = a ^ n := by simpa using hy
  have hz : a - a ^ 2 * y = 0 := by
    apply IsNilpotent.eq_zero
    refine ⟨n + 1, ?_⟩
    have e : (a - a ^ 2 * y) ^ (n + 1) = a * (a ^ n - a ^ (n + 1) * y) * (1 - a * y) ^ n := by
      have : a - a ^ 2 * y = a * (1 - a * y) := by ring
      rw [this, mul_pow]; ring
    rw [e, hy']; ring
  exact ⟨y, by linear_combination hz⟩

theorem mem_mulR {R : Subring K} {a x : K} : x ∈ mulR R a ↔ ∃ r ∈ R, a * r = x := by
  simp [mulR]

variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}

theorem isUnit_natSub (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (n m : ℕ) (h : n ≠ m) :
    IsUnit ((n : K) - (m : K)) := by
  rcases lt_or_gt_of_ne h with h | h
  · have := hn (m - n) (by omega)
    rw [Nat.cast_sub h.le] at this
    have h2 := this.neg
    simpa using h2
  · have := hn (n - m) (by omega)
    rwa [Nat.cast_sub h.le] at this

theorem no_compact_ideal (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (x : K)
    (hJ : ∀ y, y * x ∈ R) : x = 0 := by
  have := hd.artin
  have := hd.red
  have := hd.t2
  by_contra hx0
  obtain ⟨y, hy⟩ := vnr x
  obtain ⟨e, he⟩ : ∃ e, e = x * y := ⟨_, rfl⟩
  have hee : e * e = e := by rw [he]; linear_combination (-y) * hy
  have he0 : e ≠ 0 := by
    intro h
    apply hx0
    rw [hy]
    have : x ^ 2 * y = x * e := by rw [he]; ring
    rw [this, h, mul_zero]
  have heR : ∀ w, w * e ∈ R := fun w => by
    have := hJ (w * y)
    have h2 : w * e = w * y * x := by rw [he]; ring
    rwa [h2]
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have key : ∀ h : ℕ → K, (∀ n, h n ∈ R) → ∃ y ∈ R, Tendsto h U (𝓝 y) := by
    intro h hh
    obtain ⟨y, hy, hle⟩ := hd.isCompact.ultrafilter_le_nhds (U.map h) (by
      rw [le_principal_iff, Ultrafilter.coe_map]
      exact Filter.mem_map.2 (Filter.univ_mem' hh))
    exact ⟨y, hy, hle⟩
  let g : ℕ → K := fun n => (n : K) * e
  obtain ⟨y0, -, hy0⟩ := key g (fun n => heR _)
  choose c hcR hc using fun m : ℕ =>
    key (fun n => Ring.inverse ((n : K) - (m : K)) * e) (fun n => heR _)
  have h1 : ∀ m, (y0 - g m) * c m = e := by
    intro m
    refine tendsto_nhds_unique ((hy0.sub_const (g m)).mul (hc m)) (tendsto_const_nhds.congr' ?_)
    have hm : {n : ℕ | n ≠ m} ∈ (U : Filter ℕ) := by
      apply Filter.mem_hyperfilter_of_finite_compl
      simp
    filter_upwards [hm] with n hnm
    have := Ring.mul_inverse_cancel _ (isUnit_natSub hn n m hnm)
    simp only [g]
    linear_combination (-(e * e)) * this - hee
  obtain ⟨c0, -, hc0⟩ := key c hcR
  have h2 : (y0 - y0) * c0 = e :=
    tendsto_nhds_unique ((tendsto_const_nhds.sub hy0).mul hc0)
      (tendsto_const_nhds.congr (fun m => (h1 m).symm))
  apply he0
  rw [← h2]
  ring

variable (π : Kˣ)

theorem iInter_zero (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) (x : K)
    (hx : ∀ n : ℕ, x ∈ mulR R ((π : K) ^ n)) : x = 0 := by
  apply no_compact_ideal hd hn
  intro y
  obtain ⟨m, hm⟩ := hπ' y
  obtain ⟨r, hr, rfl⟩ := mem_mulR.1 (hx m)
  have : y * ((π : K) ^ m * r) = ((π : K) ^ m * y) * r := by ring
  rw [this]
  exact R.mul_mem hm hr

theorem lat_J (hd : LocalDatum K R ψ) (n : ℕ) : A5x5.Lat (mulR R ((π : K) ^ n)) := by
  have := A5x5.lat_mulR hd.isOpen hd.isCompact (π ^ n)
  simpa using this

theorem J_anti (hπ : (π : K) ∈ R) {n m : ℕ} (h : n ≤ m) :
    mulR R ((π : K) ^ m) ≤ mulR R ((π : K) ^ n) := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact mem_mulR.2 ⟨(π : K) ^ k * r, R.mul_mem (R.pow_mem hπ k) hr, by ring⟩

theorem J_sub_R (hπ : (π : K) ∈ R) {n : ℕ} {x : K} (hx : x ∈ mulR R ((π : K) ^ n)) : x ∈ R := by
  obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hx
  exact R.mul_mem (R.pow_mem hπ n) hr

theorem mulR_mul {a x r : K} (hx : x ∈ mulR R a) (hr : r ∈ R) : x * r ∈ mulR R a := by
  obtain ⟨q, hq, rfl⟩ := mem_mulR.1 hx
  exact mem_mulR.2 ⟨q * r, R.mul_mem hq hr, by ring⟩

theorem J_mul {n m : ℕ} {x y : K} (hx : x ∈ mulR R ((π : K) ^ n)) (hy : y ∈ mulR R ((π : K) ^ m)) :
    x * y ∈ mulR R ((π : K) ^ (n + m)) := by
  obtain ⟨q, hq, rfl⟩ := mem_mulR.1 hx
  obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hy
  exact mem_mulR.2 ⟨q * r, R.mul_mem hq hr, by ring⟩

theorem compact_principle (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R)
    (F : K → K) (hF : Continuous F) (C : Set K) (hC : IsCompact C)
    (h : ∀ n : ℕ, ∃ u ∈ C, F u ∈ mulR R ((π : K) ^ n)) : ∃ u ∈ C, F u = 0 := by
  have := hd.t2
  have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => C ∩ F ⁻¹' (mulR R ((π : K) ^ n) : Set K))
    (fun i => Set.inter_subset_inter_right _ (Set.preimage_mono (J_anti π hπ (Nat.le_succ i))))
    (fun i => by obtain ⟨u, hu, hu'⟩ := h i; exact ⟨u, hu, hu'⟩)
    (hC.inter_right (((lat_J π hd 0).cp.isClosed).preimage hF))
    (fun i => hC.isClosed.inter (((lat_J π hd i).cp.isClosed).preimage hF))
  obtain ⟨u, hu⟩ := hne
  rw [Set.mem_iInter] at hu
  exact ⟨u, (hu 0).1, iInter_zero π hd hn hπ' _ (fun n => (hu n).2)⟩

theorem nhds_basis (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) (V : Set K)
    (hV : V ∈ 𝓝 (0 : K)) : ∃ n : ℕ, (mulR R ((π : K) ^ n) : Set K) ⊆ V := by
  have := hd.t2
  by_contra hcon
  push Not at hcon
  have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => (mulR R ((π : K) ^ n) : Set K) ∩ (interior V)ᶜ)
    (fun i => Set.inter_subset_inter_left _ (J_anti π hπ (Nat.le_succ i)))
    (fun i => by
      obtain ⟨u, hu, hu'⟩ := Set.not_subset.1 (hcon i)
      exact ⟨u, hu, fun h => hu' (interior_subset h)⟩)
    ((lat_J π hd 0).cp.inter_right isOpen_interior.isClosed_compl)
    (fun i => (lat_J π hd i).cp.isClosed.inter isOpen_interior.isClosed_compl)
  obtain ⟨u, hu⟩ := hne
  rw [Set.mem_iInter] at hu
  have h0 := iInter_zero π hd hn hπ' u (fun n => (hu n).1)
  apply (hu 0).2
  rw [h0]
  exact mem_interior_iff_mem_nhds.2 hV

theorem J_nhds (hd : LocalDatum K R ψ) (n : ℕ) : (mulR R ((π : K) ^ n) : Set K) ∈ 𝓝 (0 : K) :=
  (lat_J π hd n).op.mem_nhds (mulR R ((π : K) ^ n)).zero_mem

theorem one_add_unit (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) (a : K)
    (ha : a ∈ mulR R ((π : K) ^ 1)) : ∃ u ∈ R, (1 + a) * u = 1 := by
  obtain ⟨u, hu, h⟩ := compact_principle π hd hn hπ hπ' (fun u => (1 + a) * u - 1)
    (by fun_prop) (R : Set K) hd.isCompact (by
      intro n
      refine ⟨∑ i ∈ Finset.range n, (-a) ^ i, R.sum_mem fun i _ =>
        R.pow_mem (R.neg_mem (J_sub_R π hπ ha)) i, ?_⟩
      have h1 := geom_sum_mul (-a) n
      have h2 : (1 + a) * ∑ i ∈ Finset.range n, (-a) ^ i - 1 = -(-a) ^ n := by
        linear_combination -h1
      rw [h2]
      apply AddSubgroup.neg_mem
      obtain ⟨r, hr, rfl⟩ := mem_mulR.1 ha
      exact mem_mulR.2 ⟨(-r) ^ n, R.pow_mem (R.neg_mem hr) n, by
        rw [pow_one, ← mul_pow]; ring⟩)
  exact ⟨u, hu, by linear_combination h⟩

theorem sub_one_mul (hπ : (π : K) ∈ R) {n : ℕ} {x y : K} (hx : x - 1 ∈ mulR R ((π : K) ^ n))
    (hy : y - 1 ∈ mulR R ((π : K) ^ n)) : x * y - 1 ∈ mulR R ((π : K) ^ n) := by
  have hyR : y ∈ R := by
    have := R.add_mem (J_sub_R π hπ hy) R.one_mem
    simpa using this
  have e : x * y - 1 = (x - 1) * y + (y - 1) := by ring
  rw [e]
  exact AddSubgroup.add_mem _ (mulR_mul hx hyR) hy

theorem sub_one_pow (hπ : (π : K) ∈ R) {n : ℕ} {x : K} (hx : x - 1 ∈ mulR R ((π : K) ^ n))
    (i : ℕ) : x ^ i - 1 ∈ mulR R ((π : K) ^ n) := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ]; exact sub_one_mul π hπ ih hx

theorem pow_diff (hπ : (π : K) ∈ R) {s k : ℕ} {si : K} (hs : (s : K) * si = 1)
    (hk : (π : K) ^ k * si ∈ R) {a b : K} (ha : a ∈ mulR R ((π : K) ^ (k + 1)))
    (hb : b ∈ mulR R ((π : K) ^ (k + 1))) :
    ∃ e ∈ mulR R ((π : K) ^ 1), (1 + a) ^ s - (1 + b) ^ s = (s : K) * (a - b) * (1 + e) := by
  have h1 := geom_sum₂_mul (1 + a) (1 + b) s
  obtain ⟨j, hj⟩ : ∃ j, j = ∑ i ∈ Finset.range s, ((1 + a) ^ i * (1 + b) ^ (s - 1 - i) - 1) :=
    ⟨_, rfl⟩
  have hjm : j ∈ mulR R ((π : K) ^ (k + 1)) := by
    rw [hj]
    apply AddSubgroup.sum_mem
    intro i _
    exact sub_one_mul π hπ (sub_one_pow π hπ (by simpa using ha) i)
      (sub_one_pow π hπ (by simpa using hb) _)
  have hj2 : ∑ i ∈ Finset.range s, (1 + a) ^ i * (1 + b) ^ (s - 1 - i) = (s : K) + j := by
    rw [hj, Finset.sum_sub_distrib]
    simp
  refine ⟨si * j, ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hjm
    exact mem_mulR.2 ⟨(π : K) ^ k * si * r, R.mul_mem hk hr, by ring⟩
  · rw [← h1, hj2]
    linear_combination (-(j * (a - b))) * hs

theorem pow_diff0 (hπ : (π : K) ∈ R) {s k : ℕ} {si : K} (hs : (s : K) * si = 1)
    (hk : (π : K) ^ k * si ∈ R) {a : K} (ha : a ∈ mulR R ((π : K) ^ (k + 1))) :
    ∃ e ∈ mulR R ((π : K) ^ 1), (1 + a) ^ s - 1 = (s : K) * a * (1 + e) := by
  obtain ⟨e, he, h⟩ := pow_diff π hπ hs hk ha (AddSubgroup.zero_mem _)
  exact ⟨e, he, by simpa using h⟩

theorem one_add_mem (hπ : (π : K) ∈ R) {n : ℕ} {e : K} (he : e ∈ mulR R ((π : K) ^ n)) :
    1 + e ∈ R := R.add_mem R.one_mem (J_sub_R π hπ he)

theorem root_exists (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {s k : ℕ} {si : K}
    (hs : (s : K) * si = 1) (hk : (π : K) ^ k * si ∈ R) {μ : K}
    (hμ : μ ∈ mulR R ((π : K) ^ (k + 1))) :
    ∃ l ∈ mulR R ((π : K) ^ (k + 1)), (1 + l) ^ s = 1 + (s : K) * μ := by
  have hF : ∀ u ∈ mulR R ((π : K) ^ (k + 1)),
      si * ((1 + u) ^ s - 1) - μ ∈ mulR R ((π : K) ^ (k + 1)) := by
    intro u hu
    obtain ⟨e, he, h⟩ := pow_diff0 π hπ hs hk hu
    have : si * ((1 + u) ^ s - 1) - μ = u * (1 + e) - μ := by
      rw [h]; linear_combination (u * (1 + e)) * hs
    rw [this]
    exact AddSubgroup.sub_mem _ (mulR_mul hu (one_add_mem π hπ he)) hμ
  obtain ⟨u, hu, h⟩ := compact_principle π hd hn hπ hπ' (fun u => si * ((1 + u) ^ s - 1) - μ)
    (by fun_prop) (mulR R ((π : K) ^ (k + 1)) : Set K) (lat_J π hd (k + 1)).cp (by
      intro n
      induction n with
      | zero =>
        exact ⟨0, AddSubgroup.zero_mem _, J_anti π hπ (Nat.zero_le _) (hF 0 (AddSubgroup.zero_mem _))⟩
      | succ n ih =>
        obtain ⟨u, hu, hun⟩ := ih
        have hu' : u - (si * ((1 + u) ^ s - 1) - μ) ∈ mulR R ((π : K) ^ (k + 1)) :=
          AddSubgroup.sub_mem _ hu (hF u hu)
        refine ⟨_, hu', ?_⟩
        obtain ⟨e, he, h⟩ := pow_diff π hπ hs hk hu' hu
        obtain ⟨f, hf⟩ : ∃ f, f = si * ((1 + u) ^ s - 1) - μ := ⟨_, rfl⟩
        rw [← hf] at h hun ⊢
        have e2 : si * ((1 + (u - f)) ^ s - 1) - μ = -(f * e) := by
          linear_combination si * h - hf - (f * (1 + e)) * hs
        show si * ((1 + (u - f)) ^ s - 1) - μ ∈ _
        rw [e2]
        exact AddSubgroup.neg_mem _ (J_mul π hun he))
  refine ⟨u, hu, ?_⟩
  have h : si * ((1 + u) ^ s - 1) - μ = 0 := h
  linear_combination (s : K) * h - ((1 + u) ^ s - 1) * hs

theorem pow_mem_mono (hπ : (π : K) ∈ R) {k k' : ℕ} (h : k ≤ k') {z : K} (hz : (π : K) ^ k * z ∈ R) :
    (π : K) ^ k' * z ∈ R := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  have : (π : K) ^ (k + j) * z = (π : K) ^ j * ((π : K) ^ k * z) := by ring
  rw [this]
  exact R.mul_mem (R.pow_mem hπ j) hz

theorem bdd_of_compact (hd : LocalDatum K R ψ) (hπ : (π : K) ∈ R)
    (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {C : Set K} (hC : IsCompact C) :
    ∃ k : ℕ, ∀ z ∈ C, (π : K) ^ k * z ∈ R := by
  obtain ⟨k, hk⟩ := hC.elim_directed_cover (fun k : ℕ => {z | (π : K) ^ k * z ∈ R})
    (fun k => hd.isOpen.preimage (by fun_prop)) (fun z _ => Set.mem_iUnion.2 (hπ' z))
    (directed_of_isDirected_le (fun i j hij z hz => pow_mem_mono π hπ hij hz))
  exact ⟨k, hk⟩

theorem binom2 (n : ℕ) {x : K} (hx : x ∈ R) : ∃ p ∈ R, (1 + x) ^ n = 1 + (n : K) * x + x ^ 2 * p := by
  induction n with
  | zero => exact ⟨0, R.zero_mem, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp, h⟩ := ih
    refine ⟨(n : K) + p + p * x, R.add_mem (R.add_mem (natCast_mem R n) hp) (R.mul_mem hp hx), ?_⟩
    rw [pow_succ, h]
    push_cast
    ring

theorem inv_bdd (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {C : Set K} (hC : IsCompact C)
    (hU : ∀ z ∈ C, IsUnit z) : ∃ k : ℕ, ∀ z ∈ C, ∀ zi : K, z * zi = 1 → (π : K) ^ k * zi ∈ R := by
  obtain ⟨k, hk⟩ := hC.elim_directed_cover
    (fun k : ℕ => {z | ∃ zi : K, z * zi = 1 ∧ (π : K) ^ k * zi ∈ R})
    (fun k => by
      rw [isOpen_iff_mem_nhds]
      rintro z0 ⟨zi0, h0, h1⟩
      have hnb : (fun z => zi0 * (z - z0)) ⁻¹' (mulR R ((π : K) ^ 1) : Set K) ∈ 𝓝 z0 := by
        apply (show Continuous fun z => zi0 * (z - z0) by fun_prop).continuousAt.preimage_mem_nhds
        simpa using J_nhds π hd 1
      filter_upwards [hnb] with z hz
      obtain ⟨u, hu, hu2⟩ := one_add_unit π hd hn hπ hπ' _ hz
      refine ⟨zi0 * u, ?_, ?_⟩
      · have hu2 : (1 + zi0 * (z - z0)) * u = 1 := hu2
        linear_combination hu2 + u * h0
      · rw [← mul_assoc]; exact R.mul_mem h1 hu)
    (fun z hz => by
      obtain ⟨u, rfl⟩ := hU z hz
      obtain ⟨k, hk⟩ := hπ' ((u⁻¹ : Kˣ) : K)
      exact Set.mem_iUnion.2 ⟨k, _, by simp, hk⟩)
    (directed_of_isDirected_le (fun i j hij z hz => by
      obtain ⟨zi, h0, h1⟩ := hz
      exact ⟨zi, h0, pow_mem_mono π hπ hij h1⟩))
  refine ⟨k, fun z hz zi hzi => ?_⟩
  obtain ⟨zi', h0, h1⟩ := hk hz
  have : zi = zi' := by linear_combination zi' * hzi - zi * h0
  rwa [this]

section Local

variable (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
  (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {m k k' i : ℕ} {si z0 z0i : K}
  (hs : ((m + 1 : ℕ) : K) * si = 1) (hk : (π : K) ^ k * si ∈ R) (hz0 : z0 * z0i = 1)
  (hk' : (π : K) ^ k' * z0i ∈ R)

include hπ hk' in
theorem small_quot {b : K} (hb : b ∈ mulR R ((π : K) ^ (k + 1 + k' + i))) :
    b * z0i ∈ mulR R ((π : K) ^ (k + 1)) := by
  obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hb
  exact mem_mulR.2 ⟨(π : K) ^ i * ((π : K) ^ k' * z0i) * r,
    R.mul_mem (R.mul_mem (R.pow_mem hπ i) hk') hr, by ring⟩

include hπ hs hk hz0 hk' in
theorem hb1 {z : K} (hz : z - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i))) :
    ∃ b ∈ mulR R ((π : K) ^ (k + 1 + k' + i)),
      z ^ (m + 1) - z0 ^ (m + 1) = ((m + 1 : ℕ) : K) * z0 ^ m * b := by
  obtain ⟨e, he, h⟩ := pow_diff0 π hπ hs hk (small_quot π hπ hk' hz)
  refine ⟨(z - z0) * (1 + e), mulR_mul hz (one_add_mem π hπ he), ?_⟩
  have e1 : z = z0 * (1 + (z - z0) * z0i) := by linear_combination (z0 - z) * hz0
  have e2 : z ^ (m + 1) = z0 ^ (m + 1) * (1 + (z - z0) * z0i) ^ (m + 1) := by
    rw [← mul_pow, ← e1]
  rw [e2]
  linear_combination z0 ^ (m + 1) * h +
    ((m + 1 : ℕ) : K) * z0 ^ m * (z - z0) * (1 + e) * hz0

include hd hn hπ hπ' hs hk hz0 hk' in
theorem hb2 {z z' : K} (hz : z - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)))
    (hz' : z' - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i))) (h : z ^ (m + 1) = z' ^ (m + 1)) :
    z = z' := by
  obtain ⟨e, he, h1⟩ := pow_diff π hπ hs hk (small_quot π hπ hk' hz) (small_quot π hπ hk' hz')
  obtain ⟨u, -, hu⟩ := one_add_unit π hd hn hπ hπ' e he
  have e1 : z = z0 * (1 + (z - z0) * z0i) := by linear_combination (z0 - z) * hz0
  have e1' : z' = z0 * (1 + (z' - z0) * z0i) := by linear_combination (z0 - z') * hz0
  have e2 : z ^ (m + 1) = z0 ^ (m + 1) * (1 + (z - z0) * z0i) ^ (m + 1) := by
    rw [← mul_pow, ← e1]
  have e2' : z' ^ (m + 1) = z0 ^ (m + 1) * (1 + (z' - z0) * z0i) ^ (m + 1) := by
    rw [← mul_pow, ← e1']
  have hp : z0 ^ (m + 1) * z0i ^ (m + 1) = 1 := by rw [← mul_pow, hz0, one_pow]
  have h3 : (1 + (z - z0) * z0i) ^ (m + 1) - (1 + (z' - z0) * z0i) ^ (m + 1) = 0 := by
    linear_combination z0i ^ (m + 1) * (h - e2 + e2') -
      ((1 + (z - z0) * z0i) ^ (m + 1) - (1 + (z' - z0) * z0i) ^ (m + 1)) * hp
  rw [h3] at h1

  have h4 : (z - z0) * z0i - (z' - z0) * z0i = 0 := by
    linear_combination (-(si * u)) * h1 -
      ((z - z0) * z0i - (z' - z0) * z0i) * (hu + (1 + e) * u * hs)
  linear_combination z0 * h4 - (z - z') * hz0

include hd hn hπ hπ' hs hk hz0 hk' in
theorem hb3 {b : K} (hb : b ∈ mulR R ((π : K) ^ (k + 1 + k' + i))) :
    ∃ z, z - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)) ∧
      z ^ (m + 1) = z0 ^ (m + 1) + ((m + 1 : ℕ) : K) * z0 ^ m * b := by
  obtain ⟨l, hl, h⟩ := root_exists π hd hn hπ hπ' hs hk (small_quot π hπ hk' hb)
  obtain ⟨e, he, h1⟩ := pow_diff0 π hπ hs hk hl
  obtain ⟨u, hu, hu2⟩ := one_add_unit π hd hn hπ hπ' e he
  have h2 : b * z0i = l * (1 + e) := by
    linear_combination si * (h1 - h) - (b * z0i - l * (1 + e)) * hs
  have h3 : z0 * l = b * u := by
    linear_combination (-(z0 * u)) * h2 - z0 * l * hu2 + b * u * hz0
  refine ⟨z0 * (1 + l), ?_, ?_⟩
  · have : z0 * (1 + l) - z0 = b * u := by linear_combination h3
    rw [this]
    exact mulR_mul hb hu
  · rw [mul_pow, h]
    linear_combination ((m + 1 : ℕ) : K) * z0 ^ m * b * hz0

end Local

theorem card_map_mk (L : AddSubgroup K) :
    Nat.card (L.map (QuotientAddGroup.mk' R.toAddSubgroup)) = R.toAddSubgroup.relIndex L := by
  rw [← AddSubgroup.relIndex_bot_left, ← AddSubgroup.relIndex_comap, AddMonoidHom.comap_bot,
    QuotientAddGroup.ker_mk']

theorem loc_count (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {m k k' i : ℕ} {si z0 z0i : K}
    (hs : ((m + 1 : ℕ) : K) * si = 1) (hk : (π : K) ^ k * si ∈ R) (hz0 : z0 * z0i = 1)
    (hk' : (π : K) ^ k' * z0i ∈ R) (T : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (hcr : IsCr R cr)
    (a : Kˣ) (ha : (a : K) * (T : K) = ((m + 1 : ℕ) : K) * z0 ^ m * (π : K) ^ (k + 1 + k' + i))
    (haR : ((a⁻¹ : Kˣ) : K) ∈ R) :
    {p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)) ∧
      p.2 ^ (m + 1) = T * cr p.1}.Finite ∧
    ({p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)) ∧
      p.2 ^ (m + 1) = T * cr p.1}.ncard : ℝ) = modK R (a : K) := by
  set S : Set ((K ⧸ R.toAddSubgroup) × Kˣ) :=
    {p | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i)) ∧ p.2 ^ (m + 1) = T * cr p.1} with hS
  obtain ⟨c0, hc0⟩ : ∃ c0 : K, c0 = z0 ^ (m + 1) * ((T⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hTi : (T : K) * ((T⁻¹ : Kˣ) : K) = 1 := by simp
  have hai : (a : K) * ((a⁻¹ : Kˣ) : K) = 1 := by simp
  have hle : R.toAddSubgroup ≤ mulR R (a : K) := by
    intro r hr
    exact mem_mulR.2 ⟨((a⁻¹ : Kˣ) : K) * r, R.mul_mem haR hr, by rw [← mul_assoc, hai, one_mul]⟩
  set X : Set (K ⧸ R.toAddSubgroup) := (fun x => ((c0 : K) : K ⧸ R.toAddSubgroup) + x) ''
    ((mulR R (a : K)).map (QuotientAddGroup.mk' R.toAddSubgroup) : Set (K ⧸ R.toAddSubgroup)) with hX
  have hinj : Set.InjOn Prod.fst S := by
    rintro ⟨x, z⟩ ⟨h1, h2⟩ ⟨x', z'⟩ ⟨h1', h2'⟩ hxx
    simp only at hxx h1 h2 h1' h2'
    subst hxx
    have h3 : (z : K) ^ (m + 1) = (z' : K) ^ (m + 1) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h2, h2']
    have := hb2 π hd hn hπ hπ' hs hk hz0 hk' h1 h1' h3
    rw [Units.ext this]
  have himg : Prod.fst '' S = X := by
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨x, z⟩, ⟨h1, h2⟩, rfl⟩
      simp only at h1 h2 ⊢
      obtain ⟨b, hb, h3⟩ := hb1 π hπ hs hk hz0 hk' h1
      obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hb
      have h4 : (z : K) ^ (m + 1) = (T : K) * (cr x : K) := by
        rw [← Units.val_pow_eq_pow_val, h2, Units.val_mul]
      have h5 : (cr x : K) = c0 + (a : K) * r := by
        rw [hc0]
        linear_combination ((T⁻¹ : Kˣ) : K) * (h3 - h4 - r * ha) +
          ((a : K) * r - (cr x : K)) * hTi
      refine ⟨(((a : K) * r : K) : K ⧸ R.toAddSubgroup), ⟨(a : K) * r, mem_mulR.2 ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
      show ((c0 : K) : K ⧸ R.toAddSubgroup) + (((a : K) * r : K) : K ⧸ R.toAddSubgroup) = x
      rw [← QuotientAddGroup.mk_add, ← h5]
      exact hcr x
    · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hl
      set x : K ⧸ R.toAddSubgroup := ((c0 : K) : K ⧸ R.toAddSubgroup) +
        (QuotientAddGroup.mk' R.toAddSubgroup) ((a : K) * r) with hx
      have h1 : ((cr x : K) : K ⧸ R.toAddSubgroup) = ((c0 + (a : K) * r : K) : K ⧸ R.toAddSubgroup) := by
        rw [hcr x, hx]; rfl
      have h2 : -(c0 + (a : K) * r) + (cr x : K) ∈ R.toAddSubgroup := (QuotientAddGroup.eq).1 h1.symm
      obtain ⟨r', hr', hr2⟩ : ∃ r' ∈ R, r' = -(c0 + (a : K) * r) + (cr x : K) := ⟨_, h2, rfl⟩
      obtain ⟨ρ, hρ⟩ : ∃ ρ : K, ρ = r + ((a⁻¹ : Kˣ) : K) * r' := ⟨_, rfl⟩
      have hρR : ρ ∈ R := by rw [hρ]; exact R.add_mem hr (R.mul_mem haR hr')
      obtain ⟨z, hz, hz2⟩ := hb3 π hd hn hπ hπ' hs hk hz0 hk'
        (mem_mulR.2 ⟨ρ, hρR, rfl⟩ : (π : K) ^ (k + 1 + k' + i) * ρ ∈ _)
      have h3 : z ^ (m + 1) = (T : K) * (cr x : K) := by
        rw [hz2, hρ]
        have e1 : (cr x : K) = c0 + (a : K) * r + r' := by rw [hr2]; ring
        rw [e1, hc0]
        linear_combination (-(r + ((a⁻¹ : Kˣ) : K) * r')) * ha + (T : K) * r' * hai -
          z0 ^ (m + 1) * hTi
      have hzu : IsUnit z := by
        have : IsUnit (z ^ (m + 1)) := by rw [h3]; exact (T * cr x).isUnit
        exact (isUnit_pow_iff (by omega)).1 this
      obtain ⟨zu, rfl⟩ := hzu
      refine ⟨(x, zu), ⟨hz, ?_⟩, rfl⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, h3, Units.val_mul]
  have hcard : X.ncard = R.toAddSubgroup.relIndex (mulR R (a : K)) := by
    rw [hX, Set.ncard_image_of_injective _ (add_right_injective _), ← card_map_mk]
    exact (Nat.card_coe_set_eq _).symm
  have hne : R.toAddSubgroup.relIndex (mulR R (a : K)) ≠ 0 :=
    A5x5.relIndex_ne_zero hd.isOpen (A5x5.lat_mulR hd.isOpen hd.isCompact a).cp
  have hXfin : X.Finite := Set.finite_of_ncard_ne_zero (by rw [hcard]; exact hne)
  refine ⟨Set.Finite.of_finite_image (by rw [himg]; exact hXfin) hinj, ?_⟩
  rw [← hinj.ncard_image, himg, hcard]
  unfold modK
  rw [AddSubgroup.relIndex_eq_one.2 hle]
  simp

theorem finite_cosets {B : AddSubgroup K} (hB : IsOpen (B : Set K)) {Om : Set K}
    (hOm : IsCompact Om) : {w : K ⧸ B | (Quotient.out w : K) ∈ Om}.Finite := by
  have : DiscreteTopology (K ⧸ B) := QuotientAddGroup.discreteTopology hB
  obtain ⟨T, hT⟩ := hOm.elim_finite_subcover (fun w : K ⧸ B => {z : K | (z : K ⧸ B) = w})
    (fun w => (isOpen_discrete ({w} : Set (K ⧸ B))).preimage continuous_quot_mk)
    (fun z _ => Set.mem_iUnion.2 ⟨(z : K ⧸ B), rfl⟩)
  refine T.finite_toSet.subset ?_
  intro w hw
  obtain ⟨w', hw', h⟩ := Set.mem_iUnion₂.1 (hT hw)
  have h : ((Quotient.out w : K) : K ⧸ B) = w' := h
  rw [QuotientAddGroup.out_eq'] at h
  rw [h]
  exact hw'

theorem out_sub_mem' {B : AddSubgroup K} (z : K) :
    (Quotient.out ((z : K) : K ⧸ B) : K) - z ∈ B := by
  have h : ((Quotient.out ((z : K) : K ⧸ B) : K) : K ⧸ B) = ((z : K) : K ⧸ B) :=
    QuotientAddGroup.out_eq' _
  have := (QuotientAddGroup.eq).1 h.symm
  rwa [neg_add_eq_sub] at this

end GroundTheory

end Formalism.FourierDecayAlt.P.A6x9

namespace Formalism.FourierDecayAlt.P

open A6x9

theorem square_near_unit : Formalism.FourierDecayAlt.A6.SquareNear := by
  intro K _ _ _ R ψ hd hn
  obtain ⟨π, hπ, hπ'⟩ := hd.unif
  obtain ⟨u2, hu2⟩ := hn 2 (by norm_num)
  obtain ⟨k, hk⟩ := hπ' ((u2⁻¹ : Kˣ) : K)
  have hs : ((2 : ℕ) : K) * ((u2⁻¹ : Kˣ) : K) = 1 := by rw [← hu2]; simp
  refine ⟨(fun x => ((u2⁻¹ : Kˣ) : K) * x) ⁻¹' (mulR R ((π : K) ^ (k + 1)) : Set K), ?_, ?_⟩
  · apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using J_nhds π hd (k + 1)
  · intro a ha
    obtain ⟨l, -, hl⟩ := root_exists π hd hn hπ hπ' hs hk ha
    have e : (1 + l) ^ 2 = (a : K) := by
      rw [hl]; linear_combination ((a : K) - 1) * hs
    have hu : IsUnit (1 + l) := by
      have : IsUnit ((1 + l) ^ 2) := by rw [e]; exact a.isUnit
      exact (isUnit_pow_iff (by norm_num)).1 this
    obtain ⟨b, hb⟩ := hu
    refine ⟨b, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, hb, e]

theorem phase_difference_estimate : Formalism.FourierDecayAlt.A6.PhaseDiff := by
  intro K _ _ _ R ψ hd hn m Om Sg hOm
  obtain ⟨π, hπ, hπ'⟩ := hd.unif
  obtain ⟨su, hsu⟩ := hn (m + 1) (by omega)
  obtain ⟨si, hsi⟩ : ∃ si : K, si = ((su⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hs : ((m + 1 : ℕ) : K) * si = 1 := by rw [← hsu, hsi]; simp
  obtain ⟨k1, hk1⟩ := bdd_of_compact π hd hπ hπ' hOm
  obtain ⟨k2, hk2⟩ := bdd_of_compact π hd hπ hπ' Sg.finite_toSet.isCompact
  obtain ⟨k3, hk3⟩ := hπ' si
  obtain ⟨k, hk⟩ : ∃ k, k = k1 + k2 + k3 := ⟨_, rfl⟩
  have hkz : ∀ z ∈ Om, (π : K) ^ k * z ∈ R := fun z hz =>
    pow_mem_mono π hπ (by omega) (hk1 z hz)
  have hkσ : ∀ σ ∈ Sg, (π : K) ^ k * σ ∈ R := fun σ hσ =>
    pow_mem_mono π hπ (by omega) (hk2 σ (by simpa using hσ))
  have hks : (π : K) ^ k * si ∈ R := pow_mem_mono π hπ (by omega) hk3
  refine ⟨_, J_nhds π hd (k + 1), _, J_nhds π hd (5 * k + 1), ?_⟩
  intro t t₁ t₂ κ ht σ hσ σ' hσ' h1 h2 hκ hκE z hz
  unfold IsShift at h1 h2
  obtain ⟨r, hr, htr⟩ := mem_mulR.1 ht
  obtain ⟨X1, hX1⟩ : ∃ X : K, X = ((t₁⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ X : K, X = ((t₂⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ X : K, X = ((t⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ X : K, X = (κ : K) - 1 := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ X : K, X = σ - σ' := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ X : K, X = d * (t₂ : K) := ⟨_, rfl⟩
  have hκ' : (κ : K) = 1 + ε := by rw [hε]; ring
  have hB : (t₂ : K) * X2 = 1 := by rw [hX2]; simp
  have hD : (t : K) * x = 1 := by rw [hx]; simp
  rw [← hX1, ← hx] at h1
  rw [← hX2, ← hx] at h2
  have hkd : (π : K) ^ k * d ∈ R := by
    rw [hdd, mul_sub]; exact R.sub_mem (hkσ σ hσ) (hkσ σ' hσ')

  have ha : σ' * (t : K) ∈ mulR R ((π : K) ^ 1) :=
    mem_mulR.2 ⟨(π : K) ^ (4 * k) * ((π : K) ^ k * σ') * r,
      R.mul_mem (R.mul_mem (R.pow_mem hπ _) (hkσ σ' hσ')) hr, by rw [← htr]; ring⟩
  obtain ⟨u, huR, hu⟩ := one_add_unit π hd hn hπ hπ' _ ha
  have ht2 : (t₂ : K) = (t : K) * u := by
    linear_combination (-(t₂ : K)) * hu + u * (-(t₂ : K) * hD - (t : K) * (t₂ : K) * h2 + (t : K) * hB)
  have hδ3 : δ = (π : K) ^ (5 * k + 1) * (d * r * u) := by rw [hδ, ht2, ← htr]; ring
  have hδR : δ ∈ R := by
    have : δ = (π : K) ^ (4 * k + 1) * ((π : K) ^ k * d) * r * u := by rw [hδ3]; ring
    rw [this]
    exact R.mul_mem (R.mul_mem (R.mul_mem (R.pow_mem hπ _) hkd) hr) huR
  have hεR : ε ∈ R := by rw [hε]; exact J_sub_R π hπ hκE
  have hpow : (1 + ε) ^ (m + 1) = (1 + δ) ^ m := by
    have h3 := congrArg Units.val hκ
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mul, ← hX1, hκ'] at h3
    rw [h3]
    congr 1
    linear_combination (t₂ : K) * h1 - (t₂ : K) * h2 + hB - hδ - (t₂ : K) * hdd
  obtain ⟨p, hp, hp2⟩ := binom2 (m + 1) hεR
  obtain ⟨q, hq, hq2⟩ := binom2 m hδR
  have hE1 : 1 + ((m + 1 : ℕ) : K) * ε + ε ^ 2 * p = 1 + (m : K) * δ + δ ^ 2 * q := by
    rw [← hp2, ← hq2, hpow]
  have ha' : si * ε * p ∈ mulR R ((π : K) ^ 1) := by
    rw [hε]
    obtain ⟨r', hr', hr2⟩ := mem_mulR.1 hκE
    exact mem_mulR.2 ⟨(π : K) ^ k * si * r' * p, R.mul_mem (R.mul_mem hks hr') hp, by
      rw [← hr2]; ring⟩
  obtain ⟨w, hwR, hw⟩ := one_add_unit π hd hn hπ hπ' _ ha'
  obtain ⟨g, hg⟩ : ∃ g : K, g = w * ((m : K) + δ * q) := ⟨_, rfl⟩
  have hgR : g ∈ R := by
    rw [hg]; exact R.mul_mem hwR (R.add_mem (natCast_mem R m) (R.mul_mem hδR hq))
  have hεg : ε = δ * si * g := by
    rw [hg]
    linear_combination (-ε) * hw + w * (si * hE1 - ε * hs)
  have hd1 : X1 - X2 = d := by linear_combination h1 - h2 - hdd
  have hδ2 : δ * X2 = d := by linear_combination X2 * hδ + d * hB
  have hT : ((m + 1 : ℕ) : K) * z * X1 - ((m + 1 : ℕ) : K) * ((κ : K) * z) * X2 - z * d =
      z * d * δ * (si ^ 2 * g ^ 2 * p - q) := by
    have e1 : ((m + 1 : ℕ) : K) * z * X1 - ((m + 1 : ℕ) : K) * ((κ : K) * z) * X2 - z * d =
        z * X2 * ((m : K) * δ - ((m + 1 : ℕ) : K) * ε) := by
      rw [hκ']
      push_cast
      linear_combination ((m : K) + 1) * z * hd1 - (m : K) * z * hδ2
    have e2 : (m : K) * δ - ((m + 1 : ℕ) : K) * ε = ε ^ 2 * p - δ ^ 2 * q := by
      linear_combination -hE1
    rw [e1, e2]
    have e3 : ε ^ 2 = δ ^ 2 * si ^ 2 * g ^ 2 := by rw [hεg]; ring
    rw [e3]
    linear_combination z * δ * (si ^ 2 * g ^ 2 * p - q) * hδ2
  rw [← hX1, ← hX2, ← hdd, hT]
  have hfin : z * d * δ * (si ^ 2 * g ^ 2 * p - q) =
      (π : K) * (((π : K) ^ k * z) * ((π : K) ^ k * d) ^ 2 * ((π : K) ^ k * si) ^ 2 * r * u * g ^ 2 * p) -
      (π : K) ^ (2 * k + 1) * (((π : K) ^ k * z) * ((π : K) ^ k * d) ^ 2 * r * u * q) := by
    rw [hδ3]; ring
  rw [hfin]
  have hZ := hkz z hz
  exact R.sub_mem
    (R.mul_mem hπ (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem hZ
      (R.pow_mem hkd 2)) (R.pow_mem hks 2)) hr) huR) (R.pow_mem hgR 2)) hp))
    (R.mul_mem (R.pow_mem hπ _) (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem hZ
      (R.pow_mem hkd 2)) hr) huR) hq))

theorem padic_change_of_variables : Formalism.FourierDecayAlt.A6.ChangeVar := by
  classical
  intro K _ _ _ R ψ hd hn m hm Om Λ hOm hΛ hst hmod
  obtain ⟨hOo, hOc, hOu, hOζ⟩ := hOm
  obtain ⟨π, hπ, hπ'⟩ := hd.unif
  obtain ⟨su, hsu⟩ := hn (m + 1) (by omega)
  obtain ⟨si, hsi⟩ : ∃ si : K, si = ((su⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hs : ((m + 1 : ℕ) : K) * si = 1 := by rw [← hsu, hsi]; simp
  obtain ⟨k, hk⟩ := hπ' si
  obtain ⟨k', hk'⟩ := inv_bdd π hd hn hπ hπ' hOc hOu
  obtain ⟨i, hi⟩ := nhds_basis π hd hn hπ hπ' (Λ : Set K) (hΛ.1.mem_nhds Λ.zero_mem)
  obtain ⟨j, hj⟩ : ∃ j, j = k + 1 + k' + i := ⟨_, rfl⟩
  have hBΛ : mulR R ((π : K) ^ j) ≤ Λ := fun x hx => hi (J_anti π hπ (by omega) hx)
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨_, J_nhds π hd (j + k + k'), ?_⟩
  intro t cr f ht hcr hf
  obtain ⟨r, hr, htr⟩ := mem_mulR.1 ht
  obtain ⟨T, hT⟩ : ∃ T : Kˣ, T = (-t) ^ m := ⟨_, rfl⟩
  have hTv : (T : K) = (-(t : K)) ^ m := by rw [hT]; simp
  simp only [← hT]

  have hloc : ∀ z0 ∈ Om,
      {p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ j) ∧
        p.2 ^ (m + 1) = T * cr p.1}.Finite ∧
      ({p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ j) ∧
        p.2 ^ (m + 1) = T * cr p.1}.ncard : ℝ) =
        (modK R (t : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K) * modK R z0 ^ m * modK R ((π : K) ^ j) := by
    intro z0 hz0
    obtain ⟨zu, rfl⟩ := hOu z0 hz0
    have hzi : (zu : K) * ((zu⁻¹ : Kˣ) : K) = 1 := by simp
    have hTi : ((T⁻¹ : Kˣ) : K) * (T : K) = 1 := by simp
    have hav : ((T⁻¹ * su * zu ^ m * π ^ j : Kˣ) : K) =
        ((T⁻¹ : Kˣ) : K) * ((m + 1 : ℕ) : K) * (zu : K) ^ m * (π : K) ^ j := by
      simp [hsu]
    have h1 := loc_count π hd hn hπ hπ' (i := i) hs hk hzi (hk' _ hz0 _ hzi) T cr hcr
      (T⁻¹ * su * zu ^ m * π ^ j)
      (by rw [hav, ← hj]; linear_combination ((m + 1 : ℕ) : K) * (zu : K) ^ m * (π : K) ^ j * hTi)
      (by
        have hE : ((T⁻¹ * su * zu ^ m * π ^ j : Kˣ) : K) *
            ((-r) ^ m * (π : K) ^ ((j + k) * m') * ((π : K) ^ k * si) *
              ((π : K) ^ k' * ((zu⁻¹ : Kˣ) : K)) ^ m) = 1 := by
          have hT2 : (T : K) = (-r) ^ m * (π : K) ^ (j + (j + k) * m' + k + k' * m) := by
            rw [hTv, ← htr, hm']; ring
          have e : ((T⁻¹ * su * zu ^ m * π ^ j : Kˣ) : K) *
              ((-r) ^ m * (π : K) ^ ((j + k) * m') * ((π : K) ^ k * si) *
                ((π : K) ^ k' * ((zu⁻¹ : Kˣ) : K)) ^ m) =
              (((T⁻¹ : Kˣ) : K) * ((-r) ^ m * (π : K) ^ (j + (j + k) * m' + k + k' * m))) *
                (((m + 1 : ℕ) : K) * si) * ((zu : K) * ((zu⁻¹ : Kˣ) : K)) ^ m := by
            rw [hav]; ring
          rw [e, ← hT2, hTi, hs, hzi]; simp
        rw [Units.inv_eq_of_mul_eq_one_right hE]
        exact R.mul_mem (R.mul_mem (R.mul_mem (R.pow_mem (R.neg_mem hr) _) (R.pow_mem hπ _)) hk)
          (R.pow_mem (hk' _ hz0 _ hzi) _))
    rw [← hj] at h1
    refine ⟨h1.1, ?_⟩
    rw [h1.2, hav]
    have u1 : IsUnit (((T⁻¹ : Kˣ) : K)) := Units.isUnit _
    have u2 : IsUnit (((m + 1 : ℕ) : K)) := hn _ (by omega)
    have u3 : IsUnit ((zu : K) ^ m) := zu.isUnit.pow m
    have u4 : IsUnit ((π : K) ^ j) := π.isUnit.pow j
    rw [A5x5.modK_mul' hd ((u1.mul u2).mul u3) u4, A5x5.modK_mul' hd (u1.mul u2) u3,
      A5x5.modK_mul' hd u1 u2, modK_pow hd zu.isUnit]
    congr 3
    have h2 : modK R ((T⁻¹ : Kˣ) : K) * modK R (T : K) = 1 := by
      rw [← A5x5.modK_mul' hd u1 T.isUnit, hTi, A5x5.modK_one]
    rw [hTv, modK_pow hd t.isUnit.neg, A5x5.modK_neg] at h2
    exact eq_inv_of_mul_eq_one_left h2

  obtain ⟨B, hB⟩ : ∃ B : AddSubgroup K, B = mulR R ((π : K) ^ j) := ⟨_, rfl⟩
  rw [← hB] at hBΛ
  simp only [← hB] at hloc
  have hBlat : IsLat B := by rw [hB]; exact ⟨(lat_J π hd j).op, (lat_J π hd j).cp⟩
  have hW := finite_cosets hBlat.1 hOc
  set W : Set (K ⧸ B) := {w | (Quotient.out w : K) ∈ Om} with hWdef
  set S : Set ((K ⧸ R.toAddSubgroup) × Kˣ) := {p | (p.2 : K) ∈ Om ∧ p.2 ^ (m + 1) = T * cr p.1}
    with hSdef
  have hq : ∀ p ∈ S, (((p.2 : Kˣ) : K) : K ⧸ B) ∈ W := by
    intro p hp
    have h1 := hst _ hp.1 _ (hBΛ (out_sub_mem' (B := B) (p.2 : K)))
    have e : (p.2 : K) + ((Quotient.out (((p.2 : Kˣ) : K) : K ⧸ B) : K) - (p.2 : K)) =
      (Quotient.out (((p.2 : Kˣ) : K) : K ⧸ B) : K) := by ring
    rw [e] at h1
    exact h1
  have hfib : ∀ w ∈ W, ∀ p : (K ⧸ R.toAddSubgroup) × Kˣ,
      (p ∈ S ∧ (((p.2 : Kˣ) : K) : K ⧸ B) = w) ↔
        ((p.2 : K) - (Quotient.out w : K) ∈ B ∧ p.2 ^ (m + 1) = T * cr p.1) := by
    intro w hw p
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, h2⟩
      have := out_sub_mem' (B := B) (p.2 : K)
      rw [h3] at this
      have h4 := B.neg_mem this
      rwa [neg_sub] at h4
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, h2⟩, ?_⟩
      · have := hst _ hw _ (hBΛ h1)
        rwa [add_sub_cancel] at this
      · rw [← QuotientAddGroup.out_eq' w]
        apply (QuotientAddGroup.eq).2
        have h4 := B.neg_mem h1
        rw [neg_sub, sub_eq_neg_add] at h4
        exact h4
  have hSfin : S.Finite := by
    refine (hW.biUnion (fun w hw => (hloc _ hw).1)).subset ?_
    intro p hp
    exact Set.mem_biUnion (hq p hp) ((hfib _ (hq p hp) p).1 ⟨hp, rfl⟩)

  have step1 : ∀ x : K ⧸ R.toAddSubgroup,
      (if (cr x : K) ∈ cutSet m Om t then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = T * cr x then f (z : K) else 0 else 0) =
      ∑ᶠ z : Kˣ, (fun p : (K ⧸ R.toAddSubgroup) × Kˣ => if p ∈ S then f (p.2 : K) else 0) (x, z) := by
    intro x
    by_cases hc : (cr x : K) ∈ cutSet m Om t
    · rw [if_pos hc]
      refine finsum_congr fun z => ?_
      refine if_congr ?_ rfl rfl
      constructor
      · intro h
        refine ⟨?_, h⟩
        obtain ⟨z0, hz0, h0⟩ := hc
        obtain ⟨zu, rfl⟩ := hOu z0 hz0
        have h1 : zu ^ (m + 1) = T * cr x := by
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, h0, Units.val_mul, hTv]
        have h2 : (z * zu⁻¹) ^ (m + 1) = 1 := by
          rw [mul_pow, inv_pow, h, h1, mul_inv_cancel]
        have h3 := hOζ _ hz0 ((z * zu⁻¹ : Kˣ) : K) (by
          rw [← Units.val_pow_eq_pow_val, h2, Units.val_one])
        rw [← Units.val_mul, inv_mul_cancel_right] at h3
        exact h3
      · exact fun h => h.2
    · rw [if_neg hc]
      symm
      refine finsum_eq_zero_of_forall_eq_zero fun z => if_neg ?_
      rintro ⟨h1, h2⟩
      refine hc ⟨_, h1, ?_⟩
      rw [← Units.val_pow_eq_pow_val, h2, Units.val_mul, hTv]
  have hsupp : Function.support
      (fun p : (K ⧸ R.toAddSubgroup) × Kˣ => if p ∈ S then f (p.2 : K) else 0) ⊆
      (hSfin.toFinset : Set _) := by
    intro p hp
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hp (if_neg h)
  rw [finsum_congr step1, ← finsum_curry _ (hSfin.toFinset.finite_toSet.subset hsupp),
    finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (t := hW.toFinset)
      (g := fun p : (K ⧸ R.toAddSubgroup) × Kˣ => (((p.2 : Kˣ) : K) : K ⧸ B))
      (fun p hp => by
        rw [Set.Finite.mem_toFinset] at hp ⊢
        exact hq p hp)]

  have hG : LatInv Λ Om (fun z => ((modK R z ^ m : ℝ) : ℂ) * f z) := by
    intro z hz l hl
    simp only []
    rw [hmod z hz l hl, hf z hz l hl]
  rw [← integral_lattice_refinement_identity K R ψ hd Λ B Om _ hΛ hBlat hBΛ hOc hst hG]
  unfold intLat
  have hsupp2 : Function.support (fun y : K ⧸ B => if (Quotient.out y : K) ∈ Om then
      ((modK R (Quotient.out y : K) ^ m : ℝ) : ℂ) * f (Quotient.out y : K) else 0) ⊆
      (hW.toFinset : Set _) := by
    intro y hy
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hy (if_neg h)
  rw [finsum_eq_sum_of_support_subset _ hsupp2, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  have hw : (Quotient.out w : K) ∈ Om := hw
  rw [if_pos hw]
  have hset : ((hSfin.toFinset.filter
      (fun p : (K ⧸ R.toAddSubgroup) × Kˣ => (((p.2 : Kˣ) : K) : K ⧸ B) = w) : Finset _) : Set _) =
      {p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - (Quotient.out w : K) ∈ B ∧
        p.2 ^ (m + 1) = T * cr p.1} := by
    ext p
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact hfib w hw p
  have hconst : ∀ p ∈ hSfin.toFinset.filter
      (fun p : (K ⧸ R.toAddSubgroup) × Kˣ => (((p.2 : Kˣ) : K) : K ⧸ B) = w),
      (if p ∈ S then f (p.2 : K) else 0) = f (Quotient.out w : K) := by
    intro p hp
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hp
    rw [if_pos hp.1]
    have h1 := ((hfib w hw p).1 hp).1
    have h2 := hf _ hw _ (hBΛ h1)
    rwa [add_sub_cancel] at h2
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_coe_finset, hset]
  have h3 := (hloc _ hw).2
  have h4 : (({p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - (Quotient.out w : K) ∈ B ∧
        p.2 ^ (m + 1) = T * cr p.1}.ncard : ℕ) : ℂ) =
      (((modK R (t : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K) * modK R (Quotient.out w : K) ^ m *
        modK R ((π : K) ^ j) : ℝ) : ℂ) := by
    rw [← h3]; simp
  rw [h4]
  have h5 : volL R B = modK R ((π : K) ^ j) := by rw [hB]; rfl
  rw [h5]
  push_cast
  ring

theorem head_size_add_block : Formalism.FourierDecayAlt.A6.CSizeAddBlock := by
  intro K _ _ _ R ψ hd h m t
  unfold cSize
  rw [A5x5.modK_det_pt, A5x5.modK_det_pt, A5x5.prod_addBlock,
    A5x5.modK_mul' hd (A5x5.isUnit_prod _) (t.isUnit.pow m), modK_pow hd t.isUnit, mul_inv]

theorem gram_equality_of_vectors : Formalism.FourierDecayAlt.A6.UGramEq := by
  intro hP hC hM K _ _ _ R ψ hD m h h' t t' cr hs hcr
  have hsz : (addBlock h m t).1.sum = (addBlock h' m t').1.sum := by
    simp [addBlock, hs]
  obtain ⟨_, h2⟩ := hP K R ψ hD (addBlock h m t) (addBlock h' m t') hsz cr hcr
  have e1 : ∀ x, Ns R ψ 1 (addBlock h m t) (addBlock h' m t') (cr x) (cr x) =
      Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) := by
    intro x; simp [Ns, pt2]
  simp only [e1] at h2
  unfold uGram
  simp only [Set.mem_univ, if_true]
  rw [h2, hC K R ψ hD h m t, hC K R ψ hD h' m t']
  unfold Ns N0
  obtain ⟨ha, hab⟩ := hM K R ψ hD t t'
  obtain ⟨hb, _⟩ := hM K R ψ hD t' t
  rw [nat_tri m, hab]
  have ha' : (modK R (t : K)) ≠ 0 := ne_of_gt ha
  have hb' : (modK R (t' : K)) ≠ 0 := ne_of_gt hb
  push_cast
  have ha'' : ((modK R (t : K) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha'
  have hb'' : ((modK R (t' : K) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb'
  field_simp
  ring

end Formalism.FourierDecayAlt.P
