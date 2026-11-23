import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A6x8

theorem iso_symm {K : Type} [CommRing K] (R : Subring K) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (φ : coker R Z ≃ₗ[R] coker R Z') (hφ : φ ∈ isoZZ R Z Z') :
    φ.symm ∈ isoZZ R Z' Z := by
  refine ⟨by rw [← hφ.1]; simp, fun v' v hv => (hφ.2 v v' (by rw [← hv]; simp)).symm⟩

theorem iso_card {K : Type} [CommRing K] (R : Subring K) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) : Nat.card (isoZZ R Z' Z) = Nat.card (isoZZ R Z Z') :=
  Nat.card_congr
    { toFun := fun φ => ⟨φ.1.symm, iso_symm R Z' Z φ.1 φ.2⟩
      invFun := fun φ => ⟨φ.1.symm, iso_symm R Z Z' φ.1 φ.2⟩
      left_inv := by intro φ; ext; simp
      right_inv := by intro φ; ext; simp }

theorem kpHerm : KpHerm := by
  intro K _ R ψ w w'
  unfold Kp
  have h := AddMonoidHom.map_finsum_of_injective (starRingEnd ℂ).toAddMonoidHom
    (starRingEnd ℂ).injective (pairTerm R ψ w w')
  have h' : conj (∑ᶠ q, pairTerm R ψ w w' q) = ∑ᶠ q, conj (pairTerm R ψ w w' q) := h
  rw [h', ← finsum_comp_equiv (Equiv.prodComm (Cos R w) (Cos R w'))]
  refine finsum_congr fun q => ?_
  rcases q with ⟨q1, q2⟩
  show pairTerm R ψ w' w (q2, q1) = conj (pairTerm R ψ w w' (q1, q2))
  have hc := iso_card R (orbZ w (rep R q1)) (orbZ w' (rep R q2))
  unfold pairTerm
  by_cases h1 : IsInt R (orbZ w (rep R q1)) ∧ IsInt R (orbZ w' (rep R q2))
  · rw [if_pos h1, if_pos h1.symm, hc]; simp; ring
  · rw [if_neg h1, if_neg (fun h => h1 h.symm)]; simp

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem small_mul {C : Set K} (hC : IsCompact C) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ U ∈ 𝓝 (0 : K), ∀ u ∈ U, ∀ c ∈ C, u * c ∈ W := by
  obtain ⟨W', hW'W, hW'o, h0⟩ := mem_nhds_iff.1 hW
  have hn : IsOpen ((fun p : K × K => p.1 * p.2) ⁻¹' W') := hW'o.preimage continuous_mul
  obtain ⟨u, v, hu, -, hsu, htv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : K))) hC hn (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = 0 := ha
      simp [ha', h0])
  exact ⟨u, hu.mem_nhds (hsu rfl), fun a ha c hc => hW'W (huv (Set.mk_mem_prod ha (htv hc)))⟩

theorem small_add {Om : Set K} (hC : IsCompact Om) (hO : IsOpen Om) :
    ∃ W ∈ 𝓝 (0 : K), ∀ z ∈ Om, ∀ w ∈ W, z + w ∈ Om := by
  have hn : IsOpen ((fun p : K × K => p.1 + p.2) ⁻¹' Om) := hO.preimage continuous_add
  obtain ⟨u, v, -, hv, hsu, htv, huv⟩ :=
    generalized_tube_lemma hC (isCompact_singleton (x := (0 : K))) hn (by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      have hb' : b = 0 := hb
      simpa [hb'] using ha)
  exact ⟨v, hv.mem_nhds (htv rfl), fun z hz w hw => huv (Set.mk_mem_prod (hsu hz) hw)⟩

theorem small_scale {Om : Set K} (hC : IsCompact Om) (hO : IsOpen Om) :
    ∃ E ∈ 𝓝 (0 : K), ∀ z ∈ Om, ∀ κ : K, κ - 1 ∈ E → κ * z ∈ Om := by
  obtain ⟨W, hW, h1⟩ := small_add hC hO
  obtain ⟨E, hE, h2⟩ := small_mul hC hW
  refine ⟨E, hE, fun z hz κ hκ => ?_⟩
  have := h1 z hz _ (h2 _ hκ z hz)
  have e : z + (κ - 1) * z = κ * z := by ring
  rwa [e] at this

def I (R : Subring K) (a : K) : Set K := {x | ∃ r ∈ R, x = a * r}

theorem I_compact {R : Subring K} (hc : IsCompact (R : Set K)) (a : K) : IsCompact (I R a) := by
  have : I R a = (fun r => a * r) '' (R : Set K) := by
    ext x; constructor
    · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  rw [this]
  exact hc.image (continuous_const.mul continuous_id)

theorem I_nhds {R : Subring K} (ho : IsOpen (R : Set K)) (a : Kˣ) : I R (a : K) ∈ 𝓝 (0 : K) := by
  have : I R (a : K) = (fun x => ((a⁻¹ : Kˣ) : K) * x) ⁻¹' (R : Set K) := by
    ext x; constructor
    · rintro ⟨r, hr, rfl⟩
      show ((a⁻¹ : Kˣ) : K) * ((a : K) * r) ∈ R
      simpa using hr
    · intro hx
      exact ⟨_, hx, by simp⟩
  rw [this]
  refine (ho.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
  show ((a⁻¹ : Kˣ) : K) * 0 ∈ R
  simp

theorem inter_zero {R : Subring K} [T2Space K] [IsReduced K] (hc : IsCompact (R : Set K))
    (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (ϖ : K) (hu : ∀ x : K, ∃ m : ℕ, ϖ ^ m * x ∈ R)
    (x : K) (hx : ∀ n, x ∈ I R (ϖ ^ n)) : x = 0 := by
  by_contra hx0
  have hx2 : x ^ 2 ≠ 0 := fun h => hx0 (IsNilpotent.eq_zero ⟨2, h⟩)
  have hI : ∀ y : K, y * x ∈ R := by
    intro y
    obtain ⟨m, hm⟩ := hu y
    obtain ⟨r, hr, e⟩ := hx m
    have : y * x = ϖ ^ m * y * r := by rw [e]; ring
    rw [this]; exact R.mul_mem hm hr
  have hW : ({x ^ 2}ᶜ : Set K) ∈ 𝓝 (0 : K) := isOpen_compl_singleton.mem_nhds (by
    simpa using hx2.symm)
  obtain ⟨U, hU, hUR⟩ := small_mul hc hW
  obtain ⟨U', hU', hsub⟩ := exists_nhds_half_neg hU
  obtain ⟨a, -, ha⟩ := hc.exists_mapClusterPt (f := (atTop : Filter ℕ)) (u := fun n : ℕ => (n : K) * x)
    (le_principal_iff.2 (mem_map.2 (Filter.univ_mem' fun n : ℕ => hI (n : K))))
  have hN : {y | y - a ∈ U'} ∈ 𝓝 a := by
    have : ContinuousAt (fun y : K => y - a) a := (continuous_id.sub continuous_const).continuousAt
    exact this.preimage_mem_nhds (by simpa using hU')
  have hf := frequently_atTop.1 (ha.frequently hN)
  obtain ⟨n, -, h1⟩ := hf 0
  obtain ⟨m, hm, h2⟩ := hf (n + 1)
  have h3 := hsub _ h2 _ h1
  obtain ⟨d, rfl⟩ : ∃ d, m = n + 1 + d := ⟨m - (n + 1), by omega⟩
  have e : ((n + 1 + d : ℕ) : K) * x - a - ((n : K) * x - a) = ((d + 1 : ℕ) : K) * x := by
    push_cast; ring
  rw [e] at h3
  obtain ⟨v, hv⟩ := hn (d + 1) (by omega)
  have h4 := hUR _ h3 _ (hI ((v⁻¹ : Kˣ) : K))
  apply h4
  show ((d + 1 : ℕ) : K) * x * (((v⁻¹ : Kˣ) : K) * x) = x ^ 2
  rw [← hv]
  have : (v : K) * ((v⁻¹ : Kˣ) : K) = 1 := by simp
  linear_combination x ^ 2 * this

structure Adic (R : Subring K) (ϖ : Kˣ) : Prop where
  t2 : T2Space K
  isOpen : IsOpen (R : Set K)
  isCompact : IsCompact (R : Set K)
  mem : (ϖ : K) ∈ R
  absorb : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R
  basis : ∀ W ∈ 𝓝 (0 : K), ∃ n : ℕ, ∀ r ∈ R, (ϖ : K) ^ n * r ∈ W

theorem adic_of_datum {R : Subring K} {ψ : AddChar K ℂ} (hD : LocalDatum K R ψ)
    (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) : ∃ ϖ : Kˣ, Adic R ϖ := by
  obtain ⟨ϖ, hϖ, hu⟩ := hD.unif
  have := hD.t2
  have := hD.red
  refine ⟨ϖ, hD.t2, hD.isOpen, hD.isCompact, hϖ, hu, fun W hW => ?_⟩
  obtain ⟨W', hW'W, hW'o, h0⟩ := mem_nhds_iff.1 hW
  have hs : IsCompact ((R : Set K) ∩ W'ᶜ) := hD.isCompact.inter_right hW'o.isClosed_compl
  have hanti : Antitone fun n : ℕ => I R ((ϖ : K) ^ n) := by
    intro n m hnm x hx
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact ⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem hϖ d) hr, by ring⟩
  obtain ⟨n, hn'⟩ := hs.elim_directed_family_closed (fun n : ℕ => I R ((ϖ : K) ^ n))
    (fun n => (I_compact hD.isCompact _).isClosed) (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨⟨-, hxW⟩, hx⟩
      have := inter_zero hD.isCompact hn (ϖ : K) hu x (fun n => Set.mem_iInter.1 hx n)
      exact hxW (this ▸ h0)) hanti.directed_ge
  refine ⟨n, fun r hr => hW'W ?_⟩
  by_contra hc
  have : (ϖ : K) ^ n * r ∈ ((R : Set K) ∩ W'ᶜ) ∩ I R ((ϖ : K) ^ n) :=
    ⟨⟨R.mul_mem (R.pow_mem hϖ n) hr, hc⟩, r, hr, rfl⟩
  rw [hn'] at this
  exact this

variable {R : Subring K} {ϖ : Kˣ}

theorem Adic.approx (h : Adic R ϖ) (f : K → K) (hf : Continuous f) (b : K)
    (ha : ∀ n : ℕ, ∃ r ∈ R, ∃ e ∈ R, f r = b + (ϖ : K) ^ n * e) : ∃ r ∈ R, f r = b := by
  have := h.t2
  have hcl : IsClosed (f '' (R : Set K)) := (h.isCompact.image hf).isClosed
  have hb : b ∈ closure (f '' (R : Set K)) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    have hW : {y | b + y ∈ N} ∈ 𝓝 (0 : K) := by
      have : ContinuousAt (fun y : K => b + y) 0 := (continuous_const.add continuous_id).continuousAt
      exact this.preimage_mem_nhds (by simpa using hN)
    obtain ⟨n, hn⟩ := h.basis _ hW
    obtain ⟨r, hr, e, he, hre⟩ := ha n
    exact ⟨f r, by rw [hre]; exact hn e he, r, hr, rfl⟩
  rw [hcl.closure_eq] at hb
  obtain ⟨r, hr, e⟩ := hb
  exact ⟨r, hr, e⟩

theorem Adic.unit_one (h : Adic R ϖ) (j : K) (hj : j ∈ I R (ϖ : K)) : ∃ v ∈ R, (1 + j) * v = 1 := by
  obtain ⟨r, hr, rfl⟩ := hj
  refine h.approx (fun v => (1 + (ϖ : K) * r) * v) (continuous_const.mul continuous_id) 1 fun n => ?_
  have hjR : -((ϖ : K) * r) ∈ R := R.neg_mem (R.mul_mem h.mem hr)
  refine ⟨∑ i ∈ Finset.range n, (-((ϖ : K) * r)) ^ i, R.sum_mem fun i _ => R.pow_mem hjR i,
    -(-r) ^ n, R.neg_mem (R.pow_mem (R.neg_mem hr) n), ?_⟩
  have := mul_neg_geom_sum (-((ϖ : K) * r)) n
  have e : (-((ϖ : K) * r)) ^ n = (ϖ : K) ^ n * (-r) ^ n := by rw [← mul_pow]; ring
  show (1 + (ϖ : K) * r) * _ = _
  rw [e] at this
  linear_combination this

def Near (R : Subring K) (a x : K) : Prop := ∃ r ∈ R, x = 1 + a * r

theorem near_one (a : K) : Near R a 1 := ⟨0, R.zero_mem, by simp⟩

theorem Near.mul {a x y : K} (ha : a ∈ R) (hx : Near R a x) (hy : Near R a y) : Near R a (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨r + q + a * r * q, R.add_mem (R.add_mem hr hq) (R.mul_mem (R.mul_mem ha hr) hq), by ring⟩

theorem Near.pow {a x : K} (ha : a ∈ R) (hx : Near R a x) (n : ℕ) : Near R a (x ^ n) := by
  induction n with
  | zero => simpa using near_one a
  | succ n ih => rw [pow_succ]; exact ih.mul ha hx

theorem Adic.near_inv (h : Adic R ϖ) {a x : K} (ha : a ∈ I R (ϖ : K)) (hx : Near R a x) :
    ∃ v, x * v = 1 ∧ Near R a v ∧ v ∈ R := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨v, hv, e⟩ := h.unit_one ((ϖ : K) * a' * r) ⟨a' * r, R.mul_mem ha' hr, by ring⟩
  exact ⟨v, e, ⟨-(r * v), R.neg_mem (R.mul_mem hr hv), by linear_combination e⟩, hv⟩

theorem near_sum {a : K} (n : ℕ) (f : ℕ → K) (hf : ∀ i, Near R a (f i)) :
    ∃ q ∈ R, ∑ i ∈ Finset.range n, f i = (n : K) + a * q := by
  induction n with
  | zero => exact ⟨0, R.zero_mem, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, e⟩ := ih
    obtain ⟨r, hr, e'⟩ := hf n
    exact ⟨q + r, R.add_mem hq hr, by rw [Finset.sum_range_succ, e, e']; push_cast; ring⟩

theorem pow_diff {c : K} (hc : c ∈ R) (s : ℕ) {x y : K} (hx : Near R ((s : K) * c) x)
    (hy : Near R ((s : K) * c) y) : ∃ q ∈ R, x ^ s - y ^ s = (s : K) * (x - y) * (1 + c * q) := by
  have ha : (s : K) * c ∈ R := R.mul_mem (natCast_mem R s) hc
  obtain ⟨q, hq, e⟩ := near_sum (R := R) s (fun i => x ^ i * y ^ (s - 1 - i))
    (fun i => (hx.pow ha i).mul ha (hy.pow ha _))
  refine ⟨q, hq, ?_⟩
  rw [← geom_sum₂_mul, e]; ring

theorem Adic.root (h : Adic R ϖ) (s : ℕ) {c : K} (hc : c ∈ I R (ϖ : K)) {b : K}
    (hb : Near R ((s : K) ^ 2 * c) b) : ∃ κ, Near R ((s : K) * c) κ ∧ κ ^ s = b := by
  obtain ⟨c', hc', hcc⟩ := hc
  have hcR : c ∈ R := by rw [hcc]; exact R.mul_mem h.mem hc'
  have key : ∀ k : ℕ, ∃ r ∈ R, ∃ e ∈ R, (1 + (s : K) * c * r) ^ s = b + (s : K) ^ 2 * c ^ (k + 1) * e := by
    intro k
    induction k with
    | zero =>
      obtain ⟨r0, hr0, e0⟩ := hb
      exact ⟨0, R.zero_mem, -r0, R.neg_mem hr0, by rw [e0]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr, e, he, hre⟩ := ih
      have hr' : r - c ^ k * e ∈ R := R.sub_mem hr (R.mul_mem (R.pow_mem hcR k) he)
      obtain ⟨q, hq, hd⟩ := pow_diff (R := R) hcR s (x := 1 + (s : K) * c * (r - c ^ k * e))
        (y := 1 + (s : K) * c * r) ⟨_, hr', rfl⟩ ⟨_, hr, rfl⟩
      refine ⟨_, hr', -(e * q), R.neg_mem (R.mul_mem he hq), ?_⟩
      linear_combination hd + hre
  obtain ⟨r, hr, e⟩ := h.approx (fun r => (1 + (s : K) * c * r) ^ s)
    ((continuous_const.add (continuous_const.mul continuous_id)).pow s) b (fun n => by
      obtain ⟨r, hr, e, he, hre⟩ := key n
      refine ⟨r, hr, (s : K) ^ 2 * ((ϖ : K) * c' ^ (n + 1)) * e,
        R.mul_mem (R.mul_mem (R.pow_mem (natCast_mem R s) 2)
          (R.mul_mem h.mem (R.pow_mem hc' _))) he, ?_⟩
      show (1 + (s : K) * c * r) ^ s = _
      rw [hre, hcc]; ring)
  exact ⟨_, ⟨r, hr, rfl⟩, e⟩

theorem Adic.shift_small (h : Adic R ϖ) (Sg : Finset K) (a : Kˣ) :
    ∃ V ∈ 𝓝 (0 : K), ∀ t ∈ V, ∀ σ ∈ Sg, σ * t ∈ I R (a : K) := by
  refine ⟨⋂ σ ∈ Sg, (fun t => σ * t) ⁻¹' I R (a : K),
    (Filter.biInter_finset_mem Sg).2 fun σ _ => ?_, fun t ht σ hσ => ?_⟩
  · have : ContinuousAt (fun t : K => σ * t) 0 := (continuous_const.mul continuous_id).continuousAt
    exact this.preimage_mem_nhds (by simpa using I_nhds h.isOpen a)
  · exact Set.mem_iInter₂.1 ht σ hσ

theorem shift_alg (t t₁ : Kˣ) (σ : K) (h : IsShift t t₁ σ) :
    (t₁ : K) * (1 + σ * (t : K)) = (t : K) := by
  unfold IsShift at h
  have h1 : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := by simp
  have h2 : ((t⁻¹ : Kˣ) : K) * (t : K) = 1 := by simp
  rw [h] at h1
  linear_combination (t : K) * h1 - (t₁ : K) * h2

theorem Adic.root_near (h : Adic R ϖ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (s : ℕ) (hs : 1 ≤ s)
    {E : Set K} (hE : E ∈ 𝓝 (0 : K)) :
    ∃ a : Kˣ, (a : K) ∈ I R (ϖ : K) ∧ ∀ b : K, Near R (a : K) b → ∃ κ : K, κ ^ s = b ∧ κ - 1 ∈ E := by
  obtain ⟨N, hN⟩ := h.basis E hE
  obtain ⟨u, hu⟩ := hn s (by omega)
  have hsR : (s : K) ∈ R := natCast_mem R s
  refine ⟨u ^ 2 * ϖ ^ (N + 1), ⟨(s : K) ^ 2 * (ϖ : K) ^ N,
    R.mul_mem (R.pow_mem hsR 2) (R.pow_mem h.mem N), by push_cast; rw [hu]; ring⟩, fun b hb => ?_⟩
  have hb' : Near R ((s : K) ^ 2 * (ϖ : K) ^ (N + 1)) b := by
    have e : ((u ^ 2 * ϖ ^ (N + 1) : Kˣ) : K) = (s : K) ^ 2 * (ϖ : K) ^ (N + 1) := by
      push_cast; rw [hu]
    rwa [e] at hb
  obtain ⟨κ, ⟨r, hr, e⟩, hκ⟩ := h.root s (c := (ϖ : K) ^ (N + 1))
    ⟨(ϖ : K) ^ N, R.pow_mem h.mem N, by ring⟩ hb'
  refine ⟨κ, hκ, ?_⟩
  have : κ - 1 = (ϖ : K) ^ N * ((ϖ : K) * (s : K) * r) := by rw [e]; ring
  rw [this]
  exact hN _ (R.mul_mem (R.mul_mem h.mem hsR) hr)

theorem Adic.inv_bounded (h : Adic R ϖ) {Om : Set K} (hC : IsCompact Om) (hU : ∀ z ∈ Om, IsUnit z) :
    ∃ M : ℕ, ∀ z ∈ Om, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R := by
  refine hC.induction_on
    (p := fun S => ∃ M : ℕ, ∀ z ∈ S, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R)
    ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨M, hM⟩
    exact ⟨M, fun z hz => hM z (hST hz)⟩
  · rintro S T ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', fun z hz z' e => ?_⟩
    rcases hz with hz | hz
    · have := R.mul_mem (R.pow_mem h.mem M') (hM z hz z' e)
      have e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M' * ((ϖ : K) ^ M * z') := by ring
      rwa [e']
    · have := R.mul_mem (R.pow_mem h.mem M) (hM' z hz z' e)
      have e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M * ((ϖ : K) ^ M' * z') := by ring
      rwa [e']
  · intro x hx
    obtain ⟨u, rfl⟩ := hU x hx
    obtain ⟨M, hM⟩ := h.absorb ((u⁻¹ : Kˣ) : K)
    refine ⟨{z | (z - (u : K)) * ((u⁻¹ : Kˣ) : K) ∈ I R (ϖ : K)}, mem_nhdsWithin_of_mem_nhds ?_, M,
      fun z hz z' e => ?_⟩
    · have : ContinuousAt (fun z : K => (z - (u : K)) * ((u⁻¹ : Kˣ) : K)) (u : K) :=
        ((continuous_id.sub continuous_const).mul continuous_const).continuousAt
      exact this.preimage_mem_nhds (by simpa using I_nhds h.isOpen ϖ)
    · obtain ⟨v, hv, ev⟩ := h.unit_one _ hz
      have i1 : (u : K) * ((u⁻¹ : Kˣ) : K) = 1 := by simp
      have : z' = ((u⁻¹ : Kˣ) : K) * v := by
        linear_combination ((u⁻¹ : Kˣ) : K) * v * e - z' * v * i1 - z' * ev
      rw [this, ← mul_assoc]
      exact R.mul_mem hM hv

end Top

theorem shiftUnit : ShiftUnit := by
  intro K _ _ _ R ψ hD hn Sg
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg ϖ
  refine ⟨V, hV, fun t ht σ hσ => ?_⟩
  have hj := hVs _ ht σ hσ
  obtain ⟨v, hv, e⟩ := h.unit_one _ hj
  have hjR : 1 + σ * (t : K) ∈ R := by
    obtain ⟨r, hr, e'⟩ := hj
    rw [e']; exact R.add_mem R.one_mem (R.mul_mem h.mem hr)
  have hx : ((t⁻¹ : Kˣ) : K) + σ = ((t⁻¹ : Kˣ) : K) * (1 + σ * (t : K)) := by
    have : ((t⁻¹ : Kˣ) : K) * (t : K) = 1 := by simp
    linear_combination -σ * this
  rw [hx]
  refine ⟨(Units.isUnit _).mul (isUnit_iff_exists_inv.2 ⟨v, e⟩), ?_⟩
  have : mulR R (((t⁻¹ : Kˣ) : K) * (1 + σ * (t : K))) = mulR R ((t⁻¹ : Kˣ) : K) := by
    ext y
    simp only [mulR, AddSubgroup.mem_map, Subring.mem_toAddSubgroup, AddMonoidHom.coe_mulLeft]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(1 + σ * (t : K)) * r, R.mul_mem hjR hr, by ring⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨v * r, R.mul_mem hv hr, by linear_combination ((t⁻¹ : Kˣ) : K) * r * e⟩
  unfold modK
  rw [this]

theorem shiftSmall : ShiftSmall := by
  intro K _ _ _ R ψ hD hn Sg W hW
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg ϖ
  obtain ⟨n, hn'⟩ := h.basis W hW
  refine ⟨V ∩ I R ((ϖ ^ n : Kˣ) : K), inter_mem hV (I_nhds h.isOpen _),
    fun t t₁ ht σ hσ hs => ?_⟩
  obtain ⟨v, hv, e⟩ := h.unit_one _ (hVs _ ht.1 σ hσ)
  obtain ⟨r, hr, e'⟩ := ht.2
  have h1 := shift_alg t t₁ σ hs
  have : (t₁ : K) = (ϖ : K) ^ n * (r * v) := by
    push_cast at e'
    linear_combination (-(t₁ : K)) * e + v * h1 + v * e'
  rw [this]
  exact hn' _ (R.mul_mem hr hv)

theorem rootCorr : RootCorr := by
  intro K _ _ _ R ψ hD hn m Sg E hE
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨a, ha, hroot⟩ := h.root_near hn (m + 1) (by omega) hE
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg a
  refine ⟨V, hV, fun t t₁ t₂ ht σ hσ σ' hσ' hs hs' => ?_⟩
  have haR : (a : K) ∈ R := by
    obtain ⟨r, hr, e⟩ := ha
    rw [e]; exact R.mul_mem h.mem hr
  have n1 : Near R (a : K) (1 + σ * (t : K)) := by
    obtain ⟨r, hr, e⟩ := hVs _ ht σ hσ
    exact ⟨r, hr, by rw [e]⟩
  have n2 : Near R (a : K) (1 + σ' * (t : K)) := by
    obtain ⟨r, hr, e⟩ := hVs _ ht σ' hσ'
    exact ⟨r, hr, by rw [e]⟩
  obtain ⟨v, hv, nv, -⟩ := h.near_inv ha n2
  have a1 := shift_alg t t₁ σ hs
  have a2 := shift_alg t t₂ σ' hs'
  have hr : ((t₂ * t₁⁻¹ : Kˣ) : K) = (1 + σ * (t : K)) * v := by
    have i1 : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := by simp
    rw [Units.val_mul]
    linear_combination (-((t₂ : K) * ((t₁⁻¹ : Kˣ) : K))) * hv + ((t₁⁻¹ : Kˣ) : K) * v * a2 -
      ((t₁⁻¹ : Kˣ) : K) * v * a1 + (1 + σ * (t : K)) * v * i1
  obtain ⟨κ, hκ, hκE⟩ := hroot _ ((n1.mul haR nv).pow haR m)
  rw [← hr, ← Units.val_pow_eq_pow_val] at hκ
  have hu : IsUnit κ := by
    have : IsUnit (κ ^ (m + 1)) := by rw [hκ]; exact Units.isUnit _
    exact (isUnit_pow_iff (by omega)).1 this
  obtain ⟨κ', rfl⟩ := hu
  exact ⟨κ', Units.ext (by rw [Units.val_pow_eq_pow_val, hκ]), hκE⟩

theorem cutSame : CutSame := by
  intro K _ _ _ R ψ hD hn m hm Om Sg hOm
  obtain ⟨hO, hC, hU, -⟩ := hOm
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨E, hE, hscale⟩ := small_scale hC hO
  obtain ⟨a, ha, hroot⟩ := h.root_near hn (m + 1) (by omega) hE
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg a
  obtain ⟨M, hM⟩ := h.inv_bounded hC hU
  have haR : (a : K) ∈ R := by
    obtain ⟨r, hr, e⟩ := ha
    rw [e]; exact R.mul_mem h.mem hr
  have step : ∀ A b : K, Near R (a : K) b → (∃ z ∈ Om, z ^ (m + 1) = A) →
      ∃ z ∈ Om, z ^ (m + 1) = A * b := by
    rintro A b hb ⟨z, hz, rfl⟩
    obtain ⟨κ, hκ, hκE⟩ := hroot b hb
    exact ⟨κ * z, hscale z hz κ hκE, by rw [mul_pow, hκ]; ring⟩
  refine ⟨V ∩ I R ((a * ϖ ^ (M * (m + 1)) : Kˣ) : K), inter_mem hV (I_nhds h.isOpen _),
    fun t ht => ⟨fun σ hσ t₁ hs => ?_, fun c hc r hr => ?_⟩⟩
  · have n1 : Near R (a : K) (1 + σ * (t : K)) := by
      obtain ⟨r, hr, e⟩ := hVs _ ht.1 σ hσ
      exact ⟨r, hr, by rw [e]⟩
    obtain ⟨v, hv, nv, -⟩ := h.near_inv ha n1
    have a1 := shift_alg t t₁ σ hs
    have e1 : (t₁ : K) = (t : K) * v := by linear_combination (-(t₁ : K)) * hv + v * a1
    ext c
    constructor
    · intro hc
      have := step ((-(t₁ : K)) ^ m * c) _ (n1.pow haR m) hc
      have e2 : (-(t₁ : K)) ^ m * c * (1 + σ * (t : K)) ^ m = (-(t : K)) ^ m * c := by
        have e3 : -(t : K) = -(t₁ : K) * (1 + σ * (t : K)) := by linear_combination a1
        rw [e3, mul_pow]; ring
      rwa [e2] at this
    · intro hc
      have := step ((-(t : K)) ^ m * c) _ (nv.pow haR m) hc
      have e2 : (-(t : K)) ^ m * c * v ^ m = (-(t₁ : K)) ^ m * c := by rw [e1]; ring
      rwa [e2] at this
  · obtain ⟨z, hz, e⟩ := hc
    obtain ⟨u, rfl⟩ := hU z hz
    have hb := hM _ hz ((u⁻¹ : Kˣ) : K) (by simp)
    obtain ⟨r1, hr1, et⟩ := ht.2
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    push_cast at et
    have htR : (t : K) ∈ R := by
      rw [et]; exact R.mul_mem (R.mul_mem haR (R.pow_mem h.mem _)) hr1
    have nb : Near R (a : K)
        (1 + (-(t : K)) ^ (m' + 1) * r * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1)) :=
      ⟨-(r1 * (-(t : K)) ^ m' * r * ((ϖ : K) ^ M * ((u⁻¹ : Kˣ) : K)) ^ (m' + 1 + 1)),
        R.neg_mem (R.mul_mem (R.mul_mem (R.mul_mem hr1 (R.pow_mem (R.neg_mem htR) _)) hr)
          (R.pow_mem hb _)), by
        linear_combination (-((-(t : K)) ^ m' * r * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1))) * et⟩
    have := step _ _ nb ⟨u, hz, rfl⟩
    have i1 : (u : K) ^ (m' + 1 + 1) * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1) = 1 := by
      rw [← mul_pow]; simp
    have e2 : (u : K) ^ (m' + 1 + 1) *
        (1 + (-(t : K)) ^ (m' + 1) * r * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1)) =
        (-(t : K)) ^ (m' + 1) * (c + r) := by
      linear_combination e + (-(t : K)) ^ (m' + 1) * r * i1
    rwa [e2] at this

end Formalism.FourierDecayAlt.P.A6x8

theorem Formalism.FourierDecayAlt.P.gramKernelHermitian : Formalism.FourierDecayAlt.A6.KpHerm := Formalism.FourierDecayAlt.P.A6x8.kpHerm

theorem Formalism.FourierDecayAlt.P.shiftUnit_statement : Formalism.FourierDecayAlt.A6.ShiftUnit := Formalism.FourierDecayAlt.P.A6x8.shiftUnit

theorem Formalism.FourierDecayAlt.P.shiftSmall_statement : Formalism.FourierDecayAlt.A6.ShiftSmall := Formalism.FourierDecayAlt.P.A6x8.shiftSmall

theorem Formalism.FourierDecayAlt.P.rootCutStable : Formalism.FourierDecayAlt.A6.CutSame := Formalism.FourierDecayAlt.P.A6x8.cutSame

theorem Formalism.FourierDecayAlt.P.rootCorrection : Formalism.FourierDecayAlt.A6.RootCorr := Formalism.FourierDecayAlt.P.A6x8.rootCorr
