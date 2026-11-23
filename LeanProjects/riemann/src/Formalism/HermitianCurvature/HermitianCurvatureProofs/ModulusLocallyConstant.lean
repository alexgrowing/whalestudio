import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P

namespace A6x4

section Alg

variable {K : Type} [CommRing K]

theorem sum_reps_eq_zero {L₁ L₂ : AddSubgroup K} {S : Finset K} (hle : L₁ ≤ L₂)
    (hS : IsReps S L₂ L₁) (f : K → ℂ) (hmul : ∀ x ∈ L₂, ∀ y ∈ L₂, f (x + y) = f x * f y)
    (h1 : ∀ l ∈ L₁, f l = 1) {l₀ : K} (hl₀ : l₀ ∈ L₂) (hne : f l₀ ≠ 1) : ∑ σ ∈ S, f σ = 0 := by
  classical
  choose! ρ hρ using fun l hl => (hS.2 l hl).exists
  have huniq : ∀ l ∈ L₂, ∀ y ∈ S, l - y ∈ L₁ → y = ρ l :=
    fun l hl y hy h => (hS.2 l hl).unique ⟨hy, h⟩ (hρ l hl)
  have key : ∀ l ∈ L₂, f (ρ l) = f l := by
    intro l hl
    have h := hρ l hl
    have e : f l = f (ρ l) * f (l - ρ l) := by
      rw [← hmul _ (hS.1 _ h.1) _ (hle h.2)]
      congr 1
      ring
    rw [e, h1 _ h.2, mul_one]
  have hsum : ∑ σ ∈ S, f (σ + l₀) = ∑ σ ∈ S, f σ := by
    refine Finset.sum_nbij' (fun σ => ρ (σ + l₀)) (fun σ => ρ (σ - l₀)) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      exact (hρ _ (L₂.add_mem (hS.1 σ hσ) hl₀)).1
    · intro σ hσ
      exact (hρ _ (L₂.sub_mem (hS.1 σ hσ) hl₀)).1
    · intro σ hσ
      have h := hρ _ (L₂.add_mem (hS.1 σ hσ) hl₀)
      refine (huniq _ (L₂.sub_mem (hS.1 _ h.1) hl₀) σ hσ ?_).symm
      have := L₁.neg_mem h.2
      have e : ρ (σ + l₀) - l₀ - σ = -(σ + l₀ - ρ (σ + l₀)) := by ring
      rw [e]
      exact this
    · intro σ hσ
      have h := hρ _ (L₂.sub_mem (hS.1 σ hσ) hl₀)
      refine (huniq _ (L₂.add_mem (hS.1 _ h.1) hl₀) σ hσ ?_).symm
      have := L₁.neg_mem h.2
      have e : ρ (σ - l₀) + l₀ - σ = -(σ - l₀ - ρ (σ - l₀)) := by ring
      rw [e]
      exact this
    · intro σ hσ
      exact (key _ (L₂.add_mem (hS.1 σ hσ) hl₀)).symm
  have h2 : ∑ σ ∈ S, f (σ + l₀) = (∑ σ ∈ S, f σ) * f l₀ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ hσ => hmul _ (hS.1 σ hσ) _ hl₀
  have h3 : (∑ σ ∈ S, f σ) * (f l₀ - 1) = 0 := by
    rw [mul_sub, ← h2, hsum, mul_one, sub_self]
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hne)

theorem reps_nonempty {L₁ L₂ : AddSubgroup K} {S : Finset K} (hS : IsReps S L₂ L₁) :
    S.Nonempty := by
  obtain ⟨a, ha, _⟩ := hS.2 0 L₂.zero_mem
  exact ⟨a, ha.1⟩

theorem ringInv_eq {z a : K} (h : z * a = 1) : Ring.inverse z = a := by
  have hz : IsUnit z := IsUnit.of_mul_eq_one a h
  calc Ring.inverse z = Ring.inverse z * (z * a) := by rw [h, mul_one]
    _ = (Ring.inverse z * z) * a := by ring
    _ = a := by rw [Ring.inverse_mul_cancel z hz, one_mul]

theorem addChar_ne_zero {G : Type} [AddGroup G] (φ : AddChar G ℂ) (x : G) : φ x ≠ 0 := by
  intro h
  have := φ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem mem_mulR_iff {R : Subring K} {a b : K} (hab : a * b = 1) (x : K) :
    x ∈ mulR R a ↔ b * x ∈ R := by
  unfold mulR
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have e : b * (AddMonoidHom.mulLeft a) r = r := by
      rw [AddMonoidHom.coe_mulLeft]
      linear_combination r * hab
    rw [e]
    exact hr
  · intro h
    refine ⟨b * x, h, ?_⟩
    rw [AddMonoidHom.coe_mulLeft]
    linear_combination x * hab

theorem pow_mul_pow_one {p q : K} (hpq : p * q = 1) (m : ℕ) : p ^ m * q ^ m = 1 := by
  rw [← mul_pow, hpq, one_pow]

theorem vnr [IsArtinianRing K] [IsReduced K] (z : K) : ∃ c, z = z * z * c := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd z (1 : K)
  simp only [smul_eq_mul, mul_one] at hy
  have h0 : (z * (1 - z * y)) ^ (n + 1) = 0 := by
    have e1 : ∀ w : K, (z * w) ^ (n + 1) = (z ^ n * w) * (z * w ^ n) := by
      intro w
      rw [mul_pow]
      ring
    have e2 : z ^ n * (1 - z * y) = z ^ n - z ^ (n + 1) * y := by ring
    rw [e1, e2, hy, sub_self, zero_mul]
  have h1 : z * (1 - z * y) = 0 := IsNilpotent.eq_zero ⟨n + 1, h0⟩
  exact ⟨y, by linear_combination h1⟩

end Alg

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem psi_one (hD : LocalDatum K R ψ) {r : K} (hr : r ∈ R) : ψ r = 1 := by
  have := (hD.selfDual 1).2 R.one_mem r hr
  rwa [one_mul] at this

theorem isLat_mulR (hD : LocalDatum K R ψ) {a b : K} (hab : a * b = 1) : IsLat (mulR R a) := by
  constructor
  · have : ((mulR R a : AddSubgroup K) : Set K) = (fun x => b * x) ⁻¹' (R : Set K) := by
      ext x
      exact mem_mulR_iff hab x
    rw [this]
    exact hD.isOpen.preimage (by fun_prop)
  · have : ((mulR R a : AddSubgroup K) : Set K) = (fun x => a * x) '' (R : Set K) := by
      unfold mulR
      rw [AddSubgroup.coe_map]
      rfl
    rw [this]
    exact hD.isCompact.image (by fun_prop)

theorem inter_zero (hD : LocalDatum K R ψ) (hQ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {p q : K}
    (hpq : p * q = 1) (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {z : K}
    (hz : ∀ m : ℕ, q ^ m * z ∈ R) : z = 0 := by
  have := hD.t2
  have := hD.artin
  have := hD.red
  by_contra hz0
  set J : Set K := {x | ∀ m : ℕ, q ^ m * x ∈ R} with hJ
  have hJmul : ∀ c x, x ∈ J → c * x ∈ J := by
    intro c x hx m
    obtain ⟨k, hk⟩ := hex c
    have h2 := R.mul_mem hk (hx (m + k))
    have e : q ^ m * (c * x) = p ^ k * c * (q ^ (m + k) * x) := by
      have h1 : p ^ k * q ^ k = 1 := pow_mul_pow_one hpq k
      rw [pow_add]
      linear_combination (-(q ^ m * c * x)) * h1
    rw [e]
    exact h2
  have hJc : IsCompact J := by
    apply hD.isCompact.of_isClosed_subset
    · have : J = ⋂ m : ℕ, (fun x => q ^ m * x) ⁻¹' (R : Set K) := by
        ext x
        simp [hJ]
      rw [this]
      exact isClosed_iInter fun m => hD.isCompact.isClosed.preimage (by fun_prop)
    · intro x hx
      simpa using hx 0
  have hopen : IsOpen {ab : K × K | ab.1 * ab.2 ≠ z} :=
    (isOpen_compl_singleton (x := z)).preimage (continuous_fst.mul continuous_snd)
  obtain ⟨U, V, hU, hV, h0U, hJV, hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : K))) hJc hopen (by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      have ha' : a = 0 := ha
      subst ha'
      show (0 : K) * b ≠ z
      rw [zero_mul]
      exact Ne.symm hz0)
  have hzJ : z ∈ J := hz
  have hseq : ∀ n : ℕ, (n : K) * z ∈ J := fun n => hJmul _ _ hzJ
  obtain ⟨a, haJ, ha⟩ := hJc.exists_clusterPt (f := map (fun n : ℕ => (n : K) * z) atTop) (by
    rw [le_principal_iff]
    exact mem_map.2 (univ_mem' hseq))
  have hU0 : U ∈ 𝓝 (0 : K) := hU.mem_nhds (h0U rfl)
  have hsub : Tendsto (fun xy : K × K => xy.1 - xy.2) (𝓝 a ×ˢ 𝓝 a) (𝓝 0) := by
    have h : Tendsto (fun xy : K × K => xy.1 - xy.2) (𝓝 (a, a)) (𝓝 (a - a)) :=
      (continuous_fst.sub continuous_snd : Continuous fun xy : K × K => xy.1 - xy.2).tendsto (a, a)
    rwa [nhds_prod_eq, sub_self] at h
  obtain ⟨N, hN, hNN⟩ := Filter.mem_prod_self_iff.1 (hsub hU0)
  have hfreq : ∃ᶠ n : ℕ in atTop, (n : K) * z ∈ N :=
    MapClusterPt.frequently (u := fun n : ℕ => (n : K) * z) ha hN
  obtain ⟨n, _, hn⟩ := hfreq.forall_exists_of_atTop 0
  obtain ⟨m, hm, hmN⟩ := hfreq.forall_exists_of_atTop (n + 1)
  have hk : ((m - n : ℕ) : K) * z ∈ U := by
    have h3 := hNN (Set.mk_mem_prod hmN hn)
    simp only [Set.mem_preimage] at h3
    rw [Nat.cast_sub (by omega), sub_mul]
    exact h3
  obtain ⟨u, hu⟩ := hQ (m - n) (by omega)
  obtain ⟨c, hc⟩ := vnr z
  have hy : (↑u⁻¹ * c) * z ∈ J := hJmul _ _ hzJ
  apply hUV (Set.mk_mem_prod hk (hJV hy))
  show ((m - n : ℕ) : K) * z * (↑u⁻¹ * c * z) = z
  rw [← hu]
  have h4 : (u : K) * ↑u⁻¹ = 1 := u.mul_inv
  linear_combination (z * z * c) * h4 - hc

theorem lat_mono {p q : K} (hpq : p * q = 1) (hp : p ∈ R) {m m' : ℕ} (h : m ≤ m') {x : K}
    (hx : q ^ m' * x ∈ R) : q ^ m * x ∈ R := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : q ^ m * x = p ^ d * (q ^ (m + d) * x) := by
    have h1 := pow_mul_pow_one hpq d
    rw [pow_add]
    linear_combination (-(q ^ m * x)) * h1
  rw [e]
  exact R.mul_mem (R.pow_mem hp d) hx

theorem small (hD : LocalDatum K R ψ) (hQ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {p q : K}
    (hpq : p * q = 1) (hp : p ∈ R) (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {V : Set K}
    (hV : V ∈ 𝓝 (0 : K)) : ∃ m : ℕ, ∀ x, q ^ m * x ∈ R → x ∈ V := by
  have := hD.t2
  by_contra hcon
  push Not at hcon
  let t : ℕ → Set K := fun m => (fun x => q ^ m * x) ⁻¹' (R : Set K) ∩ (interior V)ᶜ
  have hcl : ∀ m, IsClosed (t m) := fun m =>
    (hD.isCompact.isClosed.preimage (by fun_prop)).inter isOpen_interior.isClosed_compl
  have hne : (⋂ m, t m).Nonempty := by
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    · intro m x hx
      exact ⟨lat_mono hpq hp (Nat.le_succ m) hx.1, hx.2⟩
    · intro m
      obtain ⟨x, hx, hxV⟩ := hcon m
      exact ⟨x, hx, fun h => hxV (interior_subset h)⟩
    · apply hD.isCompact.of_isClosed_subset (hcl 0)
      intro x hx
      simpa using hx.1
    · exact hcl
  obtain ⟨x, hx⟩ := hne
  rw [Set.mem_iInter] at hx
  have hx0 : x = 0 := inter_zero hD hQ hpq hex fun m => (hx m).1
  apply (hx 0).2
  rw [hx0]
  exact mem_interior_iff_mem_nhds.2 hV

theorem one_add (hD : LocalDatum K R ψ) (hQ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {p q : K}
    (hpq : p * q = 1) (hp : p ∈ R) (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {x : K} (hx : x ∈ R) :
    ∃ w : K, (1 + p * x) * w = 1 ∧ 1 + p * x ∈ R ∧ w ∈ R := by
  have := hD.artin
  have hnz : ∀ y : K, (1 + p * x) * y = 0 → y = 0 := by
    intro y hy
    have hpow : ∀ n : ℕ, y = p ^ n * (-x) ^ n * y := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have : p ^ (n + 1) * (-x) ^ (n + 1) * y = p ^ n * (-x) ^ n * (-(p * x * y)) := by ring
        rw [this]
        have h2 : -(p * x * y) = y := by linear_combination -hy
        rw [h2]
        exact ih
    obtain ⟨k, hk⟩ := hex y
    apply inter_zero hD hQ hpq hex
    intro m
    have e : q ^ m * y = (-x) ^ (m + k) * (p ^ k * y) := by
      have h1 := pow_mul_pow_one hpq m
      have h2 := hpow (m + k)
      calc q ^ m * y = q ^ m * (p ^ (m + k) * (-x) ^ (m + k) * y) := by rw [← h2]
        _ = (p ^ m * q ^ m) * ((-x) ^ (m + k) * (p ^ k * y)) := by rw [pow_add p]; ring
        _ = _ := by rw [h1, one_mul]
    rw [e]
    exact R.mul_mem (R.pow_mem (R.neg_mem hx) _) hk
  have hu : IsUnit (1 + p * x) := by
    apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    exact hnz y (by rw [mul_comm]; exact hy)
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  refine ⟨w, hw, R.add_mem R.one_mem (R.mul_mem hp hx), ?_⟩
  have hpow : ∀ n : ℕ, ∃ s ∈ R, w = s + p ^ n * (-x) ^ n * w := by
    intro n
    induction n with
    | zero => exact ⟨0, R.zero_mem, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs, h⟩ := ih
      refine ⟨s + p ^ n * (-x) ^ n, R.add_mem hs (R.mul_mem (R.pow_mem hp n)
        (R.pow_mem (R.neg_mem hx) n)), ?_⟩
      have h2 : w = 1 - p * x * w := by linear_combination hw
      calc w = s + p ^ n * (-x) ^ n * w := h
        _ = s + p ^ n * (-x) ^ n * (1 - p * x * w) := by rw [← h2]
        _ = _ := by ring
  obtain ⟨k, hk⟩ := hex w
  obtain ⟨s, hs, h⟩ := hpow k
  rw [h]
  have e : p ^ k * (-x) ^ k * w = (-x) ^ k * (p ^ k * w) := by ring
  rw [e]
  exact R.add_mem hs (R.mul_mem (R.pow_mem (R.neg_mem hx) k) hk)

end Top

section Top2

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem bounded (hD : LocalDatum K R ψ) {p : K} (hp : p ∈ R)
    (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {C : Set K} (hC : IsCompact C) :
    ∃ m : ℕ, ∀ z ∈ C, p ^ m * z ∈ R := by
  obtain ⟨m, hm⟩ := hC.elim_directed_cover (fun m : ℕ => (fun x => p ^ m * x) ⁻¹' (R : Set K))
    (fun m => hD.isOpen.preimage (by fun_prop))
    (fun z _ => by
      obtain ⟨m, hm⟩ := hex z
      exact Set.mem_iUnion.2 ⟨m, hm⟩)
    (by
      apply Monotone.directed_le
      intro m m' h x hx
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have e : p ^ (m + d) * x = p ^ d * (p ^ m * x) := by ring
      show p ^ (m + d) * x ∈ R
      rw [e]
      exact R.mul_mem (R.pow_mem hp d) hx)
  exact ⟨m, fun z hz => hm hz⟩

theorem inv_bounded (hD : LocalDatum K R ψ) (hQ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {p q : K}
    (hpq : p * q = 1) (hp : p ∈ R) (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {Om : Set K}
    (hOm : IsCompact Om) (hu : ∀ z ∈ Om, IsUnit z) :
    ∃ k : ℕ, ∀ z ∈ Om, p ^ k * Ring.inverse z ∈ R := by
  obtain ⟨k, hk⟩ := hOm.elim_directed_cover
    (fun k : ℕ => {z : K | ∃ w, z * w = 1 ∧ p ^ k * w ∈ R})
    (fun k => by
      rw [isOpen_iff_mem_nhds]
      rintro z₀ ⟨w₀, hw₀, hk⟩
      have hN : (fun z => q * w₀ * (z - z₀)) ⁻¹' (R : Set K) ∈ 𝓝 z₀ := by
        apply (hD.isOpen.preimage (by fun_prop)).mem_nhds
        show q * w₀ * (z₀ - z₀) ∈ R
        rw [sub_self, mul_zero]
        exact R.zero_mem
      refine mem_of_superset hN ?_
      intro z hz
      obtain ⟨w', hw', _, hw'R⟩ := one_add hD hQ hpq hp hex hz
      refine ⟨w₀ * w', ?_, ?_⟩
      · have e : z = z₀ * (1 + p * (q * w₀ * (z - z₀))) := by
          linear_combination (-(z - z₀)) * hw₀ - (z₀ * w₀ * (z - z₀)) * hpq
        calc z * (w₀ * w') = z₀ * (1 + p * (q * w₀ * (z - z₀))) * (w₀ * w') := by rw [← e]
          _ = (z₀ * w₀) * ((1 + p * (q * w₀ * (z - z₀))) * w') := by ring
          _ = 1 := by rw [hw₀, hw', one_mul]
      · rw [← mul_assoc]
        exact R.mul_mem hk hw'R)
    (fun z hz => by
      obtain ⟨w, hw⟩ := (hu z hz).exists_right_inv
      obtain ⟨m, hm⟩ := hex w
      exact Set.mem_iUnion.2 ⟨m, w, hw, hm⟩)
    (by
      apply Monotone.directed_le
      rintro m m' h x ⟨w, hw, hx⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have e : p ^ (m + d) * w = p ^ d * (p ^ m * w) := by ring
      refine ⟨w, hw, ?_⟩
      rw [e]
      exact R.mul_mem (R.pow_mem hp d) hx)
  refine ⟨k, fun z hz => ?_⟩
  obtain ⟨w, hw, h⟩ := hk hz
  rw [ringInv_eq hw]
  exact h

theorem mulR_mul_unit {z v w : K} (hvw : v * w = 1) (hv : v ∈ R) (hw : w ∈ R) :
    mulR R (z * v) = mulR R z := by
  ext y
  unfold mulR
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨v * r, R.mul_mem hv hr, by ring⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨w * r, R.mul_mem hw hr, by linear_combination (z * r) * hvw⟩

theorem exists_reps {L M : AddSubgroup K} (hL : IsCompact (L : Set K)) (hM : IsOpen (M : Set K)) :
    ∃ S : Finset K, IsReps S L M := by
  classical
  have : CompactSpace L := isCompact_iff_compactSpace.1 hL
  have ho : IsOpen ((M.addSubgroupOf L : AddSubgroup L) : Set L) :=
    hM.preimage continuous_subtype_val
  have : Finite (L ⧸ M.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ ho
  have : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun y : L ⧸ M.addSubgroupOf L => ((Quotient.out y : L) : K), ?_, ?_⟩
  · intro a ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 ha
    exact (Quotient.out y : L).2
  · intro l hl
    have hrel : ∀ y : L ⧸ M.addSubgroupOf L,
        l - ((Quotient.out y : L) : K) ∈ M ↔ y = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) := by
      intro y
      have h1 : y = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) ↔
          ((Quotient.out y : L) : L ⧸ M.addSubgroupOf L) = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) := by
        rw [QuotientAddGroup.out_eq']
      rw [h1, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have e : ((-(Quotient.out y : L) + ⟨l, hl⟩ : L) : K) = l - ((Quotient.out y : L) : K) := by
        push_cast
        ring
      rw [e]
    refine ⟨((Quotient.out ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) : L) : K),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (hrel _).2 rfl⟩, ?_⟩
    rintro a ⟨ha, hal⟩
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 ha
    rw [(hrel y).1 hal]

theorem dual_exists (hD : LocalDatum K R ψ) {a b : K} (hab : a * b = 1) (ha : a ∈ R)
    (χ : AddChar R ℂ) (hχ : ∀ r : R, (r : K) ∈ mulR R a → χ r = 1) :
    ∃ z : K, ∀ r : R, χ r = ψ (z * (r : K)) := by
  classical
  obtain ⟨S, hS⟩ := exists_reps (L := R.toAddSubgroup) (M := mulR R a) hD.isCompact
    (isLat_mulR hD hab).1
  have hle : mulR R a ≤ R.toAddSubgroup := by
    intro x hx
    have h := (mem_mulR_iff hab x).1 hx
    have e : x = a * (b * x) := by linear_combination (-x) * hab
    rw [e]
    exact R.mul_mem ha h
  by_contra hcon
  push Not at hcon
  let X : K → ℂ := fun x => if h : x ∈ R then χ ⟨x, h⟩ else 0
  have hX : ∀ (x : K) (h : x ∈ R), X x = χ ⟨x, h⟩ := fun x h => dif_pos h
  have hSR : ∀ s ∈ S, s ∈ R := fun s hs => hS.1 s hs

  have h1 : ∀ s ∈ S, ∑ r ∈ S, X r * ψ (b * s * r) = 0 := by
    intro s hs
    obtain ⟨r, hr⟩ := hcon (-(b * s))
    refine sum_reps_eq_zero hle hS (fun x => X x * ψ (b * s * x)) ?_ ?_ (l₀ := (r : K)) r.2 ?_
    · intro x hx y hy
      have hxy : x + y ∈ R := R.add_mem hx hy
      show X (x + y) * ψ (b * s * (x + y)) = X x * ψ (b * s * x) * (X y * ψ (b * s * y))
      rw [hX _ hxy, hX _ hx, hX _ hy, mul_add, AddChar.map_add_eq_mul]
      have : (⟨x + y, hxy⟩ : R) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, AddChar.map_add_eq_mul]
      ring
    · intro l hl
      have hlR : l ∈ R := hle hl
      show X l * ψ (b * s * l) = 1
      rw [hX _ hlR, hχ ⟨l, hlR⟩ hl, one_mul]
      apply psi_one hD
      have e : b * s * l = s * (b * l) := by ring
      rw [e]
      exact R.mul_mem (hSR s hs) ((mem_mulR_iff hab l).1 hl)
    · show X (r : K) * ψ (b * s * (r : K)) ≠ 1
      intro h
      apply hr
      rw [hX _ r.2] at h
      have h2 : ψ (b * s * (r : K)) * ψ (-(b * s) * (r : K)) = 1 := by
        rw [← AddChar.map_add_eq_mul]
        have : b * s * (r : K) + -(b * s) * (r : K) = 0 := by ring
        rw [this, AddChar.map_zero_eq_one]
      calc χ r = χ r * (ψ (b * s * (r : K)) * ψ (-(b * s) * (r : K))) := by rw [h2, mul_one]
        _ = (χ ⟨(r : K), r.2⟩ * ψ (b * s * (r : K))) * ψ (-(b * s) * (r : K)) := by ring
        _ = ψ (-(b * s) * (r : K)) := by rw [h, one_mul]

  obtain ⟨r₀, ⟨hr₀S, hr₀⟩, huniq⟩ := hS.2 0 R.toAddSubgroup.zero_mem
  have hr₀a : r₀ ∈ mulR R a := by
    have := (mulR R a).neg_mem hr₀
    simpa using this
  have h2 : ∀ r ∈ S, r ≠ r₀ → ∑ s ∈ S, ψ (b * s * r) = 0 := by
    intro r hr hne
    have hnot : ¬ b * r ∈ R := by
      intro h
      apply hne
      apply huniq
      refine ⟨hr, ?_⟩
      rw [zero_sub]
      exact (mulR R a).neg_mem ((mem_mulR_iff hab r).2 h)
    have hex : ∃ t ∈ R, ψ (b * r * t) ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hnot ((hD.selfDual _).1 hc)
    obtain ⟨t, ht, hne'⟩ := hex
    refine sum_reps_eq_zero hle hS (fun x => ψ (b * x * r)) ?_ ?_ (l₀ := t) ht ?_
    · intro x _ y _
      show ψ (b * (x + y) * r) = ψ (b * x * r) * ψ (b * y * r)
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    · intro l hl
      apply psi_one hD
      have e : b * l * r = (b * l) * r := by ring
      rw [e]
      exact R.mul_mem ((mem_mulR_iff hab l).1 hl) (hSR r hr)
    · show ψ (b * t * r) ≠ 1
      have e : b * t * r = b * r * t := by ring
      rw [e]
      exact hne'
  have h3 : ∑ s ∈ S, ψ (b * s * r₀) = (S.card : ℂ) := by
    have : ∑ s ∈ S, ψ (b * s * r₀) = ∑ s ∈ S, (1 : ℂ) := by
      refine Finset.sum_congr rfl fun s hs => psi_one hD ?_
      have e : b * s * r₀ = s * (b * r₀) := by ring
      rw [e]
      exact R.mul_mem (hSR s hs) ((mem_mulR_iff hab r₀).1 hr₀a)
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h4 : ∑ s ∈ S, ∑ r ∈ S, X r * ψ (b * s * r) = (S.card : ℂ) := by
    rw [Finset.sum_comm]
    have : ∀ r ∈ S, ∑ s ∈ S, X r * ψ (b * s * r) = X r * ∑ s ∈ S, ψ (b * s * r) :=
      fun r _ => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl this, Finset.sum_eq_single r₀]
    · rw [h3, hX _ (hSR r₀ hr₀S), hχ _ hr₀a, one_mul]
    · intro r hr hne
      rw [h2 r hr hne, mul_zero]
    · intro h
      exact absurd hr₀S h
  rw [Finset.sum_congr rfl h1, Finset.sum_const_zero] at h4
  have hc : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 (reps_nonempty hS)).ne'
  exact hc h4.symm

end Top2

end A6x4

open A6x4

theorem characterMean : Formalism.FourierDecayAlt.A6.CharMean := by
  intro K _ ψ L₁ L₂ S hle hS a ha
  have hc : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 (reps_nonempty hS)).ne'
  split_ifs with h
  · have : ∑ σ ∈ S, ψ (a * σ) = ∑ σ ∈ S, (1 : ℂ) :=
      Finset.sum_congr rfl fun σ hσ => h σ (hS.1 σ hσ)
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hc]
  · have h' : ∃ l ∈ L₂, ψ (a * l) ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact h hcon
    obtain ⟨l₀, hl₀, hne⟩ := h'
    rw [sum_reps_eq_zero hle hS (fun x => ψ (a * x)) ?_ ha hl₀ hne, mul_zero]
    intro x _ y _
    show ψ (a * (x + y)) = ψ (a * x) * ψ (a * y)
    rw [mul_add, AddChar.map_add_eq_mul]

theorem smallUnits : Formalism.FourierDecayAlt.A6.SmallUnits := by
  intro K _ _ _ R ψ hD hQ V hV
  obtain ⟨ϖ, hp, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := ϖ.mul_inv
  obtain ⟨m, hm⟩ := small hD hQ hpq hp hex hV
  refine ⟨ϖ ^ m, hm _ ?_⟩
  rw [Units.val_pow_eq_pow_val, mul_comm, pow_mul_pow_one hpq]
  exact R.one_mem

theorem compactOpenChoice : Formalism.FourierDecayAlt.A6.LatChoice := by
  intro K _ _ _ R ψ hD hQ
  obtain ⟨ϖ, hp, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := ϖ.mul_inv
  constructor
  · intro C hC
    obtain ⟨m, hm⟩ := bounded hD hp hex hC
    have hab := pow_mul_pow_one hpq m
    refine ⟨mulR R ((ϖ : K) ^ m), isLat_mulR hD hab, ?_, ?_⟩
    · intro x hx
      have h := (mem_mulR_iff hab x).1 hx
      have e : x = (ϖ : K) ^ m * (((ϖ⁻¹ : Kˣ) : K) ^ m * x) := by linear_combination (-x) * hab
      rw [e]
      exact R.mul_mem (R.pow_mem hp m) h
    · intro z hz l hl
      apply psi_one hD
      have h := (mem_mulR_iff hab l).1 hl
      have e : z * l = ((ϖ : K) ^ m * z) * (((ϖ⁻¹ : Kˣ) : K) ^ m * l) := by
        linear_combination (-(z * l)) * hab
      rw [e]
      exact R.mul_mem (hm z hz) h
  · intro V hV
    obtain ⟨m, hm⟩ := small hD hQ hpq hp hex hV
    have hab := pow_mul_pow_one hpq m
    have hba : ((ϖ⁻¹ : Kˣ) : K) ^ m * (ϖ : K) ^ m = 1 := by rw [mul_comm]; exact hab
    refine ⟨mulR R (((ϖ⁻¹ : Kˣ) : K) ^ m), isLat_mulR hD hba, ?_, ?_⟩
    · intro x hx
      exact (mem_mulR_iff hba x).2 (R.mul_mem (R.pow_mem hp m) hx)
    · intro z hz
      apply hm
      apply (hD.selfDual _).1
      intro r hr
      have hl : ((ϖ⁻¹ : Kˣ) : K) ^ m * r ∈ mulR R (((ϖ⁻¹ : Kˣ) : K) ^ m) := by
        apply (mem_mulR_iff hba _).2
        rw [← mul_assoc, hab, one_mul]
        exact hr
      have h := hz _ hl
      have e : ((ϖ⁻¹ : Kˣ) : K) ^ m * z * r = z * (((ϖ⁻¹ : Kˣ) : K) ^ m * r) := by ring
      rw [e]
      exact h

theorem modulusLocallyConstant : Formalism.FourierDecayAlt.A6.ModLocConst := by
  intro K _ _ _ R ψ hD hQ Om hOm hu E hE
  obtain ⟨ϖ, hp, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := ϖ.mul_inv
  generalize (ϖ : K) = p at hp hex hpq
  generalize ((ϖ⁻¹ : Kˣ) : K) = q at hpq
  obtain ⟨k, hk⟩ := inv_bounded hD hQ hpq hp hex hOm hu
  obtain ⟨j, hj⟩ := small hD hQ hpq hp hex hE
  have hab := pow_mul_pow_one hpq (j + 1 + k)
  refine ⟨mulR R (p ^ (j + 1 + k)), isLat_mulR hD hab, ?_⟩
  intro z hz l hl
  have hzw : z * Ring.inverse z = 1 := Ring.mul_inverse_cancel z (hu z hz)
  have hkz := hk z hz
  generalize Ring.inverse z = w at hzw hkz ⊢
  have hr := (mem_mulR_iff hab l).1 hl
  have hr' : q ^ (j + 1 + k) * l * (p ^ k * w) ∈ R := R.mul_mem hr hkz
  generalize hx : q ^ (j + 1 + k) * l * (p ^ k * w) = x at hr'
  have hlw : l * w = p ^ (j + 1) * x := by
    rw [← hx]
    have e : p ^ (j + 1) * (q ^ (j + 1 + k) * l * (p ^ k * w)) =
        (p ^ (j + 1 + k) * q ^ (j + 1 + k)) * (l * w) := by
      rw [pow_add p (j + 1) k]
      ring
    rw [e, hab, one_mul]
  obtain ⟨w', hw', hvR, hw'R⟩ := one_add hD hQ hpq hp hex (R.mul_mem (R.pow_mem hp j) hr')
  have hzl : z + l = z * (1 + p * (p ^ j * x)) := by
    have e : p * (p ^ j * x) = l * w := by rw [hlw]; ring
    rw [e]
    linear_combination (-l) * hzw
  refine ⟨?_, ?_, ?_⟩
  · apply IsUnit.of_mul_eq_one (w * w')
    rw [hzl]
    calc z * (1 + p * (p ^ j * x)) * (w * w') = (z * w) * ((1 + p * (p ^ j * x)) * w') := by ring
      _ = 1 := by rw [hzw, hw', one_mul]
  · unfold modK
    rw [hzl, mulR_mul_unit hw' hvR hw'R]
  · apply hj
    rw [hlw]
    have e : q ^ j * (p ^ (j + 1) * x) = (p ^ j * q ^ j) * (p * x) := by ring
    rw [e, pow_mul_pow_one hpq, one_mul]
    exact R.mul_mem hp hr'

theorem annihilatorCharacters : Formalism.FourierDecayAlt.A6.PerpDual := by
  intro K _ _ _ R ψ hD hQ L₁ hL₁ hle χ hχ
  obtain ⟨ϖ, hp, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := ϖ.mul_inv
  constructor
  · obtain ⟨m, hm⟩ := small hD hQ hpq hp hex (hL₁.1.mem_nhds L₁.zero_mem)
    have hab := pow_mul_pow_one hpq m
    obtain ⟨z, hz⟩ := dual_exists hD hab (R.pow_mem hp m) χ
      (fun r hr => hχ r (hm _ ((mem_mulR_iff hab _).1 hr)))
    refine ⟨z, ?_, hz⟩
    intro l hl
    have h := hz ⟨l, hle hl⟩
    rw [hχ ⟨l, hle hl⟩ hl] at h
    exact h.symm
  · intro z z' hz hz'
    apply (hD.selfDual _).1
    intro r hr
    have h1 := hz ⟨r, hr⟩
    have h2 := hz' ⟨r, hr⟩
    have h3 : ψ ((z - z') * r) * ψ (z' * r) = ψ (z * r) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    have h4 : ψ (z' * r) = ψ (z * r) := by rw [← h1, ← h2]
    rw [h4] at h3
    exact mul_right_cancel₀ (addChar_ne_zero ψ _) (by rw [h3, one_mul])

end Formalism.FourierDecayAlt.P
