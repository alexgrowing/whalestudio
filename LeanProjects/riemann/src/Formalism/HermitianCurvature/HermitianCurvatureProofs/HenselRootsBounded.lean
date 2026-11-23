import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

noncomputable section

open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P.HenselRootsBounded

def Pk {K : Type} [CommRing K] (R : Subring K) (ϖ : Kˣ) (k : ℤ) : AddSubgroup K where
  carrier := {x | ((ϖ ^ (-k) : Kˣ) : K) * x ∈ R}
  zero_mem' := by
    show ((ϖ ^ (-k) : Kˣ) : K) * 0 ∈ R
    rw [mul_zero]; exact R.zero_mem
  add_mem' := by
    intro a b ha hb
    show ((ϖ ^ (-k) : Kˣ) : K) * (a + b) ∈ R
    rw [mul_add]; exact R.add_mem ha hb
  neg_mem' := by
    intro a ha
    show ((ϖ ^ (-k) : Kˣ) : K) * (-a) ∈ R
    rw [mul_neg]; exact R.neg_mem ha

section Alg

variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}

theorem mem_Pk {k : ℤ} {x : K} : x ∈ Pk R ϖ k ↔ ((ϖ ^ (-k) : Kˣ) : K) * x ∈ R := Iff.rfl

theorem Pk_zero {x : K} : x ∈ Pk R ϖ 0 ↔ x ∈ R := by
  rw [mem_Pk]; simp

theorem Pk_mul {k l : ℤ} {x y : K} (hx : x ∈ Pk R ϖ k) (hy : y ∈ Pk R ϖ l) :
    x * y ∈ Pk R ϖ (k + l) := by
  rw [mem_Pk] at *
  have : ((ϖ ^ (-(k + l)) : Kˣ) : K) * (x * y) =
      (((ϖ ^ (-k) : Kˣ) : K) * x) * (((ϖ ^ (-l) : Kˣ) : K) * y) := by
    rw [neg_add, zpow_add, Units.val_mul]; ring
  rw [this]; exact R.mul_mem hx hy

theorem Pk_mono (hϖ : (ϖ : K) ∈ R) {k l : ℤ} (h : l ≤ k) {x : K} (hx : x ∈ Pk R ϖ k) :
    x ∈ Pk R ϖ l := by
  obtain ⟨n, rfl⟩ := Int.le.dest h
  rw [mem_Pk] at *
  have : ((ϖ ^ (-l) : Kˣ) : K) * x = (ϖ : K) ^ n * (((ϖ ^ (-(l + n)) : Kˣ) : K) * x) := by
    rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
    congr 3; ring
  rw [this]; exact R.mul_mem (R.pow_mem hϖ n) hx

theorem Pk_smul {k : ℤ} {x r : K} (hx : x ∈ Pk R ϖ k) (hr : r ∈ R) : x * r ∈ Pk R ϖ k := by
  have := Pk_mul hx (Pk_zero.2 hr); simpa using this

theorem Pk_smul' {k : ℤ} {x r : K} (hr : r ∈ R) (hx : x ∈ Pk R ϖ k) : r * x ∈ Pk R ϖ k := by
  rw [mul_comm]; exact Pk_smul hx hr

theorem Pk_R (hϖ : (ϖ : K) ∈ R) {k : ℤ} (hk : 0 ≤ k) {x : K} (hx : x ∈ Pk R ϖ k) : x ∈ R :=
  Pk_zero.1 (Pk_mono hϖ hk hx)

theorem Pk_pow {k : ℤ} {x : K} (hx : x ∈ Pk R ϖ k) (n : ℕ) : x ^ n ∈ Pk R ϖ (n * k) := by
  induction n with
  | zero => simpa using (Pk_zero (R := R) (ϖ := ϖ)).2 R.one_mem
  | succ n ih =>
    have := Pk_mul ih hx
    rw [pow_succ]; convert this using 2; push_cast; ring

end Alg

structure Ctx (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (R : Subring K) (ϖ : Kˣ) : Prop where
  t2 : T2Space K
  isOpen : IsOpen (R : Set K)
  isCompact : IsCompact (R : Set K)
  mem : (ϖ : K) ∈ R
  ex : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R
  red : IsReduced K
  nat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}

theorem Pk_isOpen (h : Ctx K R ϖ) (k : ℤ) : IsOpen (Pk R ϖ k : Set K) :=
  h.isOpen.preimage (continuous_const.mul continuous_id)

theorem Pk_isCompact (h : Ctx K R ϖ) (k : ℤ) : IsCompact (Pk R ϖ k : Set K) := by
  have : (Pk R ϖ k : Set K) = (fun x => ((ϖ ^ k : Kˣ) : K) * x) '' (R : Set K) := by
    ext x
    constructor
    · intro hx
      refine ⟨((ϖ ^ (-k) : Kˣ) : K) * x, hx, ?_⟩
      show ((ϖ ^ k : Kˣ) : K) * (((ϖ ^ (-k) : Kˣ) : K) * x) = x
      rw [← mul_assoc, ← Units.val_mul, ← zpow_add]; simp
    · rintro ⟨r, hr, rfl⟩
      show ((ϖ ^ (-k) : Kˣ) : K) * (((ϖ ^ k : Kˣ) : K) * r) ∈ R
      rw [← mul_assoc, ← Units.val_mul, ← zpow_add]; simpa using hr
  rw [this]
  exact h.isCompact.image (continuous_const.mul continuous_id)

theorem Pk_isClosed (h : Ctx K R ϖ) (k : ℤ) : IsClosed (Pk R ϖ k : Set K) :=
  have := h.t2
  (Pk_isCompact h k).isClosed

theorem Pk_ex (h : Ctx K R ϖ) (x : K) : ∃ b : ℕ, x ∈ Pk R ϖ (-(b : ℤ)) := by
  obtain ⟨m, hm⟩ := h.ex x
  refine ⟨m, ?_⟩
  rw [mem_Pk, neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]; exact hm

theorem tube (h : Ctx K R ϖ) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ V ∈ 𝓝 (0 : K), ∀ v ∈ V, ∀ r ∈ R, v * r ∈ W := by
  obtain ⟨W', hsub, hopen, h0⟩ := mem_nhds_iff.1 hW
  obtain ⟨u, v, hu, _, h0u, hRv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : K))) h.isCompact
      (n := (fun p : K × K => p.1 * p.2) ⁻¹' W') (hopen.preimage continuous_mul)
      (by
        rintro ⟨a, b⟩ ⟨ha, _⟩
        simp only [Set.mem_singleton_iff] at ha
        simp only [Set.mem_preimage, ha, zero_mul]; exact h0)
  refine ⟨u, hu.mem_nhds (h0u rfl), fun x hx r hr => hsub ?_⟩
  exact huv (Set.mk_mem_prod hx (hRv hr))

theorem inter_zero (h : Ctx K R ϖ) {a : K} (ha : ∀ k : ℕ, a ∈ Pk R ϖ k) : a = 0 := by
  have := h.t2
  have := h.red
  have h1 : ∀ x : K, a * x ∈ R := by
    intro x
    obtain ⟨b, hb⟩ := Pk_ex h x
    have := Pk_mul (ha b) hb
    rw [add_neg_cancel] at this
    exact Pk_zero.1 this
  by_contra hne
  have hsq : a * a ≠ 0 := by
    intro h0
    exact hne (by simpa using (pow_eq_zero_iff (n := 2) (by norm_num)).1 (by rw [sq]; exact h0))
  have hW : ({a * a}ᶜ : Set K) ∈ 𝓝 (0 : K) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hsq.symm)
  obtain ⟨V, hV, hVR⟩ := tube h hW
  obtain ⟨V', hV', hsub⟩ := exists_nhds_half_neg hV
  have hmem : ∀ n : ℕ, (n : K) * a ∈ R := fun n => by rw [mul_comm]; exact h1 _
  obtain ⟨p, _, hp⟩ := h.isCompact.exists_mapClusterPt (f := atTop) (u := fun n : ℕ => (n : K) * a)
    (by
      rw [le_principal_iff, mem_map]
      exact Filter.univ_mem' hmem)
  have hU : {q : K | q - p ∈ V'} ∈ 𝓝 p := by
    have hc : Continuous fun q : K => q - p := continuous_id.sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV')
  have hf := hp.frequently hU
  obtain ⟨n, _, hn⟩ := (frequently_atTop.1 hf) 0
  obtain ⟨n', hn', hn2⟩ := (frequently_atTop.1 hf) (n + 1)
  have hd : ((n' - n : ℕ) : K) * a ∈ V := by
    have := hsub _ hn2 _ hn
    rw [Nat.cast_sub (by omega)]
    convert this using 1; ring
  obtain ⟨w, hw⟩ := h.nat (n' - n) (by omega)
  have := hVR _ hd (a * ((w⁻¹ : Kˣ) : K)) (h1 _)
  apply this
  rw [← hw]
  show (w : K) * a * (a * ((w⁻¹ : Kˣ) : K)) = a * a
  have : (w : K) * ((w⁻¹ : Kˣ) : K) = 1 := by simp
  calc (w : K) * a * (a * ((w⁻¹ : Kˣ) : K)) = a * a * ((w : K) * ((w⁻¹ : Kˣ) : K)) := by ring
    _ = a * a := by rw [this, mul_one]

theorem approx_zero (h : Ctx K R ϖ) {C : Set K} (hC : IsCompact C) {f : K → K} (hf : Continuous f)
    (hap : ∀ k : ℕ, ∃ w ∈ C, f w ∈ Pk R ϖ k) : ∃ w ∈ C, f w = 0 := by
  have := h.t2
  have := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k : ℕ => C ∩ f ⁻¹' (Pk R ϖ k : Set K))
    (by
      intro i x hx
      exact ⟨hx.1, Pk_mono h.mem (by push_cast; omega) hx.2⟩)
    (by intro i; obtain ⟨w, hw, hw'⟩ := hap i; exact ⟨w, hw, hw'⟩)
    (hC.inter_right ((Pk_isClosed h _).preimage hf))
    (fun i => hC.isClosed.inter ((Pk_isClosed h _).preimage hf))
  obtain ⟨w, hw⟩ := this
  rw [Set.mem_iInter] at hw
  exact ⟨w, (hw 0).1, inter_zero h fun k => (hw k).2⟩

theorem basis (h : Ctx K R ϖ) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ k : ℕ, ∀ x ∈ Pk R ϖ k, x ∈ W := by
  have := h.t2
  by_contra hcon
  push Not at hcon
  obtain ⟨W', hsub, hopen, h0⟩ := mem_nhds_iff.1 hW
  have := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k : ℕ => (Pk R ϖ k : Set K) ∩ W'ᶜ)
    (by
      intro i x hx
      exact ⟨Pk_mono h.mem (by push_cast; omega) hx.1, hx.2⟩)
    (by intro i; obtain ⟨w, hw, hw'⟩ := hcon i; exact ⟨w, hw, fun hh => hw' (hsub hh)⟩)
    ((Pk_isCompact h _).inter_right hopen.isClosed_compl)
    (fun i => (Pk_isClosed h _).inter hopen.isClosed_compl)
  obtain ⟨w, hw⟩ := this
  rw [Set.mem_iInter] at hw
  have hw0 : w = 0 := inter_zero h fun k => (hw k).1
  exact (hw 0).2 (hw0 ▸ h0)

theorem bounded (h : Ctx K R ϖ) {C : Set K} (hC : IsCompact C) :
    ∃ b : ℕ, ∀ c ∈ C, c ∈ Pk R ϖ (-(b : ℤ)) := by
  obtain ⟨b, hb⟩ := hC.elim_directed_cover (fun b : ℕ => (Pk R ϖ (-(b : ℤ)) : Set K))
    (fun b => Pk_isOpen h _)
    (by
      intro x _
      obtain ⟨b, hb⟩ := Pk_ex h x
      exact Set.mem_iUnion.2 ⟨b, hb⟩)
    (by
      intro i j
      exact ⟨max i j, fun x hx => Pk_mono h.mem (by push_cast; omega) hx,
        fun x hx => Pk_mono h.mem (by push_cast; omega) hx⟩)
  exact ⟨b, fun c hc => hb hc⟩

end Top

section Top2

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}

theorem inv_one_add (h : Ctx K R ϖ) {u : K} (hu : u ∈ Pk R ϖ 1) : ∃ v ∈ R, (1 + u) * v = 1 := by
  have hnu : -u ∈ Pk R ϖ 1 := (Pk R ϖ 1).neg_mem hu
  obtain ⟨v, hv, hv0⟩ := approx_zero h h.isCompact (f := fun v => (1 + u) * v - 1)
    (by fun_prop)
    (by
      intro k
      refine ⟨∑ i ∈ Finset.range k, (-u) ^ i,
        R.sum_mem fun i _ => R.pow_mem (Pk_R h.mem (by norm_num) hnu) i, ?_⟩
      have h1 := mul_neg_geom_sum (-u) k
      rw [sub_neg_eq_add] at h1
      show (1 + u) * ∑ i ∈ Finset.range k, (-u) ^ i - 1 ∈ Pk R ϖ k
      rw [h1]
      have h2 := (Pk R ϖ _).neg_mem (Pk_pow hnu k)
      rw [mul_one] at h2
      convert h2 using 1; ring)
  exact ⟨v, hv, sub_eq_zero.1 hv0⟩

theorem inv_one_add' (h : Ctx K R ϖ) {k : ℤ} (hk : 1 ≤ k) {u : K} (hu : u ∈ Pk R ϖ k) :
    ∃ u' ∈ Pk R ϖ k, (1 + u) * (1 + u') = 1 := by
  obtain ⟨v, hv, hv1⟩ := inv_one_add h (Pk_mono h.mem hk hu)
  refine ⟨-(u * v), (Pk R ϖ k).neg_mem (Pk_smul hu hv), ?_⟩
  have : v = 1 - u * v := by linear_combination hv1
  calc (1 + u) * (1 + -(u * v)) = (1 + u) * (1 - u * v) := by ring
    _ = (1 + u) * v := by rw [← this]
    _ = 1 := hv1

theorem mulU (h : Ctx K R ϖ) {n : ℤ} (hn : 0 ≤ n) {x y : K} (hx : x - 1 ∈ Pk R ϖ n)
    (hy : y - 1 ∈ Pk R ϖ n) : x * y - 1 ∈ Pk R ϖ n := by
  have hyR : y ∈ R := by
    have := R.add_mem (Pk_R h.mem hn hy) R.one_mem
    simpa using this
  have := (Pk R ϖ n).add_mem (Pk_smul hx hyR) hy
  convert this using 1; ring

theorem powU (h : Ctx K R ϖ) {n : ℤ} (hn : 0 ≤ n) {x : K} (hx : x - 1 ∈ Pk R ϖ n) (i : ℕ) :
    x ^ i - 1 ∈ Pk R ϖ n := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ]; exact mulU h hn ih hx

theorem pow_diff (h : Ctx K R ϖ) {n : ℤ} (hn : 0 ≤ n) (s : ℕ) {w w' : K} (hw : w ∈ Pk R ϖ n)
    (hw' : w' ∈ Pk R ϖ n) :
    ∃ g ∈ Pk R ϖ n, (1 + w') ^ s - (1 + w) ^ s = (w' - w) * ((s : K) + g) := by
  refine ⟨∑ i ∈ Finset.range s, ((1 + w') ^ i * (1 + w) ^ (s - 1 - i) - 1),
    (Pk R ϖ n).sum_mem fun i _ => mulU h hn (powU h hn (by simpa using hw') i)
      (powU h hn (by simpa using hw) _), ?_⟩
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    add_sub_cancel, ← geom_sum₂_mul]
  ring

theorem hensel (h : Ctx K R ϖ) (s : ℕ) {θ : K} (hθ : (s : K) * θ = 1) {a : ℕ}
    (ha : θ ∈ Pk R ϖ (-(a : ℤ))) {n : ℤ} (hn : (a : ℤ) + 1 ≤ n) {y : K} (hy : y ∈ Pk R ϖ n) :
    ∃ v ∈ R, (1 + y * v) ^ s = 1 + (s : K) * y := by
  have hn0 : 0 ≤ n := by omega
  have happ : ∀ k : ℕ, ∃ w ∈ Pk R ϖ n,
      y - w - θ * ((1 + w) ^ s - 1 - (s : K) * w) ∈ Pk R ϖ (n + k) := by
    intro k
    induction k with
    | zero => exact ⟨0, (Pk R ϖ n).zero_mem, by simpa using hy⟩
    | succ k ih =>
      obtain ⟨w, hw, he⟩ := ih
      set e := y - w - θ * ((1 + w) ^ s - 1 - (s : K) * w) with hedef
      have hw' : w + e ∈ Pk R ϖ n := (Pk R ϖ n).add_mem hw (Pk_mono h.mem (by omega) he)
      obtain ⟨g, hg, hgeq⟩ := pow_diff h hn0 s hw hw'
      refine ⟨w + e, hw', ?_⟩
      have hcalc : y - (w + e) - θ * ((1 + (w + e)) ^ s - 1 - (s : K) * (w + e)) =
          -(θ * (e * g)) := by
        have h1 : (1 + (w + e)) ^ s = (1 + w) ^ s + e * ((s : K) + g) := by
          have : w + e - w = e := by ring
          rw [this] at hgeq
          linear_combination hgeq
        rw [h1]
        linear_combination (-1 : K) * hedef
      rw [hcalc]
      refine (Pk R ϖ _).neg_mem ?_
      have := Pk_mul ha (Pk_mul he hg)
      exact Pk_mono h.mem (by push_cast; omega) this
  obtain ⟨w, hw, hw0⟩ := approx_zero h (Pk_isCompact h n)
    (f := fun w => y - w - θ * ((1 + w) ^ s - 1 - (s : K) * w)) (by fun_prop)
    (fun k => by
      obtain ⟨w, hw, he⟩ := happ k
      exact ⟨w, hw, Pk_mono h.mem (by omega) he⟩)
  obtain ⟨g, hg, hgeq⟩ := pow_diff h hn0 s (Pk R ϖ n).zero_mem hw
  simp only [add_zero, one_pow, sub_zero] at hgeq
  have hθg : θ * g ∈ Pk R ϖ 1 := Pk_mono h.mem (by omega) (Pk_mul ha hg)
  obtain ⟨v, hv, hv1⟩ := inv_one_add h hθg
  have hy' : y = w * (1 + θ * g) := by
    have : (1 + w) ^ s - 1 - (s : K) * w = w * g := by linear_combination hgeq
    rw [this] at hw0
    linear_combination hw0
  have hyv : y * v = w := by
    rw [hy', mul_assoc, hv1, mul_one]
  refine ⟨v, hv, ?_⟩
  rw [hyv, hy']
  linear_combination hgeq - w * g * hθ

theorem inv_bounded (h : Ctx K R ϖ) {Om : Set K} (hOm : IsCompact Om) (hu : ∀ z ∈ Om, IsUnit z) :
    ∃ b : ℕ, ∀ z ∈ Om, ∀ zi : K, z * zi = 1 → zi ∈ Pk R ϖ (-(b : ℤ)) := by
  obtain ⟨b, hb⟩ := hOm.elim_directed_cover
    (fun b : ℕ => {z : K | ∃ zi ∈ Pk R ϖ (-(b : ℤ)), z * zi = 1})
    (by
      intro b
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨zi, hzi, hz1⟩
      have hU : {z' : K | z' - z ∈ Pk R ϖ ((b : ℤ) + 1)} ∈ 𝓝 z := by
        have hc : Continuous fun q : K => q - z := continuous_id.sub continuous_const
        exact hc.continuousAt.preimage_mem_nhds
          ((Pk_isOpen h _).mem_nhds (by simp))
      refine Filter.mem_of_superset hU ?_
      intro z' hz'
      have h1 : zi * (z' - z) ∈ Pk R ϖ 1 := by
        have := Pk_mul hzi hz'
        convert this using 2; ring
      obtain ⟨v, hv, hv1⟩ := inv_one_add h h1
      refine ⟨zi * v, Pk_smul hzi hv, ?_⟩
      linear_combination hv1 + v * hz1)
    (by
      intro z hz
      obtain ⟨w, rfl⟩ := hu z hz
      obtain ⟨b, hb⟩ := Pk_ex h ((w⁻¹ : Kˣ) : K)
      exact Set.mem_iUnion.2 ⟨b, _, hb, by simp⟩)
    (by
      intro i j
      exact ⟨max i j,
        fun x ⟨zi, hzi, hx⟩ => ⟨zi, Pk_mono h.mem (by push_cast; omega) hzi, hx⟩,
        fun x ⟨zi, hzi, hx⟩ => ⟨zi, Pk_mono h.mem (by push_cast; omega) hzi, hx⟩⟩)
  refine ⟨b, fun z hz zi hzi => ?_⟩
  obtain ⟨zi', hzi', hz1⟩ := hb hz
  have : zi = zi' := by
    calc zi = zi * (z * zi') := by rw [hz1, mul_one]
      _ = (z * zi) * zi' := by ring
      _ = zi' := by rw [hzi, one_mul]
  rw [this]; exact hzi'

theorem classes_finite (h : Ctx K R ϖ) {C : Set K} (hC : IsCompact C) :
    {x : K ⧸ R.toAddSubgroup | ∃ c ∈ C, ((c : K) : K ⧸ R.toAddSubgroup) = x}.Finite := by
  have hd : DiscreteTopology (K ⧸ R.toAddSubgroup) :=
    QuotientAddGroup.discreteTopology h.isOpen
  exact (hC.image QuotientAddGroup.continuous_mk).finite_of_discrete

end Top2

theorem roots_finite {K : Type} [CommRing K] [IsArtinianRing K] [IsReduced K] (s : ℕ) (hs : 1 ≤ s)
    (D : Kˣ) : {z : Kˣ | z ^ s = D}.Finite := by
  classical
  have h1 : {x : K | x ^ s = (D : K)}.Finite := by
    let e := IsArtinianRing.equivPi K
    have h2 : (Set.pi Set.univ fun I : MaximalSpectrum K =>
        {y : K ⧸ I.asIdeal | y ^ s = e (D : K) I}).Finite := by
      refine Set.Finite.pi fun I => ?_
      refine Set.Finite.subset (Polynomial.nthRoots s (e (D : K) I)).toFinset.finite_toSet ?_
      intro y hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots (by omega)).2 hy
    refine Set.Finite.subset (h2.preimage e.injective.injOn) ?_
    intro x hx
    rw [Set.mem_preimage, Set.mem_pi]
    intro I _
    show (e x I) ^ s = e (D : K) I
    have hx' : x ^ s = (D : K) := hx
    rw [← hx', map_pow]; rfl
  refine Set.Finite.subset (h1.preimage Units.val_injective.injOn) ?_
  intro z hz
  have hz' : z ^ s = D := hz
  show (z : K) ^ s = (D : K)
  rw [← hz']; simp

theorem char_family {K : Type} [CommRing K] (B B' : AddSubgroup K)
    (hfin : Finite (B ⧸ B'.addSubgroupOf B)) :
    ∃ S : Finset K, S.card ≠ 0 ∧ (∀ b ∈ S, b ∈ B) ∧ ∀ χ : AddChar K ℂ, (∀ b ∈ B', χ b = 1) →
      (∃ b ∈ B, χ b ≠ 1) → ∑ b ∈ S, χ b = 0 := by
  classical
  have := Fintype.ofFinite (B ⧸ B'.addSubgroupOf B)
  let o : B ⧸ B'.addSubgroupOf B → K := fun q => ((Quotient.out q : B) : K)
  have hinj : Function.Injective o := by
    intro q q' hq
    have : (Quotient.out q : B) = Quotient.out q' := Subtype.ext hq
    calc q = Quotient.mk'' (Quotient.out q) := (Quotient.out_eq' q).symm
      _ = Quotient.mk'' (Quotient.out q') := by rw [this]
      _ = q' := Quotient.out_eq' q'
  refine ⟨Finset.univ.image o, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_ne_zero.2 ⟨0, Finset.mem_univ _⟩
  · intro b hb
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hb
    exact (Quotient.out q : B).2
  · intro χ h1 ⟨b₀, hb₀, hne⟩
    rw [Finset.sum_image fun x _ y _ hxy => hinj hxy]
    let q₀ : B ⧸ B'.addSubgroupOf B := ((⟨b₀, hb₀⟩ : B) : B ⧸ B'.addSubgroupOf B)
    have hshift : ∀ q, χ (o (q₀ + q)) = χ b₀ * χ (o q) := by
      intro q
      have hq : ((Quotient.out (q₀ + q) : B) : B ⧸ B'.addSubgroupOf B) =
          (((⟨b₀, hb₀⟩ : B) + Quotient.out q : B) : B ⧸ B'.addSubgroupOf B) := by
        rw [QuotientAddGroup.mk_add]
        show Quotient.mk'' (Quotient.out (q₀ + q)) = q₀ + Quotient.mk'' (Quotient.out q)
        rw [Quotient.out_eq', Quotient.out_eq']
      rw [QuotientAddGroup.eq] at hq
      have hq' : -o (q₀ + q) + (b₀ + o q) ∈ B' := by
        have := AddSubgroup.mem_addSubgroupOf.1 hq
        simpa [o] using this
      have h2 := h1 _ hq'
      rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, AddChar.map_add_eq_mul] at h2
      have hne0 : χ (o (q₀ + q)) ≠ 0 := by
        intro h0
        rw [h0] at h2; simp at h2
      field_simp at h2
      exact h2.symm
    have hsum : ∑ q, χ (o q) = χ b₀ * ∑ q, χ (o q) := by
      rw [Finset.mul_sum, ← Fintype.sum_equiv (Equiv.addLeft q₀) (fun q => χ (o (q₀ + q)))
        (fun q => χ (o q)) (fun q => rfl)]
      exact Finset.sum_congr rfl fun q _ => hshift q
    have : (1 - χ b₀) * ∑ q, χ (o q) = 0 := by linear_combination hsum
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm hne
    · exact h0

section Core

variable {K : Type} [CommRing K]

open Classical in

def TT (s : ℕ) (Cut : Set K) (τ : Kˣ) (F : Kˣ → ℂ) (c : Kˣ) : ℂ :=
  if (c : K) ∈ Cut then ∑ᶠ z : Kˣ, if z ^ s = τ * c then F z else 0 else 0

def mulQ (R : Subring K) (lam : Kˣ) (h1 : (lam : K) ∈ R) (h2 : ((lam⁻¹ : Kˣ) : K) ∈ R) :
    (K ⧸ R.toAddSubgroup) ≃ (K ⧸ R.toAddSubgroup) where
  toFun := QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft (lam : K))
    (by intro r hr; exact R.mul_mem h1 hr)
  invFun := QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft ((lam⁻¹ : Kˣ) : K))
    (by intro r hr; exact R.mul_mem h2 hr)
  left_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      show (((((lam⁻¹ : Kˣ) : K) * ((lam : K) * x) : K)) : K ⧸ R.toAddSubgroup) = x
      rw [← mul_assoc, ← Units.val_mul]; simp
  right_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      show ((((lam : K) * (((lam⁻¹ : Kˣ) : K) * x) : K)) : K ⧸ R.toAddSubgroup) = x
      rw [← mul_assoc, ← Units.val_mul]; simp

theorem mulQ_mk (R : Subring K) (lam : Kˣ) (h1 : (lam : K) ∈ R) (h2 : ((lam⁻¹ : Kˣ) : K) ∈ R)
    (x : K) : mulQ R lam h1 h2 (x : K ⧸ R.toAddSubgroup) =
      (((lam : K) * x : K) : K ⧸ R.toAddSubgroup) := rfl

theorem TT_congr {R : Subring K} {s : ℕ} {Cut : Set K} {τ : Kˣ} {F : Kˣ → ℂ}
    (hω : ∀ c c' : Kˣ, (c' : K) - c ∈ R → (c : K) ∈ Cut → (c' : K) ∈ Cut ∧
      ∃ ω : Kˣ, c' = c * ω ^ s ∧ ∀ z : Kˣ, z ^ s = τ * c → F (z * ω) = F z)
    (c c' : Kˣ) (hcc : (c' : K) - c ∈ R) : TT s Cut τ F c' = TT s Cut τ F c := by
  classical
  unfold TT
  by_cases hc : (c : K) ∈ Cut
  · obtain ⟨hc', ω, hcω, hF⟩ := hω c c' hcc hc
    rw [if_pos hc, if_pos hc', ← finsum_comp_equiv (Equiv.mulRight ω)]
    refine finsum_congr fun z => ?_
    have hiff : (z * ω) ^ s = τ * c' ↔ z ^ s = τ * c := by
      rw [hcω, mul_pow, ← mul_assoc]
      exact mul_left_inj _
    show (if (z * ω) ^ s = τ * c' then F (z * ω) else 0) = _
    by_cases hz : z ^ s = τ * c
    · rw [if_pos hz, if_pos (hiff.2 hz), hF z hz]
    · rw [if_neg hz, if_neg (fun hh => hz (hiff.1 hh))]
  · have hc' : (c' : K) ∉ Cut := by
      intro hc'
      have : (c : K) - c' ∈ R := by
        have := R.neg_mem hcc
        simpa using this
      exact hc (hω c' c this hc').1
    rw [if_neg hc, if_neg hc']

theorem TT_scale {s : ℕ} {Cut : Set K} {τ : Kˣ} {F G : Kˣ → ℂ} (υ : Kˣ)
    (hcut : ∀ c : Kˣ, (c : K) ∈ Cut ↔ ((υ ^ s * c : Kˣ) : K) ∈ Cut)
    (hG : ∀ c z : Kˣ, (c : K) ∈ Cut → z ^ s = τ * c → F (z * υ) = G z) (c : Kˣ) :
    TT s Cut τ F (υ ^ s * c) = TT s Cut τ G c := by
  classical
  unfold TT
  by_cases hc : (c : K) ∈ Cut
  · rw [if_pos hc, if_pos ((hcut c).1 hc), ← finsum_comp_equiv (Equiv.mulRight υ)]
    refine finsum_congr fun z => ?_
    have hiff : (z * υ) ^ s = τ * (υ ^ s * c) ↔ z ^ s = τ * c := by
      rw [mul_pow, mul_left_comm τ, mul_comm (z ^ s)]
      exact mul_right_inj _
    show (if (z * υ) ^ s = τ * (υ ^ s * c) then F (z * υ) else 0) = _
    by_cases hz : z ^ s = τ * c
    · rw [if_pos hz, if_pos (hiff.2 hz), hG c z hc hz]
    · rw [if_neg hz, if_neg (fun hh => hz (hiff.1 hh))]
  · rw [if_neg hc, if_neg (fun hh => hc ((hcut c).2 hh))]

theorem core {R : Subring K} {s : ℕ} {Cut : Set K} {τ : Kˣ} {F : Kˣ → ℂ}
    {cr : K ⧸ R.toAddSubgroup → Kˣ} (hcr : IsCr R cr)
    (hA : ∀ c c' : Kˣ, (c' : K) - c ∈ R → TT s Cut τ F c' = TT s Cut τ F c)
    (EE : Finset K) (hcard : EE.card ≠ 0) (G : K → Kˣ → ℂ)
    (hB : ∀ ε ∈ EE, ∃ lam : Kˣ, (lam : K) ∈ R ∧ ((lam⁻¹ : Kˣ) : K) ∈ R ∧
      ∀ c, TT s Cut τ F (lam * c) = TT s Cut τ (G ε) c)
    (hC : ∀ c : Kˣ, (c : K) ∈ Cut → ∀ z : Kˣ, z ^ s = τ * c → ∑ ε ∈ EE, G ε z = 0)
    (hfin1 : {x | (cr x : K) ∈ Cut}.Finite) (hfin2 : ∀ D : Kˣ, {z : Kˣ | z ^ s = D}.Finite) :
    ∑ᶠ x, TT s Cut τ F (cr x) = 0 := by
  classical
  have key : ∀ ε ∈ EE, ∑ᶠ x, TT s Cut τ F (cr x) = ∑ᶠ x, TT s Cut τ (G ε) (cr x) := by
    intro ε hε
    obtain ⟨lam, h1, h2, h3⟩ := hB ε hε
    rw [← finsum_comp_equiv (mulQ R lam h1 h2)]
    refine finsum_congr fun x => ?_
    rw [← h3]
    apply hA
    have e1 : ((cr (mulQ R lam h1 h2 x) : K) : K ⧸ R.toAddSubgroup) =
        ((((lam * cr x : Kˣ) : K)) : K ⧸ R.toAddSubgroup) := by
      rw [hcr, Units.val_mul, ← mulQ_mk R lam h1 h2, hcr]
    have e2 := (QuotientAddGroup.eq.1 e1.symm)
    have e3 : -((lam * cr x : Kˣ) : K) + (cr (mulQ R lam h1 h2 x) : K) ∈ R := e2
    convert e3 using 1; ring
  have hsum : (EE.card : ℂ) * ∑ᶠ x, TT s Cut τ F (cr x) = 0 := by
    have h1 : (EE.card : ℂ) * ∑ᶠ x, TT s Cut τ F (cr x) =
        ∑ ε ∈ EE, ∑ᶠ x, TT s Cut τ (G ε) (cr x) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl key
    rw [h1, ← finsum_sum_comm]
    · rw [← finsum_zero (α := K ⧸ R.toAddSubgroup)]
      refine finsum_congr fun x => ?_
      unfold TT
      by_cases hc : (cr x : K) ∈ Cut
      · simp only [if_pos hc]
        rw [← finsum_sum_comm]
        · rw [← finsum_zero (α := Kˣ)]
          refine finsum_congr fun z => ?_
          by_cases hz : z ^ s = τ * cr x
          · simp only [if_pos hz]; exact hC _ hc z hz
          · simp only [if_neg hz]; simp
        · intro ε _
          refine (hfin2 (τ * cr x)).subset ?_
          intro z hz
          by_contra hne
          exact hz (if_neg hne)
      · simp only [if_neg hc]; simp
    · intro ε _
      refine hfin1.subset ?_
      intro x hx
      by_contra hne
      exact hx (if_neg hne)
  rcases mul_eq_zero.1 hsum with h0 | h0
  · exact absurd (by exact_mod_cast h0) hcard
  · exact h0

end Core

section Main

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}

theorem pow_mem_of_pos (h : Ctx K R ϖ) {k : ℤ} (hk : 0 ≤ k) {x : K} (hx : x ∈ Pk R ϖ k) {m : ℕ}
    (hm : 1 ≤ m) : x ^ m ∈ Pk R ϖ k := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ]
  exact Pk_smul' (R.pow_mem (Pk_R h.mem hk hx) j) hx

theorem shift_facts (h : Ctx K R ϖ) {d : ℕ} {n : ℤ} (hn : 1 ≤ n) {t t₁ : Kˣ} {σ : K}
    (hσ : σ ∈ Pk R ϖ (-(d : ℤ))) (ht : (t : K) ∈ Pk R ϖ (n + d)) (hs : IsShift t t₁ σ) :
    ∃ μ ∈ Pk R ϖ n, (t₁ : K) = t * (1 + μ) ∧ (1 + σ * t) * (1 + μ) = 1 ∧ σ * t ∈ Pk R ϖ n := by
  have hσt : σ * t ∈ Pk R ϖ n := by
    have := Pk_mul hσ ht
    convert this using 2; ring
  obtain ⟨μ, hμ, hμ1⟩ := inv_one_add' h hn hσt
  refine ⟨μ, hμ, ?_, hμ1, hσt⟩
  have e1 : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t₁
  have e2 : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t
  have hs' : ((t₁⁻¹ : Kˣ) : K) = ((t⁻¹ : Kˣ) : K) + σ := hs
  have e3 : (t₁ : K) * (1 + σ * t) = t := by
    linear_combination (-(t : K) * t₁) * hs' + (t : K) * e1 - (t₁ : K) * e2
  calc (t₁ : K) = t₁ * ((1 + σ * t) * (1 + μ)) := by rw [hμ1, mul_one]
    _ = t * (1 + μ) := by rw [← mul_assoc, e3]

theorem unit_of (h : Ctx K R ϖ) {k : ℤ} (hk : 1 ≤ k) {w : K} (hw : w ∈ Pk R ϖ k) :
    ∃ (ω : Kˣ) (w' : K), (ω : K) = 1 + w ∧ ((ω⁻¹ : Kˣ) : K) = 1 + w' ∧ w' ∈ Pk R ϖ k := by
  obtain ⟨w', hw', h1⟩ := inv_one_add' h hk hw
  exact ⟨⟨1 + w, 1 + w', h1, by rw [mul_comm]; exact h1⟩, w', rfl, rfl, hw'⟩

theorem quot_finite (h : Ctx K R ϖ) (k l : ℤ) :
    Finite (Pk R ϖ k ⧸ (Pk R ϖ l).addSubgroupOf (Pk R ϖ k)) := by
  have : CompactSpace (Pk R ϖ k) := isCompact_iff_compactSpace.mp (Pk_isCompact h k)
  exact AddSubgroup.quotient_finite_of_isOpen _ ((Pk_isOpen h l).preimage continuous_subtype_val)

theorem crossVanish : Formalism.FourierDecayAlt.A6.CrossVanish := by
  intro K _ _ _ R ψ hD hnat m hm Om Λ Sg ζ hOm hΛ hstab hζ hζ1
  obtain ⟨ϖ, hϖ, hex⟩ := hD.unif
  have h : Ctx K R ϖ := ⟨hD.t2, hD.isOpen, hD.isCompact, hϖ, hex, hD.red, hnat⟩
  have hart := hD.artin
  have hred := hD.red
  have hψR : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    have := (hD.selfDual 1).2 R.one_mem r hr
    simpa using this
  obtain ⟨su, hsu⟩ := hnat (m + 1) (by omega)
  obtain ⟨θ, hθdef⟩ : ∃ θ : K, θ = ((su⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hθ : ((m + 1 : ℕ) : K) * θ = 1 := by rw [← hsu, hθdef]; simp
  have hsR : ((m + 1 : ℕ) : K) ∈ R := natCast_mem R _
  obtain ⟨a, ha⟩ := Pk_ex h θ
  obtain ⟨b₁, hb₁⟩ := bounded h hOm.2.1
  obtain ⟨b₂, hb₂⟩ := inv_bounded h hOm.2.1 hOm.2.2.1
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ, b = b₁ + b₂ := ⟨_, rfl⟩
  have hbz : ∀ z ∈ Om, z ∈ Pk R ϖ (-(b : ℤ)) := fun z hz => Pk_mono hϖ (by omega) (hb₁ z hz)
  have hbi : ∀ z ∈ Om, ∀ zi : K, z * zi = 1 → zi ∈ Pk R ϖ (-(b : ℤ)) :=
    fun z hz zi hzi => Pk_mono hϖ (by omega) (hb₂ z hz zi hzi)
  obtain ⟨l, hl⟩ := basis h (hΛ.1.mem_nhds Λ.zero_mem)
  obtain ⟨d, hd⟩ := bounded h Sg.finite_toSet.isCompact
  obtain ⟨e₁, he₁⟩ := Pk_ex h (ζ : K)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, (1 - (ζ : K)) ∉ Pk R ϖ N₀ := by
    by_contra hcon
    push Not at hcon
    have h0 := inter_zero h hcon
    apply hζ1
    ext
    rw [Units.val_one]
    linear_combination -h0
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = m * b := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = N₀ + a + b := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = N + e₁ + q + b := ⟨_, rfl⟩
  obtain ⟨big, hbig⟩ : ∃ big : ℕ, big = a + 1 + l + b := ⟨_, rfl⟩
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : ℕ, v₁ = M + a + big + N + q + b + e₁ := ⟨_, rfl⟩
  have hpm : ∀ zi ∈ Pk R ϖ (-(b : ℤ)), zi ^ m ∈ Pk R ϖ (-(q : ℤ)) := fun zi hzi => by
    have := Pk_pow hzi m
    convert this using 2; rw [hq]; push_cast; ring
  have hps : ∀ zi ∈ Pk R ϖ (-(b : ℤ)), zi ^ (m + 1) ∈ Pk R ϖ (-((q : ℤ) + b)) := fun zi hzi => by
    have := Pk_pow hzi (m + 1)
    convert this using 2; rw [hq]; push_cast; ring
  have omΛ : ∀ z ∈ Om, ∀ w ∈ Pk R ϖ ((l : ℤ) + b), z * w ∈ Λ := fun z hz w hw => hl _ (by
    have := Pk_mul (hbz z hz) hw
    convert this using 2; ring)
  have omO : ∀ z ∈ Om, ∀ w ∈ Pk R ϖ ((l : ℤ) + b), z * (1 + w) ∈ Om := fun z hz w hw => by
    have := hstab z hz _ (omΛ z hz w hw)
    convert this using 1; ring
  obtain ⟨BB, hBcard, hBmem, hBsum⟩ := char_family (Pk R ϖ (-(N : ℤ))) (Pk R ϖ ((e₁ : ℤ) + b))
    (quot_finite h _ _)
  refine ⟨(Pk R ϖ (M : ℤ) : Set K), (Pk_isOpen h _).mem_nhds (Pk R ϖ _).zero_mem,
    (Pk R ϖ ((v₁ : ℤ) + d) : Set K), (Pk_isOpen h _).mem_nhds (Pk R ϖ _).zero_mem, ?_⟩
  intro t t₁ t₂ κ cr g ht σ hσ σ' hσ' hs₁ hs₂ _ hκE hcr hg hsupp
  have cut_mul : ∀ c ∈ cutSet m Om t, ∀ w ∈ Pk R ϖ ((l : ℤ) + b),
      (1 + w) ^ (m + 1) * c ∈ cutSet m Om t := by
    rintro c ⟨z, hz, hzc⟩ w hw
    exact ⟨z * (1 + w), omO z hz w hw, by rw [mul_pow, hzc]; ring⟩
  obtain ⟨μ₁, hμ₁, ht₁, hi₁, hσt₁⟩ := shift_facts h (n := (v₁ : ℤ)) (by omega)
    (hd σ (Finset.mem_coe.2 hσ)) ht hs₁
  obtain ⟨μ₂, hμ₂, ht₂, hi₂, hσt₂⟩ := shift_facts h (n := (v₁ : ℤ)) (by omega)
    (hd σ' (Finset.mem_coe.2 hσ')) ht hs₂
  have ht₁P : (t₁ : K) ∈ Pk R ϖ (v₁ : ℤ) := by
    rw [ht₁]
    exact Pk_smul (Pk_mono hϖ (by omega) ht) (R.add_mem R.one_mem (Pk_R hϖ (by omega) hμ₁))
  have hnt₁P : -(t₁ : K) ∈ Pk R ϖ (v₁ : ℤ) := (Pk R ϖ _).neg_mem ht₁P
  have e₁₁ : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t₁
  have e₂₂ : (t₂ : K) * ((t₂⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t₂
  have hq12 : (t₁ : K) * ((t₂⁻¹ : Kˣ) : K) = (1 + μ₁) * (1 + σ' * t) := by
    linear_combination ((t₂⁻¹ : Kˣ) : K) * ht₁ - (t : K) * (1 + μ₁) * ((t₂⁻¹ : Kˣ) : K) * hi₂ -
      (1 + σ' * t) * (1 + μ₁) * ((t₂⁻¹ : Kˣ) : K) * ht₂ + (1 + σ' * t) * (1 + μ₁) * e₂₂
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : K, ρ = (κ : K) * ((t₁ : K) * ((t₂⁻¹ : Kˣ) : K)) := ⟨_, rfl⟩
  have hρ : ρ - 1 ∈ Pk R ϖ (M : ℤ) := by
    rw [hρdef, hq12]
    refine mulU h (by omega) hκE (mulU h (by omega) ?_ ?_)
    · simpa using Pk_mono hϖ (by omega) hμ₁
    · simpa using Pk_mono hϖ (by omega) hσt₂
  have hρR : ρ ∈ R := by
    have := R.add_mem (Pk_R hϖ (by omega) hρ) R.one_mem
    simpa using this
  obtain ⟨A, hA⟩ : ∃ A : K, A = ((m + 1 : ℕ) : K) * ((t₁⁻¹ : Kˣ) : K) -
      ((m + 1 : ℕ) : K) * (ζ : K) * (κ : K) * ((t₂⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hAt : A * (t₁ : K) = ((m + 1 : ℕ) : K) * (1 - (ζ : K) * ρ) := by
    rw [hA, hρdef]
    linear_combination ((m + 1 : ℕ) : K) * e₁₁
  have h1ζ : (1 - (ζ : K)) ∈ Pk R ϖ (-(e₁ : ℤ)) :=
    (Pk R ϖ _).sub_mem (Pk_mono hϖ (by omega) (Pk_zero.2 R.one_mem)) he₁
  have root_mem : ∀ c : Kˣ, (c : K) ∈ cutSet m Om t → ∀ z : Kˣ, z ^ (m + 1) = (-t₁) ^ m * c →
      (z : K) ∈ Om := by
    have hμ'' : (1 + μ₁) ^ m - 1 ∈ Pk R ϖ (v₁ : ℤ) := powU h (by omega) (by simpa using hμ₁) m
    have hy' : θ * ((1 + μ₁) ^ m - 1) ∈ Pk R ϖ ((v₁ : ℤ) - a) := by
      have := Pk_mul ha hμ''
      convert this using 2; ring
    obtain ⟨v, hv, hveq⟩ := hensel h (m + 1) hθ ha (n := (v₁ : ℤ) - a) (by omega) hy'
    have hw' : θ * ((1 + μ₁) ^ m - 1) * v ∈ Pk R ϖ ((l : ℤ) + b) :=
      Pk_mono hϖ (by omega) (Pk_smul hy' hv)
    have hveq' : (1 + θ * ((1 + μ₁) ^ m - 1) * v) ^ (m + 1) = (1 + μ₁) ^ m := by
      rw [hveq]; linear_combination ((1 + μ₁) ^ m - 1) * hθ
    rintro c ⟨z₀, hz₀, hz₀c⟩ z hz
    have hzK : (z : K) ^ (m + 1) = (-(t₁ : K)) ^ m * c := by
      have := congrArg Units.val hz
      simpa using this
    have hz₁ := omO z₀ hz₀ _ hw'
    have hz₁p : (z₀ * (1 + θ * ((1 + μ₁) ^ m - 1) * v)) ^ (m + 1) = (z : K) ^ (m + 1) := by
      rw [mul_pow, hz₀c, hveq', hzK, ht₁, ← neg_mul, mul_pow]; ring
    obtain ⟨u₁, hu₁⟩ := hOm.2.2.1 _ hz₁
    have := hOm.2.2.2 _ hz₁ ((z : K) * ((u₁⁻¹ : Kˣ) : K))
      (by rw [mul_pow, ← hz₁p, ← hu₁, ← mul_pow]; simp)
    convert this using 1
    rw [← hu₁]; simp
  have hβ : ∀ z : Kˣ, (z : K) ∈ Om → g (z : K) ≠ 0 →
      A * θ * ((-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ m) ∈ R := by
    intro z hz hgz
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hzi : ((z⁻¹ : Kˣ) : K) ∈ Pk R ϖ (-(b : ℤ)) := hbi z hz _ (Units.mul_inv z)
    have hzim := hpm _ hzi
    have e : A * θ * ((-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ m) =
        -((1 - (ζ : K)) * ((-(t₁ : K)) ^ j * ((z⁻¹ : Kˣ) : K) ^ m)) +
          (ζ : K) * ((ρ - 1) * ((-(t₁ : K)) ^ j * ((z⁻¹ : Kˣ) : K) ^ m)) := by
      rw [show (-(t₁ : K)) ^ m = (-(t₁ : K)) ^ j * (-(t₁ : K)) by rw [hj, pow_succ]]
      linear_combination (-θ * ((-(t₁ : K)) ^ j * ((z⁻¹ : Kˣ) : K) ^ m)) * hAt -
        (1 - (ζ : K) * ρ) * ((-(t₁ : K)) ^ j * ((z⁻¹ : Kˣ) : K) ^ m) * hθ
    rw [e]
    refine R.add_mem (R.neg_mem ?_) ?_
    · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · have hm1 : m = 1 := by omega
        have hζ2 : ζ * ζ = 1 := by
          have := hζ
          rw [hm1] at this
          rw [← this]; exact (sq ζ).symm
        have hζi : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ2
        have h3 := hsupp z hz hgz
        rw [mul_inv, hζi, Units.val_mul] at h3
        rw [hj0, hm1, pow_zero, pow_one, one_mul]
        convert h3 using 1; ring
      · have := Pk_mul h1ζ (Pk_mul (pow_mem_of_pos h (by omega) hnt₁P hjpos) hzim)
        exact Pk_R hϖ (by omega) this
    · have := Pk_mul he₁ (Pk_mul hρ (Pk_mul
        (Pk_zero.2 (R.pow_mem (Pk_R hϖ (by omega) hnt₁P) j)) hzim))
      exact Pk_R hϖ (by omega) this
  obtain ⟨F, hF⟩ : ∃ F : Kˣ → ℂ, F = fun z : Kˣ => g (z : K) * ψ (A * (z : K)) := ⟨_, rfl⟩
  have Fshift : ∀ z : Kˣ, (z : K) ∈ Om → ∀ w ∈ Pk R ϖ ((l : ℤ) + b), ∀ ω : Kˣ, (ω : K) = 1 + w →
      F (z * ω) = F z * ψ (A * (z : K) * w) := by
    intro z hz w hw ω hω
    rw [hF]
    show g ((z * ω : Kˣ) : K) * ψ (A * ((z * ω : Kˣ) : K)) = g z * ψ (A * z) * ψ (A * z * w)
    rw [Units.val_mul, hω, mul_add, mul_one, hg z hz _ (omΛ z hz w hw), mul_add,
      AddChar.map_add_eq_mul, mul_assoc A]
    ring
  have hω : ∀ c c' : Kˣ, (c' : K) - c ∈ R → (c : K) ∈ cutSet m Om t → (c' : K) ∈ cutSet m Om t ∧
      ∃ ω : Kˣ, c' = c * ω ^ (m + 1) ∧ ∀ z : Kˣ, z ^ (m + 1) = (-t₁) ^ m * c → F (z * ω) = F z := by
    intro c c' hcc hc
    have hcci : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := Units.mul_inv c
    have hciP : ((c⁻¹ : Kˣ) : K) ∈ Pk R ϖ ((v₁ : ℤ) + -((q : ℤ) + b)) := by
      obtain ⟨z₀, hz₀, hz₀c⟩ := hc
      obtain ⟨u₀, hu₀⟩ := hOm.2.2.1 z₀ hz₀
      have hzz : z₀ * ((u₀⁻¹ : Kˣ) : K) = 1 := by rw [← hu₀]; simp
      have e1 : (z₀ * ((u₀⁻¹ : Kˣ) : K)) ^ (m + 1) = 1 := by rw [hzz, one_pow]
      rw [mul_pow, hz₀c] at e1
      have e2 : ((c⁻¹ : Kˣ) : K) = (-(t : K)) ^ m * ((u₀⁻¹ : Kˣ) : K) ^ (m + 1) := by
        linear_combination -((c⁻¹ : Kˣ) : K) * e1 +
          ((-(t : K)) ^ m * ((u₀⁻¹ : Kˣ) : K) ^ (m + 1)) * hcci
      rw [e2]
      exact Pk_mul (pow_mem_of_pos h (by omega)
        ((Pk R ϖ _).neg_mem (Pk_mono hϖ (by omega) ht)) hm) (hps _ (hbi z₀ hz₀ _ hzz))
    have hy : θ * (((c' : K) - c) * ((c⁻¹ : Kˣ) : K)) ∈ Pk R ϖ ((v₁ : ℤ) - q - b - a) := by
      have := Pk_mul ha (Pk_smul' hcc hciP)
      convert this using 2; ring
    obtain ⟨v, hv, hveq⟩ := hensel h (m + 1) hθ ha (n := (v₁ : ℤ) - q - b - a) (by omega) hy
    obtain ⟨w, hwdef⟩ : ∃ w : K, w = θ * (((c' : K) - c) * ((c⁻¹ : Kˣ) : K)) * v := ⟨_, rfl⟩
    rw [← hwdef] at hveq
    have hwP : w ∈ Pk R ϖ ((v₁ : ℤ) - q - b - a) := by rw [hwdef]; exact Pk_smul hy hv
    have hwl : w ∈ Pk R ϖ ((l : ℤ) + b) := Pk_mono hϖ (by omega) hwP
    obtain ⟨ω, _, hωv, _, _⟩ := unit_of h (k := (v₁ : ℤ) - q - b - a) (by omega) hwP
    have hc'eq : (c' : K) = (1 + w) ^ (m + 1) * c := by
      rw [hveq]
      linear_combination (-((c' : K) - c) * (c : K) * ((c⁻¹ : Kˣ) : K)) * hθ - ((c' : K) - c) * hcci
    refine ⟨by rw [hc'eq]; exact cut_mul _ hc _ hwl, ω, ?_, ?_⟩
    · ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val, hωv, hc'eq]; ring
    · intro z hz
      have hzO := root_mem c hc z hz
      rw [Fshift z hzO w hwl ω hωv]
      by_cases hgz : g (z : K) = 0
      · rw [hF]
        show g (z : K) * ψ (A * z) * _ = g (z : K) * ψ (A * z)
        rw [hgz]; simp
      · have hzK : (z : K) ^ (m + 1) = (-(t₁ : K)) ^ m * c := by
          have := congrArg Units.val hz
          simpa using this
        have hzzi : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := Units.mul_inv z
        have e1 : ((z : K) * ((z⁻¹ : Kˣ) : K)) ^ (m + 1) = 1 := by rw [hzzi, one_pow]
        rw [mul_pow, hzK] at e1
        have hci : ((c⁻¹ : Kˣ) : K) = (-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ (m + 1) := by
          linear_combination -((c⁻¹ : Kˣ) : K) * e1 +
            ((-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ (m + 1)) * hcci
        have e3 : A * (z : K) * w = (A * θ * ((-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ m)) *
            (((c' : K) - c) * v) := by
          rw [hwdef, hci, pow_succ]
          linear_combination (A * θ * (-(t₁ : K)) ^ m * ((z⁻¹ : Kˣ) : K) ^ m *
            ((c' : K) - c) * v) * hzzi
        rw [e3, hψR _ (R.mul_mem (hβ z hzO hgz) (R.mul_mem hcc hv)), mul_one]
  have hB : ∀ β ∈ BB, ∃ lam : Kˣ, (lam : K) ∈ R ∧ ((lam⁻¹ : Kˣ) : K) ∈ R ∧
      ∀ c, TT (m + 1) (cutSet m Om t) ((-t₁) ^ m) F (lam * c) =
        TT (m + 1) (cutSet m Om t) ((-t₁) ^ m)
          (fun z => F z * ψ (A * (z : K) * ((t₁ : K) * β))) c := by
    intro β hβB
    have hε : (t₁ : K) * β ∈ Pk R ϖ ((v₁ : ℤ) + -(N : ℤ)) := Pk_mul ht₁P (hBmem β hβB)
    obtain ⟨υ, ε', hυ, hυi, hε'⟩ := unit_of h (by omega) hε
    have hεl : (t₁ : K) * β ∈ Pk R ϖ ((l : ℤ) + b) := Pk_mono hϖ (by omega) hε
    have hε'l : ε' ∈ Pk R ϖ ((l : ℤ) + b) := Pk_mono hϖ (by omega) hε'
    refine ⟨υ ^ (m + 1), ?_, ?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, hυ]
      exact R.pow_mem (R.add_mem R.one_mem (Pk_R hϖ (by omega) hε)) _
    · rw [← inv_pow, Units.val_pow_eq_pow_val, hυi]
      exact R.pow_mem (R.add_mem R.one_mem (Pk_R hϖ (by omega) hε')) _
    · refine TT_scale υ ?_ ?_
      · intro c
        rw [Units.val_mul, Units.val_pow_eq_pow_val, hυ]
        constructor
        · intro hc; exact cut_mul _ hc _ hεl
        · intro hc
          have := cut_mul _ hc _ hε'l
          have h1 : (1 + (t₁ : K) * β) * (1 + ε') = 1 := by
            rw [← hυ, ← hυi]; exact Units.mul_inv υ
          have h2 : (1 + ε') ^ (m + 1) * ((1 + (t₁ : K) * β) ^ (m + 1) * (c : K)) = c := by
            rw [← mul_assoc, ← mul_pow, mul_comm (1 + ε'), h1, one_pow, one_mul]
          rwa [h2] at this
      · intro c z hc hz
        exact Fshift z (root_mem c hc z hz) _ hεl υ hυ
  have hC : ∀ c : Kˣ, (c : K) ∈ cutSet m Om t → ∀ z : Kˣ, z ^ (m + 1) = (-t₁) ^ m * c →
      ∑ β ∈ BB, F z * ψ (A * (z : K) * ((t₁ : K) * β)) = 0 := by
    intro c hc z hz
    have hzO := root_mem c hc z hz
    have hzP := hbz z hzO
    have hzzi : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := Units.mul_inv z
    have hziP := hbi z hzO _ hzzi
    obtain ⟨a', ha'⟩ : ∃ a' : K, a' = A * (t₁ : K) * z := ⟨_, rfl⟩
    have hsum := hBsum (ψ.compAddMonoidHom (AddMonoidHom.mulLeft a'))
      (by
        intro x hx
        show ψ (a' * x) = 1
        apply hψR
        have h1 : a' ∈ Pk R ϖ (-(e₁ : ℤ) + -(b : ℤ)) := by
          rw [ha', hAt]
          refine Pk_mul (Pk_smul' hsR ((Pk R ϖ _).sub_mem
            (Pk_mono hϖ (by omega) (Pk_zero.2 R.one_mem)) (Pk_smul he₁ hρR))) hzP
        exact Pk_R hϖ (by omega) (Pk_mul h1 hx))
      (by
        by_contra hcon
        push Not at hcon
        have h1 : a' ∈ Pk R ϖ (N : ℤ) := by
          rw [mem_Pk]
          refine (hD.selfDual _).1 fun r hr => ?_
          have h2 := hcon (((ϖ ^ (-(N : ℤ)) : Kˣ) : K) * r) (by
            rw [mem_Pk, ← mul_assoc, ← Units.val_mul, ← zpow_add]
            simpa using hr)
          have h3 : ψ (a' * (((ϖ ^ (-(N : ℤ)) : Kˣ) : K) * r)) = 1 := h2
          rw [← h3]; congr 1; ring
        have h4 : ((m + 1 : ℕ) : K) * ((ζ : K) * ((ρ - 1) * (z : K))) ∈ Pk R ϖ (N : ℤ) :=
          Pk_smul' hsR (Pk_mono hϖ (by omega) (Pk_mul he₁ (Pk_mul hρ hzP)))
        have h5 := Pk_mul ha (Pk_mul hziP ((Pk R ϖ _).add_mem h1 h4))
        apply hN₀
        have h6 : (1 - (ζ : K)) = θ * (((z⁻¹ : Kˣ) : K) *
            (a' + ((m + 1 : ℕ) : K) * ((ζ : K) * ((ρ - 1) * (z : K))))) := by
          rw [ha', hAt]
          linear_combination (-(1 - (ζ : K)) * ((m + 1 : ℕ) : K) * θ) * hzzi - (1 - (ζ : K)) * hθ
        rw [h6]
        exact Pk_mono hϖ (by omega) h5)
    rw [← Finset.mul_sum]
    have : ∑ β ∈ BB, ψ (A * (z : K) * ((t₁ : K) * β)) = 0 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun β _ => ?_
      show _ = ψ (a' * β)
      rw [ha']; congr 1; ring
    rw [this, mul_zero]
  have hfin1 : {x | (cr x : K) ∈ cutSet m Om t}.Finite := by
    have hcomp : IsCompact ((fun z : K => (-((t⁻¹ : Kˣ) : K)) ^ m * z ^ (m + 1)) '' Om) :=
      hOm.2.1.image (by fun_prop)
    refine (classes_finite h hcomp).subset ?_
    rintro x ⟨z, hz, hzc⟩
    refine ⟨cr x, ⟨z, hz, ?_⟩, hcr x⟩
    show (-((t⁻¹ : Kˣ) : K)) ^ m * z ^ (m + 1) = cr x
    rw [hzc, ← mul_assoc, ← mul_pow, neg_mul_neg, Units.inv_mul, one_pow, one_mul]
  have hmain := core hcr (TT_congr (R := R) hω) BB hBcard
    (fun β z => F z * ψ (A * (z : K) * ((t₁ : K) * β))) hB hC hfin1
    (fun D => roots_finite (m + 1) (by omega) D)
  refine Eq.trans (finsum_congr fun x => ?_) hmain
  unfold TT
  by_cases hc : (cr x : K) ∈ cutSet m Om t
  · rw [if_pos hc, if_pos hc]
    refine finsum_congr fun z => ?_
    by_cases hz : z ^ (m + 1) = (-t₁) ^ m * cr x
    · rw [if_pos hz, if_pos hz, hF, hA]
      show _ = g (z : K) * ψ _
      congr 2; ring
    · rw [if_neg hz, if_neg hz]
  · rw [if_neg hc, if_neg hc]

end Main

end Formalism.FourierDecayAlt.P.HenselRootsBounded

theorem Formalism.FourierDecayAlt.P.crossTermsVanish : Formalism.FourierDecayAlt.A6.CrossVanish :=
  Formalism.FourierDecayAlt.P.HenselRootsBounded.crossVanish
