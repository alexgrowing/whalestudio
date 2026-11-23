import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierExtractionTsumClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TendstoTsumZeroOfEventuallyNotMemRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueAddEquivOfCompatibleCongr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology

namespace GlobalTheory.MatchTerm

theorem exists_char_pow {K X : Type} [Field K] [IsAlgClosed K] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {k : ℕ} (hk : k ≠ 0) (t : Multiplicative X →* Kˣ) :
    ∃ s : Multiplicative X →* Kˣ, s ^ k = t := by
  have h : ∀ u : Kˣ, ∃ v : Kˣ, v ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (Nat.pos_of_ne_zero hk)
    have : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z this, Units.ext (by simpa using hz)⟩
  choose v hv using h
  let b := Module.finBasis ℤ X
  refine ⟨TorsionFourier.charOfValues b fun i => v (t (Multiplicative.ofAdd (b i))), MonoidHom.ext fun x => ?_⟩
  change (∏ i, v (t (Multiplicative.ofAdd (b i))) ^ (b.repr x.toAdd i)) ^ k = t (Multiplicative.ofAdd x.toAdd)
  rw [TorsionFourier.char_apply_eq_prod b t, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv]

section
variable {K X X' : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X']

theorem class_sum_eq [IsAlgClosed K] {M : ℕ} (hM : ‖(M : K)‖ = 1) (σ : X → K) (σ' : X' → K)
    (hσ : Tendsto σ cofinite (𝓝 0)) (hσ' : Tendsto σ' cofinite (𝓝 0)) (c : K) (α : X) (α' : X')
    (E : {t : Multiplicative X →* Kˣ // t ^ M = 1} → {t : Multiplicative X' →* Kˣ // t ^ M = 1})
    (hE : Function.Bijective E)
    (hα : ∀ t, (E t).1 (Multiplicative.ofAdd α') = t.1 (Multiplicative.ofAdd α))
    (hs : ∀ t, ∑' β, σ' β * ((E t).1 (Multiplicative.ofAdd β) : K) =
      c * ∑' β, σ β * (t.1 (Multiplicative.ofAdd β) : K)) :
    ∑' μ, σ' (α' + M • μ) = c * ∑' μ, σ (α + M • μ) := by
  have h0 : (M : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hM
    exact zero_ne_one hM
  have hp : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at h0)
  haveI : NeZero (M : K) := ⟨h0⟩
  haveI : NeZero M := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
  obtain ⟨hf, h1, -⟩ := fourier_extraction_tsum_class K X M ζ hp hM hζ σ hσ α
  obtain ⟨-, h2, -⟩ := fourier_extraction_tsum_class K X' M ζ hp hM hζ σ' hσ' α'
  have hc : M ^ finrank ℤ X = M ^ finrank ℤ X' := by
    rw [← TorsionFourier.natCard_torsionChars (K := K) hp hζ, ← TorsionFourier.natCard_torsionChars (K := K) hp hζ]
    exact Nat.card_eq_of_bijective E hE
  have hc' : (M : K) ^ finrank ℤ X = (M : K) ^ finrank ℤ X' := by exact_mod_cast congrArg (Nat.cast : ℕ → K) hc
  rw [← finsum_comp E hE] at h2
  simp only [hα, hs] at h2
  haveI := Fintype.ofFinite {t : Multiplicative X →* Kˣ // t ^ M = 1}
  rw [finsum_eq_sum_of_fintype] at h1 h2
  apply mul_left_cancel₀ (pow_ne_zero (finrank ℤ X') h0)
  rw [← h2, ← hc', mul_left_comm, ← h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => mul_left_comm _ _ _

theorem limit_class {n : ℕ} (hn : 2 ≤ n) (σ : X → K) (σ' : X' → K)
    (hσ : Tendsto σ cofinite (𝓝 0)) (hσ' : Tendsto σ' cofinite (𝓝 0)) (c : K) (x : X) (α' : ℕ → X')
    (hα : ∀ j, ∃ μ, α' (j + 1) = α' j + n ^ j • μ)
    (hs : ∀ j, ∑' μ, σ' (α' j + n ^ j • μ) = c * ∑' μ, σ (x + n ^ j • μ)) :
    (∀ x', (∀ j, ∃ μ, x' = α' j + n ^ j • μ) → σ' x' = c * σ x) ∧
      (c * σ x ≠ 0 → ∃ x', ∀ j, ∃ μ, x' = α' j + n ^ j • μ) := by
  have h1 := ((tendsto_tsum_pow_classes K X n hn σ hσ (fun _ => x) fun j => ⟨0, by simp⟩).1 x
    fun j => ⟨0, by simp⟩).const_mul c
  have h2 := tendsto_tsum_pow_classes K X' n hn σ' hσ' α' hα
  simp only [hs] at h2
  refine ⟨fun x' hx => tendsto_nhds_unique (h2.1 x' hx) h1, fun hc => ?_⟩
  by_contra h
  exact hc (tendsto_nhds_unique h1 (h2.2 h))
end

section
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)

theorem r_left {k : ℕ} {p q : N.QT k} {p' : N'.QT k} (h : μ.r k p p') (e : N.QEq p q) : μ.r k q p' :=
  (μ.eqv k p q p' p' h e).2 ((N'.qEq_equivalence k).refl _)

theorem r_right {k : ℕ} {p : N.QT k} {p' q' : N'.QT k} (h : μ.r k p p') (e : N'.QEq p' q') : μ.r k p q' :=
  (μ.eqv k p p p' q' h ((N.qEq_equivalence k).refl _)).2 e

theorem qeq_right {k : ℕ} {p : N.QT k} {p' q' : N'.QT k} (h : μ.r k p p') (e : μ.r k p q') : N'.QEq p' q' :=
  (μ.eqv k p p p' q' h ((N.qEq_equivalence k).refl _)).1 e

theorem eq_of_qeq {N : NumD C} {k : ℕ} (hk : k ≠ 0) {p q : N.QT k} (h : N.QEq p q) (e : p.1.1 = q.1.1) : p = q := by
  obtain ⟨z, h1, h2⟩ := h
  rw [e, left_eq_add] at h1
  have hz : z = 0 := by
    have := TorsionFourier.add_nsmul_injective (Nat.pos_of_ne_zero hk) (0 : N.X) (a₁ := z) (a₂ := 0) (by simpa using h1)
    exact this
  rw [hz, N.io_zero, mul_one] at h2
  exact Subtype.ext (Prod.ext e h2.symm)

theorem r_one {k : ℕ} (hk : ∃ j, k = n ^ j) : μ.r k 1 1 := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j 1
  have h := μ.mul _ _ _ _ _ hu hu
  rw [mul_one] at h
  obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 (qeq_right μ hu h)
  refine r_right μ hu ((N'.qEq_equivalence _).symm ((N'.qEq_iff _ _).2 ⟨z, ?_⟩))
  rw [one_mul]
  exact mul_left_cancel hz

theorem r_pow {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') (i : ℕ) :
    μ.r k (p ^ i) (p' ^ i) := by
  induction i with
  | zero => simpa using r_one μ hk
  | succ i ih => rw [pow_succ, pow_succ]; exact μ.mul _ _ _ _ _ ih h

theorem r_inv {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') :
    μ.r k p⁻¹ p'⁻¹ := by
  have h1 := r_one μ hk
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j p⁻¹
  have h2 := μ.mul _ _ _ _ _ h hu
  rw [mul_inv_cancel] at h2
  obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 (qeq_right μ h1 h2)
  refine r_right μ hu ((N'.qEq_equivalence _).symm ((N'.qEq_iff _ _).2 ⟨z, ?_⟩))
  rw [one_mul] at hz
  rw [← hz, inv_mul_cancel_left]

theorem r_incl {k K : ℕ} (k' : ℕ) (hK : K = k * k') (hk : k' ≠ 0) {p : N.QT k} {p' : N'.QT k} {q : N.QT K}
    {q' : N'.QT K} (h1 : q.1.1 = p.1.1 ^ k') (h2 : q.1.2 = p.1.2) (h3 : q'.1.1 = p'.1.1 ^ k')
    (h4 : q'.1.2 = p'.1.2) : μ.r k p p' ↔ μ.r K q q' := by
  subst hK
  exact μ.incl k k' p p' q q' hk h1 h2 h3 h4

theorem exists_one_of_inG {N : NumD C} {k : ℕ} {p : N.QT k} (h : N.InG p) : ∃ q, N.QEq p q ∧ q.1.1 = 1 := by
  obtain ⟨z, hz⟩ := h
  refine ⟨p * N.qTriv k (-z), (N.qEq_iff _ _).2 ⟨_, rfl⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change p.1.1.toAdd + k • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

theorem tot_G (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (p : N.QT k) (hp : p.1.1 = 1) :
    ∃ p', μ.r k p p' ∧ p'.1.1 = 1 := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j p
  obtain ⟨q, e, hq⟩ := exists_one_of_inG ((hA.2 j p u hu).1.1 ⟨0, by simp [hp]⟩)
  exact ⟨q, r_right μ hu e, hq⟩

theorem cotot_G (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (p' : N'.QT k) (hp : p'.1.1 = 1) :
    ∃ p, μ.r k p p' ∧ p.1.1 = 1 := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.cotot j p'
  obtain ⟨q, e, hq⟩ := exists_one_of_inG ((hA.2 j u p' hu).1.2 ⟨0, by simp [hp]⟩)
  exact ⟨q, r_left μ hu e, hq⟩

theorem exists_tor_of_inT {N : NumD C} {k : ℕ} {p : N.QT k} (h : N.InT p) :
    ∃ t ht, N.QEq p (N.qTor t ht) := by
  obtain ⟨q, e, h1, h2⟩ := h
  obtain ⟨t, ht⟩ := (N.exists_tor_iff _).2 h2
  have h3 : t ^ k = 1 := by
    apply N.tor_injective
    rw [N.tor_pow, ht, N.mem_QT.1 q.2, h1, N.tor_one]
    exact N.io_zero
  refine ⟨t, h3, ?_⟩
  have : q = N.qTor t h3 := Subtype.ext (Prod.ext h1 ht.symm)
  exact this ▸ e

theorem inT_tor {N : NumD C} {k : ℕ} (t : Multiplicative N.X →* Cˣ) (ht : t ^ k = 1) : N.InT (N.qTor t ht) :=
  ⟨_, (N.qEq_equivalence k).refl _, rfl, rfl⟩

theorem thetaMatching_exists_right_torus_torsion (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (t : Multiplicative N.X →* Cˣ) (ht : t ^ k = 1) :
    ∃ t' ht', μ.r k (N.qTor t ht) (N'.qTor t' ht') := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j (N.qTor t ht)
  obtain ⟨t', ht', e⟩ := exists_tor_of_inT ((hA.2 j _ u hu).2.1 (inT_tor t ht))
  exact ⟨t', ht', r_right μ hu e⟩

theorem thetaMatching_exists_left_torus_torsion (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (t' : Multiplicative N'.X →* Cˣ) (ht' : t' ^ k = 1) :
    ∃ t ht, μ.r k (N.qTor t ht) (N'.qTor t' ht') := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.cotot j (N'.qTor t' ht')
  obtain ⟨t, ht, e⟩ := exists_tor_of_inT ((hA.2 j u _ hu).2.2 (inT_tor t' ht'))
  exact ⟨t, ht, r_left μ hu e⟩

theorem exists_torus_bij (hn : n ≠ 0) (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) :
    ∃ E : {t : Multiplicative N.X →* Cˣ // t ^ k = 1} → {t : Multiplicative N'.X →* Cˣ // t ^ k = 1},
      Function.Bijective E ∧ ∀ t, μ.r k (N.qTor t.1 t.2) (N'.qTor (E t).1 (E t).2) := by
  have hk0 : k ≠ 0 := by obtain ⟨j, rfl⟩ := hk; exact pow_ne_zero _ hn
  choose f hf h using thetaMatching_exists_right_torus_torsion μ hA hk
  refine ⟨fun t => ⟨f t.1 t.2, hf t.1 t.2⟩, ⟨fun s t e => ?_, fun t' => ?_⟩, fun t => h t.1 t.2⟩
  · have e' : N'.qTor _ (hf s.1 s.2) = N'.qTor _ (hf t.1 t.2) :=
      congrArg (fun u : {t : Multiplicative N'.X →* Cˣ // t ^ k = 1} => N'.qTor u.1 u.2) e
    have h1 := h s.1 s.2
    rw [e'] at h1
    have := eq_of_qeq hk0 (μ.inj k _ _ _ h1 (h t.1 t.2)) rfl
    exact Subtype.ext (N.tor_injective (congrArg (fun q : N.QT k => q.1.2) this))
  · obtain ⟨t, ht, e⟩ := thetaMatching_exists_left_torus_torsion μ hA hk t'.1 t'.2
    refine ⟨⟨t, ht⟩, Subtype.ext (N'.tor_injective ?_)⟩
    exact congrArg (fun q : N'.QT k => q.1.2) (eq_of_qeq hk0 (qeq_right μ (h t ht) e) rfl)

def Cl (j : ℕ) (x : N.X) (x' : N'.X) : Prop :=
  ∃ p p', μ.r (n ^ j) p p' ∧ p.1.1.toAdd = x ∧ p'.1.1.toAdd = x'

theorem Cl.add {j : ℕ} {x y : N.X} {x' y' : N'.X} (h : Cl μ j x x') (h' : Cl μ j y y') :
    Cl μ j (x + y) (x' + y') := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  obtain ⟨q, q', h', rfl, rfl⟩ := h'
  exact ⟨_, _, μ.mul _ _ _ _ _ h h', rfl, rfl⟩

theorem Cl.cong (hA : μ.A) {j : ℕ} {x y : N.X} {x' y' : N'.X} (h : Cl μ j x x') (h' : Cl μ j y y') :
    (∃ z, y = x + n ^ j • z) ↔ ∃ z', y' = x' + n ^ j • z' := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  obtain ⟨q, q', h', rfl, rfl⟩ := h'
  have := (hA.2 j _ _ (μ.mul _ _ _ _ _ (r_inv μ ⟨j, rfl⟩ h) h')).1
  simp only [← neg_add_eq_iff_eq_add]
  exact this

theorem Cl.shift {j : ℕ} {x : N.X} {x' : N'.X} (h : Cl μ j x x') (z : N.X) (z' : N'.X) :
    Cl μ j (x + n ^ j • z) (x' + n ^ j • z') := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  exact ⟨p * N.qTriv _ z, p' * N'.qTriv _ z',
    r_right μ (r_left μ h ((N.qEq_iff _ _).2 ⟨z, rfl⟩)) ((N'.qEq_iff _ _).2 ⟨z', rfl⟩), rfl, rfl⟩

theorem Cl.down (hn : n ≠ 0) {j : ℕ} {x : N.X} {x' : N'.X} (h : Cl μ (j + 1) x x') : Cl μ j x x' := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  refine ⟨⟨(p.1.1, p.1.2 ^ n), ?_⟩, ⟨(p'.1.1, p'.1.2 ^ n), ?_⟩, ?_, rfl, rfl⟩
  · rw [NumD.mem_QT, ← pow_mul, ← pow_succ']; exact p.2
  · rw [NumD.mem_QT, ← pow_mul, ← pow_succ']; exact p'.2
  · exact (r_incl μ n (pow_succ n j) hn rfl rfl rfl rfl).2 (r_pow μ ⟨_, rfl⟩ h n)

theorem Cl.tor {j : ℕ} {x : N.X} {x' : N'.X} (h : Cl μ j x x') {t : Multiplicative N.X →* Cˣ} {ht : t ^ n ^ j = 1}
    {t' : Multiplicative N'.X →* Cˣ} {ht' : t' ^ n ^ j = 1} (e : μ.r _ (N.qTor t ht) (N'.qTor t' ht')) :
    t' (Multiplicative.ofAdd x') = t (Multiplicative.ofAdd x) := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  have := μ.wp _ _ _ _ _ e h
  rwa [NumD.wp_qTor, NumD.wp_qTor] at this
end

end GlobalTheory.MatchTerm
