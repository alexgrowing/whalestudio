import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependence
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormRepGeneratorsAndThetaSeriesTermStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransportStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmPairingEqOneOfOddOfDiag
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisUniqueMinPairSums
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierExtractionTsumClass

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.LabelsAgree

section Transport
variable {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N')

def toHom : NumD.Hom (RingHom.id O) N N' where
  φ := J.φ.toMonoidHom
  h := J.h
  h_one := J.h_one
  θ_eq := J.θ_eq
  σ_eq := J.σ_eq
  lam := J.lam
  th_eq := J.th_eq
  e := J.e
  c_eq := J.c_eq
  ψ_eq := J.ψ_eq

theorem rel_iff (g : N.Gt) (g' : N'.Gt) : (toHom J).Rel g g' ↔ J.Rel g g' := Iff.rfl

def TR {k : ℕ} (p : N.QT k) (p' : N'.QT k) : Prop :=
  p'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 p'.1.2

theorem rel_unique {g : N.Gt} {a b : N'.Gt} (ha : J.Rel g a) (hb : J.Rel g b) : a = b :=
  ((GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).1 g).unique ha hb

theorem rel_mul {g h : N.Gt} {a b : N'.Gt} (ha : J.Rel g a) (hb : J.Rel h b) : J.Rel (g * h) (a * b) :=
  (GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).2.1 g h a b ha hb

theorem rel_pow {g : N.Gt} {a : N'.Gt} (ha : J.Rel g a) (k : ℕ) : J.Rel (g ^ k) (a ^ k) := by
  induction k with
  | zero => simpa using J.rel_one
  | succ k ih => rw [pow_succ, pow_succ]; exact rel_mul J ih ha

theorem tr_exists {k : ℕ} (p : N.QT k) : ∃ p', TR J p p' := by
  obtain ⟨g', hg'⟩ := ((GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).1 p.1.2).exists
  have h1 := rel_pow J hg' k
  rw [N.mem_QT.1 p.2] at h1
  have h2 : J.Rel (N.io p.1.1.toAdd) (N'.io (J.e p.1.1.toAdd)) := (GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).2.2.1 _
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g'), rel_unique J h1 h2⟩, rfl, hg'⟩

theorem tr_unique {k : ℕ} {p : N.QT k} {a b : N'.QT k} (ha : TR J p a) (hb : TR J p b) : a = b :=
  Subtype.ext (Prod.ext (ha.1.trans hb.1.symm) (rel_unique J ha.2 hb.2))

theorem tr_mul {k : ℕ} {p q : N.QT k} {a b : N'.QT k} (ha : TR J p a) (hb : TR J q b) :
    TR J (p * q) (a * b) := by
  refine ⟨?_, rel_mul J ha.2 hb.2⟩
  change a.1.1.toAdd + b.1.1.toAdd = J.e (p.1.1.toAdd + q.1.1.toAdd)
  rw [map_add, ha.1, hb.1]

theorem tr_wp {k : ℕ} {p q : N.QT k} {a b : N'.QT k} (ha : TR J p a) (hb : TR J q b) :
    N'.wp a b = N.wp p q :=
  (GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).2.2.2.1 k p q a b ha.1 ha.2 hb.1 hb.2

theorem tr_txT {m : ℕ} (hm : Odd m) {p : N.QT (m ^ 2)} {a : N'.QT (m ^ 2)} (ha : TR J p a) (χ : N.X) :
    N'.txT m a (J.e χ) = J.lam * N.txT m p χ :=
  ((GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).2.2.2.2 m hm p a ha.1 ha.2 χ).1

theorem eq_of_qEq {k : ℕ} (hk : k ≠ 0) {p q : N.QT k} (h : N.QEq p q) (hy : p.1.1 = q.1.1) : p = q := by
  obtain ⟨z, h1, h2⟩ := h
  have hz : k • z = 0 := by rw [hy] at h1; exact left_eq_add.1 h1
  have hz0 : z = 0 := by
    have := TorsionFourier.add_nsmul_injective (Nat.pos_of_ne_zero hk) (0 : N.X) (a₁ := z) (a₂ := 0)
      (by simp [hz])
    exact this
  rw [hz0, N.io_zero, mul_one] at h2
  exact Subtype.ext (Prod.ext hy h2.symm)

theorem wp_mul_left {k : ℕ} (p p' q : N.QT k) : N.wp (p * p') q = N.wp p q * N.wp p' q :=
  (GlobalTheory.T.degenerationWeilPairing_properties _ N k p p' q).1

theorem wp_mul_right {k : ℕ} (p q q' : N.QT k) : N.wp p (q * q') = N.wp p q * N.wp p q' := by
  rw [N.wp_swap, wp_mul_left, mul_inv, ← N.wp_swap, ← N.wp_swap]

theorem wp_tor {k : ℕ} {d : N.QT k} (h1 : d.1.1 = 1) (h2 : d.1.2.b = 1) (q : N.QT k) :
    N.wp d q = d.1.2.s q.1.1.toAdd :=
  (GlobalTheory.T.degenerationWeilPairing_properties _ N k d q q).2.2.2.2.2.1 h1 h2

end Transport

theorem exists_char_root {C X : Type} [Field C] [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (u : Multiplicative X →* Cˣ) {k : ℕ} (hk : k ≠ 0) : ∃ t : Multiplicative X →* Cˣ, t ^ k = u := by
  let b := Module.finBasis ℤ X
  have h : ∀ x : Cˣ, ∃ y : Cˣ, y ^ k = x := fun x => by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : C) (Nat.pos_of_ne_zero hk)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hk] at hy
      exact x.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩
  choose r hr using h
  refine ⟨TorsionFourier.charOfValues b fun i => r (u (Multiplicative.ofAdd (b i))), MonoidHom.ext fun x => ?_⟩
  change (∏ i, r (u (Multiplicative.ofAdd (b i))) ^ (b.repr x.toAdd i)) ^ k = u (Multiplicative.ofAdd x.toAdd)
  rw [TorsionFourier.char_apply_eq_prod b u, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hr]

section Level
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n) (J : NumD.Iso N N')

theorem exists_norm (hB : μ.B J.e) (j : ℕ) (p : N.QT (n ^ j)) :
    ∃ p', μ.r (n ^ j) p p' ∧ p'.1.1.toAdd = J.e p.1.1.toAdd := by
  obtain ⟨p', hp'⟩ := μ.tot j p
  obtain ⟨z, hz⟩ := hB j p p' hp'
  refine ⟨p' * N'.qTriv _ (-z), (μ.eqv _ p p p' _ hp' ((N.qEq_equivalence _).refl p)).2
    ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩), ?_⟩
  change p'.1.1.toAdd + n ^ j • (-z) = _
  rw [hz, smul_neg, add_neg_cancel_right]

theorem r_unique {k : ℕ} (hk : k ≠ 0) {p : N.QT k} {a b : N'.QT k} (ha : μ.r k p a) (hb : μ.r k p b)
    (hy : a.1.1 = b.1.1) : a = b :=
  eq_of_qEq hk ((μ.eqv _ p p a b ha ((N.qEq_equivalence _).refl p)).1 hb) hy

theorem r_of_tr_zero (hB : μ.B J.e) (hG : μ.OnG J) {j : ℕ} {p : N.QT (n ^ j)} {a : N'.QT (n ^ j)}
    (hp : p.1.1 = 1) (ha : TR J p a) : μ.r (n ^ j) p a := by
  obtain ⟨p', h1, h2⟩ := exists_norm μ J hB j p
  have h3 : p'.1.1 = 1 := by
    rw [hp, toAdd_one, map_zero] at h2
    exact h2
  rw [tr_unique J ha ⟨h2, hG j p p' h1 hp h3⟩]
  exact h1

theorem exists_pre_zero (hA : μ.A) (hG : μ.OnG J) {j : ℕ} {a : N'.QT (n ^ j)} (ha : a.1.1 = 1) :
    ∃ p, μ.r (n ^ j) p a ∧ TR J p a := by
  obtain ⟨p₀, h₀⟩ := μ.cotot j a
  obtain ⟨z, hz⟩ := (hA.2 j p₀ a h₀).1.2 ⟨0, by rw [ha]; simp⟩
  have h1 : μ.r (n ^ j) (p₀ * N.qTriv _ (-z)) a :=
    (μ.eqv _ p₀ _ a a h₀ ((N.qEq_iff _ _).2 ⟨-z, rfl⟩)).2 ((N'.qEq_equivalence _).refl a)
  have h2 : (p₀ * N.qTriv _ (-z)).1.1 = 1 := by
    change p₀.1.1.toAdd + n ^ j • (-z) = 0
    rw [hz, smul_neg, add_neg_cancel]
  refine ⟨_, h1, ?_, hG j _ _ h1 h2 ha⟩
  rw [h2, ha, toAdd_one, toAdd_one, map_zero]

def Defect (k : ℕ) (x : N.X) (d : N'.QT k) : Prop :=
  d.1.1 = 1 ∧ d.1.2.b = 1 ∧ ∀ p a, p.1.1.toAdd = x → TR J p a → μ.r k p (a * d)

theorem exists_defect [IsAlgClosed C] {g g' : ℕ} (hn : (n : C) ≠ 0) (hT : N.Tors n g) (hT' : N'.Tors n g')
    (hA : μ.A) (hB : μ.B J.e) (hG : μ.OnG J) (j : ℕ) (x : N.X) : ∃ d, Defect μ J (n ^ j) x d := by
  have hn0 : n ^ j ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hn)
  obtain ⟨p₀, hp₀⟩ := (GlobalTheory.Ex.QStr.qStructure C N n g hn hT j).2.2.1 x
  obtain ⟨p', h1, h2⟩ := exists_norm μ J hB j p₀
  obtain ⟨a₀, ha₀⟩ := tr_exists J p₀
  have e : p' = a₀ * (p' / a₀) := by simp
  have hd : (p' / a₀).1.1 = 1 := by
    change p'.1.1.toAdd - a₀.1.1.toAdd = 0
    rw [h2, ha₀.1, sub_self]
  refine ⟨p' / a₀, hd, ?_, fun p a hp ha => ?_⟩
  · obtain ⟨d₀, q1, q2, q3⟩ := ((GlobalTheory.Ex.QStr.qStructure C N' n g' hn hT' j).2.2.2.2.1 (p' / a₀)).1 fun q' hq' => by
      obtain ⟨q, r1, r2⟩ := exists_pre_zero μ J hA hG hq'
      have w1 := μ.wp _ _ _ _ _ h1 r1
      rw [e, wp_mul_left, tr_wp J ha₀ r2] at w1
      exact mul_eq_left.1 w1
    rw [eq_of_qEq hn0 q1 (hd.trans q2.symm)]
    exact q3
  · obtain ⟨u, hu⟩ := tr_exists J (p / p₀)
    have h3 : (p / p₀).1.1 = 1 := by
      change p.1.1.toAdd - p₀.1.1.toAdd = 0
      rw [hp, hp₀, sub_self]
    have h4 := μ.mul _ _ _ _ _ h1 (r_of_tr_zero μ J hB hG h3 hu)
    have h5 := tr_mul J ha₀ hu
    rw [mul_div_cancel] at h4 h5
    rw [tr_unique J ha h5, mul_right_comm, ← e]
    exact h4

theorem defect_add {k : ℕ} (hk : k ≠ 0) {x x' : N.X} (p p' : N.QT k) (hp : p.1.1.toAdd = x)
    (hp' : p'.1.1.toAdd = x') {d d' d'' : N'.QT k}
    (h : Defect μ J k x d) (h' : Defect μ J k x' d') (h'' : Defect μ J k (x + x') d'') : d'' = d * d' := by
  obtain ⟨a, ha⟩ := tr_exists J p
  obtain ⟨a', ha'⟩ := tr_exists J p'
  have h1 := μ.mul _ _ _ _ _ (h.2.2 p a hp ha) (h'.2.2 p' a' hp' ha')
  rw [mul_mul_mul_comm] at h1
  have h2 := h''.2.2 (p * p') (a * a') (by rw [← hp, ← hp']; rfl) (tr_mul J ha ha')
  refine mul_left_cancel (r_unique μ hk h2 h1 ?_)
  change a.1.1 * a'.1.1 * d''.1.1 = a.1.1 * a'.1.1 * (d.1.1 * d'.1.1)
  rw [h.1, h'.1, h''.1, mul_one (1 : Multiplicative N'.X)]

theorem defect_symm {k : ℕ} {x x' : N.X} (p p' : N.QT k) (hp : p.1.1.toAdd = x)
    (hp' : p'.1.1.toAdd = x') {d d' : N'.QT k}
    (h : Defect μ J k x d) (h' : Defect μ J k x' d') : d.1.2.s (J.e x') = d'.1.2.s (J.e x) := by
  obtain ⟨a, ha⟩ := tr_exists J p
  obtain ⟨a', ha'⟩ := tr_exists J p'
  have h1 := μ.wp _ _ _ _ _ (h.2.2 p a hp ha) (h'.2.2 p' a' hp' ha')
  rw [wp_mul_left, wp_mul_right, tr_wp J ha ha', mul_assoc, mul_eq_left, N'.wp_swap, wp_tor h'.1 h'.2.1,
    wp_tor h.1 h.2.1, inv_mul_eq_one] at h1
  have e : (a' * d').1.1.toAdd = J.e x' := by
    change (a'.1.1 * d'.1.1).toAdd = _
    rw [h'.1, mul_one, ha'.1, hp']
  rw [← e, ← h1, ha.1, hp]

end Level

theorem exists_good {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {n g : ℕ} (hn : (n : C) ≠ 0)
    (hT : N.Tors n g) {j : ℕ} (hj : j ≠ 0) (x : N.X) :
    ∃ p : N.QT ((n ^ j) ^ 2), p.1.1.toAdd = x ∧ ‖N.th (p.1.2.b ^ n ^ j)‖ = 1 := by
  have hn0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by rintro rfl; simp at hn))
  have root : ∀ (i : ℕ) (a : N.A), ∃ b, b ^ n ^ i = a := by
    intro i
    induction i with
    | zero => exact fun a => ⟨a, by simp⟩
    | succ i ih =>
      intro a
      obtain ⟨b, rfl⟩ := hT.div a
      obtain ⟨b', rfl⟩ := ih b
      exact ⟨b', by rw [pow_succ, pow_mul]⟩
  obtain ⟨a, ha⟩ := root j (N.c x)
  obtain ⟨t, ht, hth⟩ := hT.good a
  obtain ⟨b, hb⟩ := root j (a * t)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.Ex.QStr.qStructure C N n g hn hT j).1 b
  have ht' : t ^ n ^ j = 1 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ', pow_mul, ht, one_pow]
  obtain ⟨u, hu⟩ := (N.exists_tor_iff (N.io x * (γ ^ (n ^ j) ^ 2)⁻¹)).2 (by
    rw [NumD.Gt.mul_b, NumD.Gt.inv_b, NumD.Gt.pow_b, hγ, sq, pow_mul, hb, mul_pow, ht', ha, mul_one, N.io_b,
      mul_inv_cancel])
  obtain ⟨v, hv⟩ := exists_char_root u hn0
  refine ⟨⟨(Multiplicative.ofAdd x, N.tor v * γ), ?_⟩, rfl, ?_⟩
  · rw [N.mem_QT, mul_pow, ← N.tor_pow, hv, hu, inv_mul_cancel_right]
    rfl
  · change ‖N.th ((1 * γ.b) ^ n ^ j)‖ = 1
    rw [one_mul, hγ, hb, hth]

theorem tendsto_txT {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (hI : N.Int q) {m : ℕ}
    (hm : Odd m) (p : N.QT (m ^ 2)) : Filter.Tendsto (N.txT m p) Filter.cofinite (nhds 0) := by
  have hm0 : 0 < m := hm.pos
  have h1 := hI.pos.comp (TorsionFourier.add_nsmul_injective hm0 p.1.1.toAdd).tendsto_cofinite
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (h1.atTop_div_const (r := (m : ℝ) ^ 2) (by positivity))
  refine squeeze_zero_norm (fun χ => ?_) h2
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p χ]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)

theorem norm_char {C X : Type} [NormedField C] [AddCommGroup X] {k : ℕ} (hk : k ≠ 0) {t : Multiplicative X →* Cˣ}
    (ht : t ^ k = 1) (x : Multiplicative X) : ‖(t x : C)‖ = 1 := by
  have h1 : ‖(t x : C)‖ ^ k = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, TorsionFourier.apply_pow_eq_one ht, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).1 h1

theorem eq_one_of_sums {C X : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} (hm : ‖(m : C)‖ = 1)
    (T : X → C) (hT : Filter.Tendsto T Filter.cofinite (nhds 0)) (h0 : T 0 ≠ 0)
    (hdom : ∀ z, z ≠ 0 → ‖T (m • z)‖ < ‖T 0‖) (w : C) (τ : Multiplicative X →* Cˣ) (hτ : τ ^ m = 1)
    (h : ∀ u : Multiplicative X →* Cˣ, u ^ m = 1 →
      ∑' χ, w * (τ (Multiplicative.ofAdd χ) : C) * T χ * (u (Multiplicative.ofAdd χ) : C) =
        ∑' χ, T χ * (u (Multiplicative.ofAdd χ) : C)) : w = 1 := by
  have hmC : (m : C) ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; exact zero_ne_one hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmC
  haveI : NeZero (m : C) := ⟨hmC⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C m
  have hT' : Filter.Tendsto (fun χ => w * (τ (Multiplicative.ofAdd χ) : C) * T χ) Filter.cofinite (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hT ⊢
    simpa only [norm_mul, norm_char hm0 hτ, mul_one, mul_zero] using hT.const_mul ‖w‖
  obtain ⟨-, a1, a2⟩ := fourier_extraction_tsum_class C X m ζ (Nat.pos_of_ne_zero hm0) hm hζ T hT 0
  obtain ⟨-, b1, -⟩ := fourier_extraction_tsum_class C X m ζ (Nat.pos_of_ne_zero hm0) hm hζ _ hT' 0
  simp only [zero_add] at a1 a2 b1
  rw [finsum_congr fun u => by rw [h u.1 u.2], a1] at b1
  have e : ∀ z : X, (τ (Multiplicative.ofAdd (m • z)) : C) = 1 := fun z => by
    rw [ofAdd_nsmul, map_pow, TorsionFourier.apply_pow_eq_one hτ, Units.val_one]
  simp only [e, mul_one, tsum_mul_left] at b1
  have b2 := mul_left_cancel₀ (pow_ne_zero _ hmC) b1
  have hS : ∑' z, T (m • z) ≠ 0 := by
    rw [← norm_ne_zero_iff, a2 hdom, norm_ne_zero_iff]; exact h0
  exact (mul_eq_right₀ hS).1 b2.symm

theorem defect_diag {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    {N N' : NumD C} {q : QuadraticMap ℤ N.X ℝ} {n g : ℕ} (ho : Odd n) (hn : ‖(n : C)‖ = 1) (hI : N.Int q)
    (hT : N.Tors n g) (μ : Match N N' n) (J : NumD.Iso N N') (hl : (J.lam : C) = μ.c₀) {j : ℕ} (hj : j ≠ 0)
    {x : N.X} (hx : ∀ z, z ≠ 0 → q x < q (x + (n ^ j) ^ 2 • z)) {d : N'.QT ((n ^ j) ^ 2)}
    (hd : Defect μ J ((n ^ j) ^ 2) x d) : d.1.2.s (J.e x) ^ (((n ^ j) ^ 2 - 1) / 2 + 1) = 1 := by
  have hnC : (n : C) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  obtain ⟨p, hp, hth⟩ := exists_good hnC hT hj x
  have htx := μ.tx j
  have hmn : ‖((n ^ j : ℕ) : C)‖ = 1 := by rw [Nat.cast_pow, norm_pow, hn, one_pow]
  have hm : Odd (n ^ j) := ho.pow
  generalize n ^ j = m at *
  have hm0 : m ≠ 0 := hm.pos.ne'
  obtain ⟨t', ht'⟩ := (N'.exists_tor_iff d.1.2).2 hd.2.1
  have ht'k : t' ^ m ^ 2 = 1 := by
    apply N'.tor_injective
    rw [N'.tor_pow, ht', N'.mem_QT.1 d.2, hd.1, toAdd_one, N'.io_zero, N'.tor_one]
  let τ : Multiplicative N.X →* Cˣ := (t'.comp (AddMonoidHom.toMultiplicative J.e.toAddMonoidHom)) ^ m
  have hτ : ∀ χ, τ (Multiplicative.ofAdd χ) = t' (Multiplicative.ofAdd (J.e χ)) ^ m := fun _ => rfl
  have hτm : τ ^ m = 1 := MonoidHom.ext fun χ => by
    change (t' (Multiplicative.ofAdd (J.e χ.toAdd)) ^ m) ^ m = 1
    rw [← pow_mul, ← sq, TorsionFourier.apply_pow_eq_one ht'k]
  have hnorm := (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p
  have h00 : ‖N.txT m p 0‖ = Real.exp (-(q x / (m : ℝ) ^ 2)) := by
    rw [hnorm, N.c_zero, one_mul, hth, mul_one, smul_zero, add_zero, hp]
  rw [← ht', NumD.torus_generator_apply]
  apply Units.ext
  rw [Units.val_one]
  refine eq_one_of_sums hmn (N.txT m p) (tendsto_txT hI hm p) ?_ (fun z hz => ?_) _ τ hτm fun u hu => ?_
  · rw [← norm_pos_iff, h00]; exact Real.exp_pos _
  · rw [h00, hnorm, hp, smul_smul, ← sq]
    refine (mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)).trans_lt (Real.exp_lt_exp.2 (neg_lt_neg ?_))
    exact div_lt_div_of_pos_right (hx z hz) (by positivity)
  · obtain ⟨t, rfl⟩ := exists_char_root u hm0
    have ht : t ^ m ^ 2 = 1 := by rw [sq, pow_mul, hu]
    obtain ⟨a, ha⟩ := tr_exists J (p * N.qTor t ht)
    have hpx : (p * N.qTor t ht).1.1 = p.1.1 := mul_one _
    have h1 := htx _ _ (hd.2.2 _ a (by rw [hpx, hp]) ha)
    have hay : a.1.1 = Multiplicative.ofAdd (J.e x) := by
      rw [← hp, ← hpx, ← ha.1]; rfl
    have hpy : p.1.1 = Multiplicative.ofAdd x := by rw [← hp]; rfl
    have h2 : ∀ χ, N.txT m (p * N.qTor t ht) χ = (t (Multiplicative.ofAdd x) ^ ((m ^ 2 - 1) / 2 + 1) : Cˣ) *
        (N.txT m p χ * ((t ^ m) (Multiplicative.ofAdd χ) : C)) := fun χ => by
      rw [(GlobalTheory.Ex.txT_shift C N m hm p (p * N.qTor t ht) χ).2 t hpx rfl, hpy, toAdd_ofAdd, ofAdd_add, ofAdd_nsmul,
        map_mul, map_pow, MonoidHom.pow_apply]
      push_cast
      ring
    have h3 : ∀ χ, N'.txT m (a * d) (J.e χ) = μ.c₀ * ((t (Multiplicative.ofAdd x) ^ ((m ^ 2 - 1) / 2 + 1) : Cˣ) *
        (((t' (Multiplicative.ofAdd (J.e x)) ^ ((m ^ 2 - 1) / 2 + 1) : Cˣ) : C) * (τ (Multiplicative.ofAdd χ) : C) *
          N.txT m p χ * ((t ^ m) (Multiplicative.ofAdd χ) : C))) := fun χ => by
      rw [(GlobalTheory.Ex.txT_shift C N' m hm a (a * d) (J.e χ)).2 t' (by change a.1.1 * d.1.1 = _; rw [hd.1, mul_one])
        (by rw [ht']; rfl), tr_txT J hm ha, h2, hl, hay, toAdd_ofAdd, ofAdd_add, ofAdd_nsmul,
        map_mul, map_pow, hτ]
      push_cast
      ring
    rw [NumD.tx, NumD.tx, ← J.e.toEquiv.tsum_eq] at h1
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, h3, tsum_mul_left] at h1
    exact mul_left_cancel₀ (Units.ne_zero _) (mul_left_cancel₀ μ.c₀_ne h1)

theorem main : AllMatch fun {_} _ {N} {N'} {_} μ _ _ =>
    μ.A → ∀ J : NumD.Iso N N', μ.B J.e → μ.OnG J → (J.lam : _) = μ.c₀ → μ.OnQ J := by
  intro C _ _ _ _ N N' q q' n g g' hp ho hn hI _ hT hT' μ hA J hB hG hl i p p' h1 h2
  have hnC : (n : C) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have hn0 : n ≠ 0 := hp.ne_zero
  obtain ⟨j₀, hj₀⟩ := pow_unbounded_of_one_lt
    (1 + 4 * (Module.finrank ℤ N.X : ℝ) * (2 : ℝ) ^ ((Module.finrank ℤ N.X : ℝ) / 2))
    (show (1 : ℝ) < n by exact_mod_cast hp.one_lt)
  set j := i + j₀ + 1 with hj
  have hk : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn0)
  obtain ⟨e, he⟩ := exists_basis_unique_min_pair_sums N.X q hI.pos _ _ ((n ^ j) ^ 2) rfl le_rfl
    (hj₀.trans_le (by
      rw [← pow_mul, Nat.cast_pow]
      exact pow_le_pow_right₀ (by exact_mod_cast hp.one_le) (by omega)))
  have hd : ∀ x, ∃ d, Defect μ J ((n ^ j) ^ 2) x d := by
    rw [← pow_mul]; exact exists_defect μ J hnC hT hT' hA hB hG _
  have hs : ∀ x, ∃ s : N.QT ((n ^ j) ^ 2), s.1.1.toAdd = x := fun x =>
    (exists_good hnC hT (Nat.succ_ne_zero _) x).imp fun _ h => h.1
  choose d hd using hd
  choose s hs using hs
  have hodd : Odd ((n ^ j) ^ 2) := ho.pow.pow
  have key := symm_pairing_eq_one_of_odd_of_diag N.X Cˣ _ ((n ^ j) ^ 2) e
    ((((n ^ j) ^ 2 - 1) / 2 + 1 : ℕ) : ℤ) hodd
    (by
      obtain ⟨c, hc⟩ := hodd
      rw [hc]
      exact ⟨1, by omega⟩)
    (fun x y => (d x).1.2.s (J.e y))
    (fun x x' y => by
      rw [defect_add μ J hk (s x) (s x') (hs x) (hs x') (hd x) (hd x') (hd (x + x'))]
      change ((d x).1.2 * (d x').1.2).s _ = _
      rw [NumD.Gt.mul_s, (hd x').2.1, N'.cub.face₃, div_one])
    (fun x y => defect_symm μ J (s x) (s y) (hs x) (hs y) (hd x) (hd y))
    (fun x y => by
      obtain ⟨a, ha⟩ := tr_exists J (s y)
      have := (GlobalTheory.T.degenerationWeilPairing_properties _ N' _ (d x) a a).2.2.2.1
      rwa [wp_tor (hd x).1 (hd x).2.1, ha.1, hs] at this)
    (fun a => by
      rw [zpow_natCast]
      exact defect_diag ho hn hI hT μ J hl (Nat.succ_ne_zero _) (fun z hz => (he a a z hz).1) (hd _))
    (fun a b => by
      rw [zpow_natCast]
      exact defect_diag ho hn hI hT μ J hl (Nat.succ_ne_zero _) (fun z hz => (he a b z hz).2) (hd _))
  have hd1 : ∀ x, d x = 1 := fun x =>
    Subtype.ext (Prod.ext (hd x).1 (NumD.Gt.ext (hd x).2.1 (funext fun χ => by
      have := key x (J.e.symm χ)
      rwa [AddEquiv.apply_symm_apply] at this)))
  have top : ∀ (a : N.QT ((n ^ j) ^ 2)) (a' : N'.QT ((n ^ j) ^ 2)), TR J a a' → μ.r _ a a' := fun a a' h => by
    have := (hd _).2.2 a a' rfl h
    rwa [hd1, mul_one] at this
  have hkk : (n ^ j) ^ 2 = n ^ i * n ^ (i + 2 * j₀ + 2) := by rw [hj]; ring
  rw [hkk] at top
  generalize hk' : n ^ (i + 2 * j₀ + 2) = k' at top
  have hk'0 : k' ≠ 0 := hk' ▸ pow_ne_zero _ hn0
  let a : N.QT (n ^ i * k') := ⟨(p.1.1 ^ k', p.1.2), by
    rw [N.mem_QT, pow_mul, N.mem_QT.1 p.2, toAdd_pow, N.io_nsmul]⟩
  let a' : N'.QT (n ^ i * k') := ⟨(p'.1.1 ^ k', p'.1.2), by
    rw [N'.mem_QT, pow_mul, N'.mem_QT.1 p'.2, toAdd_pow, N'.io_nsmul]⟩
  refine (μ.incl _ k' p p' a a' hk'0 rfl rfl rfl rfl).2 (top a a' ⟨?_, h2⟩)
  change (p'.1.1 ^ k').toAdd = J.e (p.1.1 ^ k').toAdd
  rw [toAdd_pow, toAdd_pow, map_nsmul, h1]

end GlobalTheory.LabelsAgree
