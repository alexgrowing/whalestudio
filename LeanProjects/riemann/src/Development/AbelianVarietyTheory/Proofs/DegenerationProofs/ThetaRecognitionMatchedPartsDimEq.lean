import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterionStatement

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.MatchParts

section Gen
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}

theorem qrefl {k : ℕ} (p : N.QT k) : N.QEq p p := (N.qEq_equivalence k).refl p

theorem r_right (μ : Match N N' n) {k : ℕ} {p : N.QT k} {p' q' : N'.QT k} (h : μ.r k p p') :
    μ.r k p q' ↔ N'.QEq p' q' := μ.eqv k p p p' q' h (qrefl p)

theorem r_left (μ : Match N N' n) {k : ℕ} {p q : N.QT k} {p' : N'.QT k} (h : μ.r k p p') (e : N.QEq p q) :
    μ.r k q p' := (μ.eqv k p q p' p' h e).2 (qrefl p')

noncomputable def flip (μ : Match N N' n) : Match N' N n where
  r k p' p := μ.r k p p'
  tot := μ.cotot
  cotot := μ.tot
  mul k p q p' q' h h' := μ.mul k _ _ _ _ h h'
  eqv k p' q' p q h e :=
    ⟨fun h' => μ.inj k p q q' ((r_right μ h).2 e) h', fun e' => (μ.eqv k p q p' q' h e').2 e⟩
  inj k p' q' p h h' := (r_right μ h).1 h'
  incl k k' p' p q' q hk a b c d := μ.incl k k' p p' q q' hk c d a b
  wp k p' q' p q h h' := (μ.wp k p q p' q' h h').symm
  c₀ := μ.c₀⁻¹
  c₀_ne := inv_ne_zero μ.c₀_ne
  tx j p' p h := by rw [μ.tx j p p' h, ← mul_assoc, inv_mul_cancel₀ μ.c₀_ne, one_mul]

theorem tot' (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) (p : N.QT k) : ∃ p', μ.r k p p' := by
  obtain ⟨j, rfl⟩ := hk
  exact μ.tot j p

theorem qmul {k : ℕ} {p q : N.QT k} (a : N.QT k) (h : N.QEq p q) : N.QEq (a * p) (a * q) := by
  rw [N.qEq_iff] at h ⊢
  obtain ⟨z, rfl⟩ := h
  exact ⟨z, (mul_assoc _ _ _).symm⟩

theorem r_one (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) : μ.r k 1 1 := by
  obtain ⟨p', h⟩ := tot' μ hk 1
  have h2 := μ.mul k _ _ _ _ h h
  rw [mul_one] at h2
  have h3 := qmul p'⁻¹ ((r_right μ h).1 h2)
  rw [inv_mul_cancel, inv_mul_cancel_left] at h3
  exact (r_right μ h).2 ((N'.qEq_equivalence k).symm h3)

theorem r_pow (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p')
    (a : ℕ) : μ.r k (p ^ a) (p' ^ a) := by
  induction a with
  | zero => simpa using r_one μ hk
  | succ a ih => rw [pow_succ, pow_succ]; exact μ.mul k _ _ _ _ ih h

theorem r_inv (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') :
    μ.r k p⁻¹ p'⁻¹ := by
  obtain ⟨q', hq⟩ := tot' μ hk p⁻¹
  have h2 := μ.mul k _ _ _ _ h hq
  rw [mul_inv_cancel] at h2
  have h3 := qmul p'⁻¹ ((r_right μ h2).1 (r_one μ hk))
  rw [inv_mul_cancel_left, mul_one] at h3
  exact (r_right μ hq).2 h3

def ofG {k : ℕ} (x : N.Gt) (hx : x ^ k = 1) : N.QT k := ⟨(1, x), by rw [N.mem_QT]; exact hx.trans N.io_zero.symm⟩

theorem pow_eq_one_of {k : ℕ} (p : N.QT k) (h : p.1.1 = 1) : p.1.2 ^ k = 1 := by
  have := N.mem_QT.1 p.2
  rw [this, h]; exact N.io_zero

theorem exists_rep {k : ℕ} {p : N.QT k} (h : N.InG p) : ∃ q, N.QEq p q ∧ q.1.1 = 1 := by
  obtain ⟨z, hz⟩ := h
  refine ⟨p * N.qTriv k (-z), (N.qEq_iff _ _).2 ⟨_, rfl⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change p.1.1.toAdd + k • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

theorem y_pow {k : ℕ} (p : N.QT k) (a : ℕ) : (p ^ a).1.1.toAdd = a • p.1.1.toAdd := by simp

theorem nsmul_cancel {a : ℕ} (ha : a ≠ 0) {x y : N.X} (h : a • x = a • y) : x = y := by
  have : (a : ℤ) • x = (a : ℤ) • y := by simpa using h
  exact smul_right_injective N.X (by exact_mod_cast ha) this

theorem half_div (μ : Match N N' n) (j : ℕ) (hj : 2 ≤ j) (hdiv : ∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ n = γ)
    (hc : ‖μ.c₀‖ = 1)
    (hcos : ∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧
      ‖N.tx (n ^ j) (p * h)‖ = 1)
    (hsup : ∀ p : N'.QT ((n ^ j) ^ 2), ‖N'.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)
    (p : N.QT ((n ^ j) ^ 2)) (hp : p.1.1 = 1) :
    ∃ p', μ.r _ p p' ∧ ∃ z, p'.1.1.toAdd = n ^ j • z := by
  have hk : ∃ i, (n ^ j) ^ 2 = n ^ i := ⟨j * 2, (pow_mul _ _ _).symm⟩
  let P : N.QT ((n ^ j) ^ 2) → Prop := fun p => ∃ p', μ.r _ p p' ∧ ∃ z, p'.1.1.toAdd = n ^ j • z
  have Pmul : ∀ a b, P a → P b → P (a * b) := by
    rintro a b ⟨a', ha, z, hz⟩ ⟨b', hb, w, hw⟩
    refine ⟨a' * b', μ.mul _ _ _ _ _ ha hb, z + w, ?_⟩
    change a'.1.1.toAdd + b'.1.1.toAdd = _
    rw [hz, hw, smul_add]
  have Ppow : ∀ a (i : ℕ), P a → P (a ^ i) := by
    rintro a i ⟨a', ha, z, hz⟩
    exact ⟨a' ^ i, r_pow μ hk ha i, i • z, by rw [y_pow, hz, smul_comm]⟩
  have step : ∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ s d, P s ∧ d.1.1 = 1 ∧ p = s * d ^ n := by
    intro p hp
    obtain ⟨h, h1, h2, h3⟩ := hcos p hp
    obtain ⟨s', hs'⟩ := tot' μ hk (p * h)
    obtain ⟨δ, hδ⟩ := hdiv h.1.2⁻¹
    have hδ' : δ ^ (n ^ j) ^ 2 = 1 := by
      obtain ⟨i, hi⟩ : ∃ i, j * 2 = 1 + (j + 1) + i := ⟨j - 2, by omega⟩
      rw [← pow_mul, hi, pow_add, pow_add, pow_one, pow_mul, pow_mul, hδ, inv_pow, h2, inv_one, one_pow]
    refine ⟨p * h, ofG δ hδ', ⟨s', hs', hsup s' ?_⟩, rfl, ?_⟩
    · rw [μ.tx j _ _ hs', norm_mul, hc, h3, one_mul]
    · have : ofG δ hδ' ^ n = h⁻¹ := by
        refine Subtype.ext (Prod.ext ?_ ?_)
        · simp [ofG, h1]
        · simpa [ofG] using hδ
      rw [this, mul_inv_cancel_right]
  have iter : ∀ i : ℕ, ∃ s d, P s ∧ d.1.1 = 1 ∧ p = s * d ^ n ^ i := by
    intro i
    induction i with
    | zero => exact ⟨1, p, ⟨1, r_one μ hk, 0, by simp⟩, hp, by simp⟩
    | succ i ih =>
      obtain ⟨s, d, hs, hd, e⟩ := ih
      obtain ⟨s₂, d₂, hs₂, hd₂, e₂⟩ := step d hd
      refine ⟨s * s₂ ^ n ^ i, d₂, Pmul _ _ hs (Ppow _ _ hs₂), hd₂, ?_⟩
      rw [e, e₂, mul_pow, ← pow_mul d₂, mul_assoc s, pow_succ' n i]
  obtain ⟨s, d, hs, -, e⟩ := iter j
  rw [e]
  obtain ⟨d', hd'⟩ := tot' μ hk d
  exact Pmul _ _ hs ⟨_, r_pow μ hk hd' _, _, y_pow _ _⟩

theorem inG_of_half (μ : Match N N' n) {k k' K m : ℕ} (hK : K = k * k') (hm : K = m * m) (hkm : k ∣ m) (hm0 : m ≠ 0)
    (hlev : ∃ j, K = n ^ j) (hdiv : ∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ m = γ)
    (H : ∀ p : N.QT K, p.1.1 = 1 → ∃ p', μ.r K p p' ∧ ∃ z, p'.1.1.toAdd = m • z)
    (p : N.QT k) (p' : N'.QT k) (h : μ.r k p p') (hp : N.InG p) : N'.InG p' := by
  subst hK
  have hk' : k' ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hm0 hm0 (hm.symm.trans (mul_zero _))
  obtain ⟨p₀, e, h0⟩ := exists_rep hp
  replace h := r_left μ h e
  have hx := pow_eq_one_of p₀ h0
  obtain ⟨ξ, hξ⟩ := hdiv p₀.1.2
  have hξ' : ξ ^ (k * k') = 1 := by
    obtain ⟨c, hc⟩ := hkm
    rw [hm, pow_mul, hξ, hc, pow_mul, hx, one_pow]
  obtain ⟨ξ', hr, z, hz⟩ := H (ofG ξ hξ') rfl
  let q' : N'.QT (k * k') := ⟨(p'.1.1 ^ k', p'.1.2), by
    rw [N'.mem_QT, pow_mul, N'.mem_QT.1 p'.2, toAdd_pow, N'.io_nsmul]⟩
  have hq : μ.r (k * k') (ofG ξ hξ' ^ m) q' :=
    (μ.incl k k' p₀ p' _ q' hk' (by simp [ofG, h0]) (by simpa [ofG] using hξ) rfl rfl).1 h
  obtain ⟨w, hw, -⟩ := (r_right μ (r_pow μ hlev hr m)).1 hq
  refine ⟨z + w, nsmul_cancel hk' ?_⟩
  rw [y_pow, hz, smul_smul, ← hm, ← smul_add] at hw
  rw [smul_smul, mul_comm, ← hw]
  rfl

theorem inT_of_inG (μ : Match N N' n) (j : ℕ)
    (hG : ∀ p p', μ.r (n ^ j) p p' → N'.InG p' → N.InG p)
    (hT : ∀ p : N.QT (n ^ j), N.InT p → ∀ p' : N.QT (n ^ j), p'.1.1 = 1 → N.wp p p' = 1)
    (hT' : ∀ p : N'.QT (n ^ j), (∀ p' : N'.QT (n ^ j), p'.1.1 = 1 → N'.wp p p' = 1) → N'.InT p)
    (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)) (h : μ.r _ p p') (hp : N.InT p) : N'.InT p' := by
  refine hT' p' fun t' ht' => ?_
  obtain ⟨t, ht⟩ := μ.cotot j t'
  obtain ⟨t₀, e, h0⟩ := exists_rep (hG t t' ht ⟨0, by simp [ht']⟩)
  rw [μ.wp _ p t₀ p' t' h (r_left μ ht e)]
  exact hT p hp t₀ h0

theorem card_le_of_rel {α β : Type} [Finite β] (R : α → β → Prop) (h : ∀ a, ∃ b, R a b)
    (hi : ∀ a a' b, R a b → R a' b → a = a') : Nat.card α ≤ Nat.card β := by
  choose f hf using h
  exact Nat.card_le_card_of_injective f fun a a' e => hi a a' (f a) (hf a) (e ▸ hf a')

theorem rank_le (μ : Match N N' n) (hn : 1 < n) {k : ℕ} (hk : k = n ^ 1)
    (hG : ∀ p p', μ.r k p p' → N'.InG p' → N.InG p) (hy : ∀ y : N.X, ∃ p : N.QT k, p.1.1.toAdd = y) :
    Module.finrank ℤ N.X ≤ Module.finrank ℤ N'.X := by
  have hl : ∃ j, k = n ^ j := ⟨1, hk⟩
  have hk1 : 1 < k := by rw [hk, pow_one]; exact hn
  have h1 : Nat.card (N.X ⧸ (nsmulAddMonoidHom k : N.X →+ N.X).range) = k ^ Module.finrank ℤ N.X :=
    AddSubgroup.index_range_nsmul N.X k
  have h2 : Nat.card (N'.X ⧸ (nsmulAddMonoidHom k : N'.X →+ N'.X).range) = k ^ Module.finrank ℤ N'.X :=
    AddSubgroup.index_range_nsmul N'.X k
  haveI : Finite (N'.X ⧸ (nsmulAddMonoidHom k : N'.X →+ N'.X).range) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; positivity)
  rw [← Nat.pow_le_pow_iff_right hk1, ← h1, ← h2]
  refine card_le_of_rel (fun a b => ∃ p p', μ.r k p p' ∧ a = QuotientAddGroup.mk p.1.1.toAdd ∧
    b = QuotientAddGroup.mk p'.1.1.toAdd) (fun a => ?_) ?_
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨p, rfl⟩ := hy y
    obtain ⟨p', h⟩ := tot' μ hl p
    exact ⟨_, p, p', h, rfl, rfl⟩
  · rintro _ _ _ ⟨p, p', h, rfl, rfl⟩ ⟨q, q', h', rfl, e⟩
    obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 e
    obtain ⟨w, hw⟩ := hG _ _ (μ.mul k _ _ _ _ (r_inv μ hl h) h') ⟨z, hz.symm⟩
    exact QuotientAddGroup.eq.2 ⟨w, hw.symm⟩

theorem tors_le (μ : Match N N' n) (hn : 1 < n) {k a a' : ℕ} (hk : k = n ^ 1)
    (hG : ∀ p p', μ.r k p p' → N.InG p → N'.InG p')
    (e : Nonempty ((powMonoidHom k : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin a → ZMod k)))
    (e' : Nonempty ((powMonoidHom k : N'.Gt →* N'.Gt).ker ≃* Multiplicative (Fin a' → ZMod k))) : a ≤ a' := by
  have hl : ∃ j, k = n ^ j := ⟨1, hk⟩
  have hk1 : 1 < k := by rw [hk, pow_one]; exact hn
  obtain ⟨e⟩ := e
  obtain ⟨e'⟩ := e'
  have h1 : Nat.card (powMonoidHom k : N.Gt →* N.Gt).ker = k ^ a := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]; simp
  have h2 : Nat.card (powMonoidHom k : N'.Gt →* N'.Gt).ker = k ^ a' := by
    rw [Nat.card_congr e'.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]; simp
  haveI : Finite (powMonoidHom k : N'.Gt →* N'.Gt).ker :=
    Nat.finite_of_card_ne_zero (by rw [h2]; positivity)
  rw [← Nat.pow_le_pow_iff_right hk1, ← h1, ← h2]
  refine card_le_of_rel (fun x x' => μ.r k (ofG x.1 x.2) (ofG x'.1 x'.2)) (fun x => ?_) ?_
  · obtain ⟨p', h⟩ := tot' μ hl (ofG x.1 x.2)
    obtain ⟨q', e, h0⟩ := exists_rep (hG _ _ h ⟨0, by simp [ofG]⟩)
    refine ⟨⟨q'.1.2, pow_eq_one_of q' h0⟩, ?_⟩
    have : ofG q'.1.2 (pow_eq_one_of q' h0) = q' := Subtype.ext (Prod.ext h0.symm rfl)
    have h' := (r_right μ h).2 e
    rw [← this] at h'
    exact h'
  · intro x y b h h'
    obtain ⟨z, hz, hz'⟩ := μ.inj k _ _ _ h h'
    have : z = 0 := nsmul_cancel (a := k) (by omega) (by simpa [ofG] using hz.symm)
    rw [this, N.io_zero, mul_one] at hz'
    exact Subtype.ext hz'.symm

end Gen

section Main
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N N' : NumD C} {q : QuadraticMap ℤ N.X ℝ} {q' : QuadraticMap ℤ N'.X ℝ} {n g g' : ℕ}

theorem norm_le (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) : ‖μ.c₀‖ ≤ 1 := by
  obtain ⟨h, -, -, hh⟩ := (GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N q hI n g hn ho h1 hT 1 le_rfl).2.1 1 rfl
  obtain ⟨p', hp'⟩ := tot' μ ⟨1 * 2, (pow_mul n 1 2).symm⟩ (1 * h)
  have := ((GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N' q' hI' n g' hn ho h1 hT' 1 le_rfl).1 p').1
  rwa [μ.tx 1 _ _ hp', norm_mul, hh, mul_one] at this

theorem norm_eq (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) : ‖μ.c₀‖ = 1 := by
  refine le_antisymm (norm_le hn ho h1 hI hI' hT hT' μ) ?_
  have : ‖μ.c₀⁻¹‖ ≤ 1 := norm_le hn ho h1 hI' hI hT' hT (flip μ)
  rwa [norm_inv, inv_le_one₀ (norm_pos_iff.2 μ.c₀_ne)] at this

theorem inG_imp (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) (j : ℕ) (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j))
    (h : μ.r _ p p') (hp : N.InG p) : N'.InG p' := by
  have h0 : (n : C) ≠ 0 := fun e => by simp [e] at h1
  refine inG_of_half μ (k' := n ^ (j + 4)) (K := (n ^ (j + 2)) ^ 2) (m := n ^ (j + 2)) (by ring) (by ring)
    (pow_dvd_pow _ (by omega)) (pow_ne_zero _ hn.ne_zero) ⟨_, (pow_mul _ _ _).symm⟩
    (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT (j + 2)).2.1 ?_ p p' h hp
  exact half_div μ (j + 2) (by omega) (by simpa using (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT 1).2.1)
    (norm_eq hn ho h1 hI hI' hT hT' μ) (GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N q hI n g hn ho h1 hT (j + 2) (by omega)).2.1
    fun p => ((GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N' q' hI' n g' hn ho h1 hT' (j + 2) (by omega)).1 p).2

theorem inT_imp (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) (j : ℕ) (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j))
    (h : μ.r _ p p') (hp : N.InT p) : N'.InT p' := by
  have h0 : (n : C) ≠ 0 := fun e => by simp [e] at h1
  exact inT_of_inG μ j (fun p p' h => inG_imp hn ho h1 hI' hI hT' hT (flip μ) j p' p h)
    (fun p => ((GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT j).2.2.2.2.1 p).2)
    (fun p => ((GlobalTheory.T.degenerationData_torsion_structure_algClosed C N' n g' h0 hT' j).2.2.2.2.1 p).1) p p' h hp

theorem ranks_le (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) :
    Module.finrank ℤ N.X ≤ Module.finrank ℤ N'.X ∧
      2 * g + Module.finrank ℤ N.X ≤ 2 * g' + Module.finrank ℤ N'.X := by
  have h0 : (n : C) ≠ 0 := fun e => by simp [e] at h1
  exact ⟨rank_le μ hn.one_lt rfl (fun p p' h => inG_imp hn ho h1 hI' hI hT' hT (flip μ) 1 p' p h)
      (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT 1).2.2.1,
    tors_le μ hn.one_lt rfl (inG_imp hn ho h1 hI hI' hT hT' μ 1)
      (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT 1).2.2.2.1 (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N' n g' h0 hT' 1).2.2.2.1⟩

end Main

theorem match_parts : AllMatch fun μ g g' => μ.A ∧ g = g' := by
  intro C _ _ _ _ N N' q q' n g g' hn ho h1 hI hI' hT hT' μ
  refine ⟨⟨norm_eq hn ho h1 hI hI' hT hT' μ, fun j p p' h =>
    ⟨⟨inG_imp hn ho h1 hI hI' hT hT' μ j p p' h, inG_imp hn ho h1 hI' hI hT' hT (flip μ) j p' p h⟩,
     ⟨inT_imp hn ho h1 hI hI' hT hT' μ j p p' h, inT_imp hn ho h1 hI' hI hT' hT (flip μ) j p' p h⟩⟩⟩, ?_⟩
  have a := ranks_le hn ho h1 hI hI' hT hT' μ
  have b := ranks_le hn ho h1 hI' hI hT' hT (flip μ)
  omega

end GlobalTheory.MatchParts
