import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem uIdeal_sup_comap_bar_and_mul_le : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)), w ≠ ⊤ → uIdeal D r ≤ w → uIdeal D r ⊔ Ideal.comap D.bar (uIdeal D r) = ⊤ ∧ uIdeal D r * Ideal.comap D.bar (uIdeal D r) ≤ Ideal.span {(p : 𝓞 D.F)} := by
  intro p _ D r w hw hu
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have hbb : ∀ a, D.bar (D.bar a) = a := fun a => by
    apply Subtype.ext
    have h1 := D.bar_eq (D.bar a)
    rw [D.bar_eq a] at h1
    exact h1.trans (by simp; rfl)
  set u := uIdeal D r with hu_def
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hα : D.ω - (r : 𝓞 D.F) ∈ u := sub_mem_uIdeal D r
  have hpu : (p : 𝓞 D.F) ∈ u := p_mem_uIdeal D r
  have hn0 : (D.ω - r) * (D.bar D.ω - r) = ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) := by
    push_cast
    linear_combination hnm - (r : 𝓞 D.F) * htr
  have hdvd : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hnd
    obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 hnd
    apply hw
    rw [Ideal.eq_top_iff_one]
    have h1 : ((x * p + y * (r ^ 2 - D.tr * r + D.nm) : ℤ) : 𝓞 D.F) ∈ u := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, ← hn0]
      exact u.add_mem (u.mul_mem_left _ hpu) (u.mul_mem_left _ (u.mul_mem_right _ hα))
    rw [hxy, Int.cast_one] at h1
    exact hu h1
  obtain ⟨k0, hk0⟩ := hdvd
  have hvb : D.bar D.ω - (r : 𝓞 D.F) ∈ Ideal.comap D.bar u := by
    rw [Ideal.mem_comap, map_sub, map_intCast, hbb]; exact hα
  constructor
  · rw [Ideal.eq_top_iff_one]
    have ht : ¬ (p : ℤ) ∣ D.tr - 2 * r := by
      intro h
      apply D.disc_p
      have h2 := (dvd_pow h two_ne_zero).sub (dvd_mul_of_dvd_right (⟨k0, hk0⟩ : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm) 4)
      have e2 : D.tr ^ 2 - 4 * D.nm = (D.tr - 2 * r) ^ 2 - 4 * (r ^ 2 - D.tr * r + D.nm) := by ring
      rw [e2]
      exact h2
    obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 ht
    have h1 : ((x * p + y * (D.tr - 2 * r) : ℤ) : 𝓞 D.F) ∈ u ⊔ Ideal.comap D.bar u := by
      have e1 : ((x * p + y * (D.tr - 2 * r) : ℤ) : 𝓞 D.F) =
          (x : 𝓞 D.F) * p + ((y : 𝓞 D.F) * (D.ω - r) + (y : 𝓞 D.F) * (D.bar D.ω - r)) := by
        push_cast
        linear_combination (-(y : 𝓞 D.F)) * htr
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hpu))
        (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hα))
          (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right hvb)))
    rwa [hxy, Int.cast_one] at h1
  · rw [Ideal.mul_le]
    intro a ha b hb
    obtain ⟨a1, a2, rfl⟩ := Ideal.mem_span_pair.1 ha
    rw [Ideal.mem_comap] at hb
    obtain ⟨b1, b2, hb12⟩ := Ideal.mem_span_pair.1 hb
    have hb' : b = D.bar b1 * p + D.bar b2 * (D.bar D.ω - r) := by
      have := congrArg D.bar hb12
      rw [hbb, map_add, map_mul, map_mul, map_natCast, map_sub, map_intCast] at this
      exact this.symm
    subst hb'
    have h0 := hn0
    rw [hk0] at h0
    push_cast at h0
    rw [Ideal.mem_span_singleton']
    refine ⟨a1 * (D.bar b1 * p + D.bar b2 * (D.bar D.ω - r)) + a2 * D.bar b1 * (D.ω - r) + a2 * D.bar b2 * (k0 : 𝓞 D.F), ?_⟩
    linear_combination (-(a2 * D.bar b2)) * h0

theorem mem_addSubgroup_of_double_orthogonal : ∀ (M : Type) [AddCommGroup M] [Finite M] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (e : M → M → kˣ), (∀ x x' y, e (x + x') y = e x y * e x' y) → (∀ x y y', e x (y + y') = e x y * e x y') → (∀ x, (∀ y, e x y = 1) → x = 0) → ∀ (K : AddSubgroup M) (z : M), (∀ y, (∀ x ∈ K, e y x = 1) → e y z = 1) → z ∈ K := by
  intro M _ _ k _ _ _ e eadd1 eadd2 endeg K z hz
  by_contra hzK
  have e0r : ∀ x, e x 0 = 1 := fun x => by
    have h := eadd2 x 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  let Φ : M → (Multiplicative M →* kˣ) := fun y =>
    { toFun := fun x => e y (Multiplicative.toAdd x)
      map_one' := e0r y
      map_mul' := fun a b => eadd2 _ _ _ }
  have hΦ : Function.Injective Φ := by
    intro y y' h
    have : y - y' = 0 := endeg _ fun x => by
      have h1 : e y x = e y' x := DFunLike.congr_fun h (Multiplicative.ofAdd x)
      have h2 := eadd1 (y - y') y' x
      rw [sub_add_cancel, h1] at h2
      exact right_eq_mul.mp h2
    exact sub_eq_zero.1 this
  have : NeZero (Monoid.exponent (Multiplicative M) : k) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have h₁ : Nat.card (Multiplicative M →* kˣ) = Nat.card (Multiplicative M) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ _
  have : Finite (Multiplicative M →* kˣ) := Nat.finite_of_card_ne_zero (by rw [h₁]; exact Nat.card_pos.ne')
  have hsurj : Function.Surjective Φ := (hΦ.bijective_of_nat_card_le (by rw [h₁]; rfl)).2
  have : NeZero (Monoid.exponent (Multiplicative (M ⧸ K)) : k) :=
    ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have hz0 : Multiplicative.ofAdd (z : M ⧸ K) ≠ 1 := by
    rw [Ne, ofAdd_eq_one, QuotientAddGroup.eq_zero_iff]
    exact hzK
  obtain ⟨χ0, hχ0⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative (M ⧸ K)) k hz0
  let χ : Multiplicative M →* kˣ := χ0.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' K))
  obtain ⟨y, hy⟩ := hsurj χ
  have hχ : ∀ x, e y x = χ0 (Multiplicative.ofAdd (x : M ⧸ K)) := fun x =>
    DFunLike.congr_fun hy (Multiplicative.ofAdd x)
  refine hχ0 ?_
  rw [← hχ]
  refine hz y fun x hx => ?_
  rw [hχ, (QuotientAddGroup.eq_zero_iff x).2 hx, ofAdd_zero, map_one]

theorem exists_submodule_killed_card_eq_pow : ∀ (R : Type) [CommRing R] (w : Ideal R), w.IsMaximal → 0 < Nat.card (R ⧸ w) → ∀ (M : Type) [AddCommGroup M] [Module R M] [Finite M] (j : ℕ), Nat.card (R ⧸ w) ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} → ∃ K : Submodule R M, (∀ x ∈ K, ∀ a ∈ w, a • x = 0) ∧ Nat.card K = Nat.card (R ⧸ w) ^ j := by
  intro R _ w hw hpos M _ _ _ j hj
  haveI := hw
  letI : Field (R ⧸ w) := Ideal.Quotient.field w
  set T := Submodule.torsionBySet R M (w : Set R) with hT
  have hTm : ∀ x : M, x ∈ T ↔ ∀ a ∈ w, a • x = 0 := fun x => by
    rw [Submodule.mem_torsionBySet_iff]
    exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.2⟩
  have hcT : Nat.card {x : M // ∀ a ∈ w, a • x = 0} = Nat.card T :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hTm x).symm)
  haveI : Finite (R ⧸ w) := Nat.finite_of_card_ne_zero hpos.ne'
  haveI : Module.Finite (R ⧸ w) T := Module.Finite.of_finite
  have hd := Module.natCard_eq_pow_finrank (K := R ⧸ w) (V := T)
  have hq : 1 < Nat.card (R ⧸ w) := Finite.one_lt_card
  have hjd : j ≤ Module.finrank (R ⧸ w) T :=
    (Nat.pow_le_pow_iff_right hq).1 (by rw [← hd, ← hcT]; exact hj)
  let b := Module.finBasis (R ⧸ w) T
  let f : Fin j → T := fun i => b (Fin.castLE hjd i)
  have hf : LinearIndependent (R ⧸ w) f := b.linearIndependent.comp _ (Fin.castLE_injective hjd)
  let S : Submodule (R ⧸ w) T := Submodule.span (R ⧸ w) (Set.range f)
  have hS : Module.finrank (R ⧸ w) S = j := by rw [finrank_span_eq_card hf, Fintype.card_fin]
  have hcS : Nat.card S = Nat.card (R ⧸ w) ^ j := by
    rw [Module.natCard_eq_pow_finrank (K := R ⧸ w) (V := S), hS]
  refine ⟨(S.restrictScalars R).map T.subtype, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 hx
    exact (hTm _).1 y.2
  · rw [← hcS, ← Nat.card_congr (Submodule.equivMapOfInjective _ (Submodule.injective_subtype T) (S.restrictScalars R)).toEquiv]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem exists_maximal_isotropic_of_type : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e) → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.F) M] [Finite M], (∀ x : M, c • x = 0) → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (e : M → M → kˣ), (∀ x x' y, e (x + x') y = e x y * e x' y) → (∀ x y y', e x (y + y') = e x y * e x y') → (∀ (a : 𝓞 D.F) x y, e (a • x) y = e x (D.bar a • y)) → (∀ x y, e x y * e y x = 1) → (∀ x, (∀ y, e x y = 1) → x = 0) → Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} → ∃ H : Submodule (𝓞 D.F) M, (∀ x ∈ H, ∀ y ∈ H, e x y = 1) ∧ (∀ x, (∀ y ∈ H, e x y = 1) → x ∈ H) ∧ (∀ x ∈ H, (∃ i : ℕ, ∀ a ∈ uIdeal D r ^ i, a • x = 0) → ∀ a ∈ w, a • x = 0) ∧ Nat.card {x : M // x ∈ H ∧ ∀ a ∈ w, a • x = 0} = Ideal.absNorm w ^ j := by
  intro p _ D r w j c hw hu ⟨E0, hc⟩ M _ _ _ hM k _ _ _ e eadd1 eadd2 eadj eskew endeg hcard
  have e0r : ∀ x, e x 0 = 1 := fun x => by
    have h := eadd2 x 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have einv : ∀ x y, e y x = (e x y)⁻¹ := fun x y => eq_inv_of_mul_eq_one_right (eskew x y)
  have hbb : ∀ a, D.bar (D.bar a) = a := fun a => by
    apply Subtype.ext
    have h1 := D.bar_eq (D.bar a)
    rw [D.bar_eq a] at h1
    exact h1.trans (by simp; rfl)
  set u := uIdeal D r with hu_def
  set v := Ideal.comap D.bar u with hv_def
  set E := E0 + 1 with hE
  obtain ⟨hcop, hprod⟩ := uIdeal_sup_comap_bar_and_mul_le p D r w hw.ne_top hu
  have hpE : ∀ x : M, ((p : 𝓞 D.F) ^ E) • x = 0 := by
    intro x
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hE, pow_succ', mul_smul, ← hc, hM x, smul_zero]
  have hprodE : ∀ a ∈ u ^ E, ∀ b ∈ v ^ E, ∀ x : M, (a * b) • x = 0 := by
    intro a ha b hb x
    have h1 : a * b ∈ (u * v) ^ E := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    have h2 := Ideal.pow_right_mono hprod E h1
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
    obtain ⟨d, hd⟩ := h2
    rw [← hd, mul_smul, hpE, smul_zero]
  have hcopE : ∀ i, ∃ a ∈ u ^ i, ∃ b ∈ v ^ E, a + b = 1 := fun i =>
    Ideal.isCoprime_iff_exists.mp ((Ideal.isCoprime_iff_sup_eq.mpr hcop).pow)
  obtain ⟨ε', hε'u, ε, hεv, hsum⟩ := hcopE E
  have barv : ∀ a ∈ v ^ E, D.bar a ∈ u ^ E := fun a ha => Ideal.le_comap_pow _ E ha
  have baru : ∀ a ∈ u ^ E, D.bar a ∈ v ^ E := by
    intro a ha
    have h1 : Ideal.map D.bar u ≤ v := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      show D.bar (D.bar x) ∈ u
      rw [hbb]; exact hx
    have h2 : D.bar a ∈ Ideal.map D.bar (u ^ E) := Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 E h2
  have hsplit : ∀ x : M, ε • x + ε' • x = x := fun x => by rw [← add_smul, add_comm, hsum, one_smul]
  have hεε' : ∀ x : M, ε • ε' • x = 0 := fun x => by rw [← mul_smul, mul_comm]; exact hprodE _ hε'u _ hεv x
  have hε'ε : ∀ x : M, ε' • ε • x = 0 := fun x => by rw [← mul_smul]; exact hprodE _ hε'u _ hεv x
  have isoε : ∀ a b : M, e (ε • a) (ε • b) = 1 := fun a b => by
    rw [eadj, ← mul_smul]
    rw [hprodE _ (barv _ hεv) _ hεv b, e0r]
  have isoε' : ∀ a b : M, e (ε' • a) (ε' • b) = 1 := fun a b => by
    rw [eadj, ← mul_smul, mul_comm]
    rw [hprodE _ hε'u _ (baru _ hε'u) b, e0r]
  have hN : Ideal.absNorm w = Nat.card (𝓞 D.F ⧸ w) := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hwp : (p : 𝓞 D.F) ∈ w := hu (p_mem_uIdeal D r)
  have hNpos : 0 < Nat.card (𝓞 D.F ⧸ w) := by
    rw [← hN, Nat.pos_iff_ne_zero]
    intro h0
    rw [Ideal.absNorm_eq_zero_iff.1 h0, Ideal.mem_bot] at hwp
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hwp
  rw [hN] at hcard
  obtain ⟨K, hKw, hKc⟩ := exists_submodule_killed_card_eq_pow (𝓞 D.F) w hw hNpos M j hcard
  have hε'K : ∀ x ∈ K, ε' • x = 0 := fun x hx =>
    hKw x hx ε' (hu (Ideal.pow_le_self (by omega) hε'u))
  have hεK : ∀ x ∈ K, ε • x = x := fun x hx => by
    have := hsplit x
    rwa [hε'K x hx, add_zero] at this
  let K' : Submodule (𝓞 D.F) M :=
    { carrier := {y | ε • y = 0 ∧ ∀ x ∈ K, e x y = 1}
      add_mem' := fun {y y'} hy hy' => ⟨by rw [smul_add, hy.1, hy'.1, add_zero],
        fun x hx => by rw [eadd2, hy.2 x hx, hy'.2 x hx, _root_.mul_one]⟩
      zero_mem' := ⟨smul_zero _, fun x _ => e0r x⟩
      smul_mem' := fun a y hy => ⟨by rw [← mul_smul, mul_comm, mul_smul, hy.1, smul_zero],
        fun x hx => by
          have h := eadj (D.bar.symm a) x y
          rw [RingEquiv.apply_symm_apply] at h
          rw [← h]
          exact hy.2 _ (K.smul_mem _ hx)⟩ }
  have memK' : ∀ y, y ∈ K' ↔ ε • y = 0 ∧ ∀ x ∈ K, e x y = 1 := fun y => Iff.rfl
  have hK'ε' : ∀ y ∈ K', ε' • y = y := fun y hy => by
    have := hsplit y
    rwa [hy.1, zero_add] at this

  have hε'mem : ∀ y : M, (∀ x ∈ K, e y x = 1) → ε' • y ∈ K' := by
    intro y hy
    refine ⟨hεε' y, fun x hx => ?_⟩
    have h1 : e x y = 1 := by rw [einv, hy x hx, inv_one]
    have h2 := h1
    rw [← hsplit y, eadd2] at h2
    have h3 : e x (ε • y) = 1 := by rw [← hεK x hx]; exact isoε x y
    rwa [h3, _root_.one_mul] at h2
  have hinK : ∀ x ∈ K ⊔ K', (∃ i : ℕ, ∀ a ∈ u ^ i, a • x = 0) → x ∈ K := by
    rintro x hx ⟨i, hi⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hz' : z = ε' • (y + z) := by rw [smul_add, hε'K y hy, zero_add, hK'ε' z hz]
    obtain ⟨a, ha, b, hb, hab⟩ := hcopE i
    have h1 : a • z = 0 := by
      rw [hz', ← mul_smul, mul_comm, mul_smul, hi a ha, smul_zero]
    have h2 : b • z = 0 := by
      rw [hz', ← mul_smul, mul_comm]
      exact hprodE _ hε'u _ hb _
    have h3 : z = 0 := by rw [← one_smul (𝓞 D.F) z, ← hab, add_smul, h1, h2, add_zero]
    rw [h3, add_zero]
    exact hy
  refine ⟨K ⊔ K', ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨k1, hk1, k1', hk1', rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨k2, hk2, k2', hk2', rfl⟩ := Submodule.mem_sup.1 hy
    have a1 : e k1 k2 = 1 := by rw [← hεK k1 hk1, ← hεK k2 hk2]; exact isoε _ _
    have a2 : e k1 k2' = 1 := hk2'.2 k1 hk1
    have a3 : e k1' k2 = 1 := by rw [einv, hk1'.2 k2 hk2, inv_one]
    have a4 : e k1' k2' = 1 := by rw [← hK'ε' k1' hk1', ← hK'ε' k2' hk2']; exact isoε' _ _
    rw [eadd1, eadd2, eadd2, a1, a2, a3, a4, _root_.mul_one, _root_.mul_one]
  · intro g hg
    have hg' : ε' • g ∈ K' := by
      refine hε'mem g fun x hx => hg x (Submodule.mem_sup_left hx)
    have hgK : ε • g ∈ K := by
      refine mem_addSubgroup_of_double_orthogonal M k e eadd1 eadd2 endeg K.toAddSubgroup (ε • g) fun y hy => ?_
      have hy' : ε' • y ∈ K' := hε'mem y hy
      have h1 : e g (ε' • y) = 1 := hg _ (Submodule.mem_sup_right hy')
      rw [← hsplit g, eadd1, isoε' g y, _root_.mul_one] at h1
      rw [← hsplit y, eadd1, isoε y g, _root_.one_mul, einv, h1, inv_one]
    rw [← hsplit g]
    exact Submodule.add_mem_sup hgK hg'
  · intro x hx hi
    exact hKw x (hinK x hx (hi.imp fun i h a ha => h a ha))
  · have e1 : {x : M // x ∈ K ⊔ K' ∧ ∀ a ∈ w, a • x = 0} ≃ K :=
      Equiv.subtypeEquivRight fun x => ⟨fun h => hinK x h.1 ⟨1, fun a ha => h.2 a (hu (by rwa [pow_one] at ha))⟩,
        fun h => ⟨Submodule.mem_sup_left h, hKw x h⟩⟩
    rw [Nat.card_congr e1, hKc, hN]

end GlobalTheory.UPel.HT.ES
