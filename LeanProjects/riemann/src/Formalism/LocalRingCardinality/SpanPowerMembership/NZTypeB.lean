import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeA

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder

variable {g : ℕ} [hg : Fact g.Prime]

theorem one_lt_pow_g {d : ℕ} (hd : 1 ≤ d) : 2 ≤ g ^ d := by
  calc 2 ≤ g := hg.out.two_le
    _ ≤ g ^ d := Nat.le_self_pow (by omega) g

theorem coprime_n (d : ℕ) (hd : 1 ≤ d) : Nat.Coprime (g ^ d - 1) g := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hg.out]
  intro h
  have h2 : g ∣ g ^ d := dvd_pow_self g (by omega)
  have h3 := Nat.dvd_sub h2 h
  have h4 : g ^ d - (g ^ d - 1) = 1 := by
    have := one_lt_pow_g (g := g) hd
    omega
  rw [h4] at h3
  exact hg.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem exists_gen (d : ℕ) (hd : 1 ≤ d) : ∃ u : (Fbar g)ˣ, orderOf u = g ^ d - 1 := by
  classical
  haveI : Fintype (GaloisField g d) := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := (GaloisField g d)ˣ)
  let φ : GaloisField g d →ₐ[ZMod g] Fbar g := IsAlgClosed.lift
  refine ⟨Units.map φ.toRingHom.toMonoidHom x, ?_⟩
  rw [orderOf_injective (Units.map φ.toRingHom.toMonoidHom) (Units.map_injective φ.toRingHom.injective) x,
    orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_eq_fintype_card, Fintype.card_units]
  congr 1
  first
    | exact GaloisField.card g d (by omega)
    | (rw [← Nat.card_eq_fintype_card]; exact GaloisField.card g d (by omega))
    | simpa [Nat.card_eq_fintype_card] using GaloisField.card g d (by omega)

variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)

include hd hu in
theorem pow_gd : u ^ (g ^ d) = u := by
  have := one_lt_pow_g (g := g) hd
  rw [show g ^ d = g ^ d - 1 + 1 by omega, pow_succ, ← hu, pow_orderOf_eq_one, one_mul]

include hd hu in
theorem pow_g_add (j : ℕ) : u ^ (g ^ (j + d)) = u ^ (g ^ j) := by
  rw [pow_add, mul_comm, pow_mul, pow_gd hd u hu]

include hd hu in

theorem dvd_of_pow_eq {i j a : ℕ} (hij : i ≤ j) (h : u ^ (g ^ i * a) = u ^ (g ^ j * a)) :
    g ^ d - 1 ∣ a * (g ^ (j - i) - 1) := by
  rw [pow_eq_pow_iff_modEq, hu] at h
  have hle : g ^ i * a ≤ g ^ j * a := Nat.mul_le_mul_right a (Nat.pow_le_pow_right hg.out.pos hij)
  have h1 : g ^ d - 1 ∣ g ^ j * a - g ^ i * a := (Nat.modEq_iff_dvd' hle).1 h
  have hp : 1 ≤ g ^ (j - i) := Nat.one_le_pow _ _ hg.out.pos
  have hgj : g ^ j = g ^ i * g ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
  have h2 : g ^ j * a - g ^ i * a = g ^ i * (a * (g ^ (j - i) - 1)) := by
    rw [hgj]
    have hle2 : a ≤ a * g ^ (j - i) := Nat.le_mul_of_pos_right a hp
    zify [hp, hle, hle2, hgj ▸ hle]
    ring
  rw [h2] at h1
  exact ((coprime_n d hd).pow_right i).dvd_mul_left.1 h1

include hd hu in
theorem orbit_inj {i j : ℕ} (hi : i < d) (hj : j < d) (h : u ^ (g ^ i) = u ^ (g ^ j)) : i = j := by
  rcases le_total i j with hij | hij
  · by_contra hne
    have hlt : i < j := lt_of_le_of_ne hij hne
    have hdv := dvd_of_pow_eq hd u hu (a := 1) hij (by simpa using h)
    rw [one_mul] at hdv
    have h1 : 1 < g ^ (j - i) := Nat.one_lt_pow (by omega) hg.out.one_lt
    have h2 : g ^ (j - i) < g ^ d := Nat.pow_lt_pow_right hg.out.one_lt (by omega)
    have := Nat.le_of_dvd (by omega) hdv
    omega
  · by_contra hne
    have hlt : j < i := lt_of_le_of_ne hij (Ne.symm hne)
    have hdv := dvd_of_pow_eq hd u hu (a := 1) hij (by simpa using h.symm)
    rw [one_mul] at hdv
    have h1 : 1 < g ^ (i - j) := Nat.one_lt_pow (by omega) hg.out.one_lt
    have h2 : g ^ (i - j) < g ^ d := Nat.pow_lt_pow_right hg.out.one_lt (by omega)
    have := Nat.le_of_dvd (by omega) hdv
    omega

def orbQ (d : ℕ) (u : (Fbar g)ˣ) : (Fbar g)[X] := ∏ i ∈ Finset.range d, (X - C ((u : Fbar g) ^ (g ^ i)))

theorem orbQ_monic : (orbQ d u).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _

theorem orbQ_natDegree : (orbQ d u).natDegree = d := by
  rw [orbQ, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

include hd hu in
theorem orbQ_frob : (orbQ d u).map (frobenius (Fbar g) g) = orbQ d u := by
  have hf : ∀ i, (X - C ((u : Fbar g) ^ g ^ i)).map (frobenius (Fbar g) g) =
      X - C ((u : Fbar g) ^ g ^ (i + 1)) := fun i => by
    simp only [Polynomial.map_sub, map_X, map_C, frobenius_def, ← pow_mul, pow_succ]
  have hd' : (u : Fbar g) ^ g ^ d = u := by
    have := congrArg Units.val (pow_gd hd u hu)
    simpa using this
  unfold orbQ
  rw [Polynomial.map_prod]
  simp_rw [hf]
  apply mul_right_cancel₀ (X_sub_C_ne_zero ((u : Fbar g) ^ g ^ 0))
  rw [← Finset.prod_range_succ' (fun i => X - C ((u : Fbar g) ^ g ^ i)), Finset.prod_range_succ, hd',
    pow_zero, pow_one]

include hd hu in
theorem exists_orbP : ∃ P : (ZMod g)[X], P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u ∧
    P.natDegree = d ∧ P.Monic := by
  have frob_fixed : ∀ y : Fbar g, y ^ g = y → y ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := by
    intro y hy
    classical
    by_contra hy'
    have hf0 : (X ^ g - X : (Fbar g)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hg.out.one_lt
    have hsub : insert y (Finset.univ.image (algebraMap (ZMod g) (Fbar g))) ⊆
        (X ^ g - X : (Fbar g)[X]).roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hy
      · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hz
        rw [← map_pow, ZMod.pow_card]
    have hny : y ∉ Finset.univ.image (algebraMap (ZMod g) (Fbar g)) := fun h => by
      obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h
      exact hy' ⟨c, hc⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hny, Finset.card_image_of_injective _ (algebraMap (ZMod g) (Fbar g)).injective,
      Finset.card_univ, ZMod.card] at hc
    have h2 := (Multiset.toFinset_card_le _).trans (card_roots' (X ^ g - X : (Fbar g)[X]))
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hg.out.one_lt] at h2
    omega
  have hc : ∀ n, (orbQ d u).coeff n ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := fun n => by
    have h := congrArg (fun p => p.coeff n) (orbQ_frob hd u hu)
    simp only [coeff_map, frobenius_def] at h
    exact frob_fixed _ h
  have hl : orbQ d u ∈ Polynomial.lifts (algebraMap (ZMod g) (Fbar g)) := (lifts_iff_coeff_lifts _).2 hc
  obtain ⟨P, hPmap, hPdeg, hPmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (orbQ_monic u)
  exact ⟨P, hPmap, hPdeg.trans (orbQ_natDegree u), hPmonic⟩

theorem mem_roots_orbQ {y : Fbar g} : y ∈ (orbQ d u).roots ↔ ∃ i < d, y = (u : Fbar g) ^ (g ^ i) := by
  have h0 := (orbQ_monic (d := d) u).ne_zero
  unfold orbQ at h0 ⊢
  rw [roots_prod _ _ h0]
  simp only [roots_X_sub_C, Multiset.mem_bind, Finset.mem_val, Finset.mem_range, Multiset.mem_singleton]

variable {P : (ZMod g)[X]} (hP : P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u)

include hP in
theorem mem_rootsBar_P {y : Fbar g} : y ∈ rootsBar P ↔ ∃ i < d, y = (u : Fbar g) ^ (g ^ i) := by
  rw [rootsBar, hP]
  exact mem_roots_orbQ u

include hd hu hP in

theorem le_natDegree_of_dvd {q : (ZMod g)[X]} (hq : q ∣ P) (hq0 : q.natDegree ≠ 0) : d ≤ q.natDegree := by
  classical
  have hq0' : q ≠ 0 := by
    rintro rfl
    simp at hq0
  have hqm : q.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := Polynomial.map_ne_zero hq0'
  have hPm : P.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := by
    rw [hP]; exact (orbQ_monic u).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (q.map (algebraMap (ZMod g) (Fbar g))) (by
    rw [degree_map]
    intro h
    exact hq0 (natDegree_eq_of_degree_eq_some h))
  have hyP : y ∈ rootsBar P := by
    rw [rootsBar, mem_roots hPm]
    exact hy.dvd (Polynomial.map_dvd _ hq)
  obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P u hP).1 hyP
  have hcomp : (frobenius (Fbar g) g).comp (algebraMap (ZMod g) (Fbar g)) = algebraMap (ZMod g) (Fbar g) :=
    RingHom.ext fun c => by simp [frobenius_def, ← map_pow, ZMod.pow_card]
  have hfrob : ∀ z, (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot z →
      (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot (z ^ g) := by
    intro z hz
    simp only [IsRoot, eval_map] at hz ⊢
    have h := Polynomial.hom_eval₂ q (algebraMap (ZMod g) (Fbar g)) (frobenius (Fbar g) g) z
    rw [hcomp, hz, map_zero, frobenius_def] at h
    exact h.symm
  have hiter : ∀ k, (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot ((u : Fbar g) ^ g ^ (i + k)) := by
    intro k
    induction k with
    | zero => simpa using hy
    | succ k ih =>
      have h := hfrob _ ih
      rw [← pow_mul, ← pow_succ] at h
      exact h
  have hall : ∀ j < d, (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot ((u : Fbar g) ^ g ^ j) := by
    intro j hj
    have h1 := hiter (d - i + j)
    have h2 : i + (d - i + j) = j + d := by omega
    rw [h2] at h1
    have h3 := congrArg Units.val (pow_g_add hd u hu j)
    simp only [Units.val_pow_eq_pow_val] at h3
    rwa [h3] at h1
  have hsub : (Finset.range d).image (fun j => (u : Fbar g) ^ g ^ j) ⊆
      (q.map (algebraMap (ZMod g) (Fbar g))).roots.toFinset := fun z hz => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
    rw [Multiset.mem_toFinset, mem_roots hqm]
    exact hall j (Finset.mem_range.1 hj)
  have hinj : Set.InjOn (fun j => (u : Fbar g) ^ g ^ j) (Finset.range d) := fun a ha b hb hab =>
    orbit_inj hd u hu (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) (Units.ext (by simpa using hab))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hc
  calc d ≤ _ := hc
    _ ≤ Multiset.card (q.map (algebraMap (ZMod g) (Fbar g))).roots := Multiset.toFinset_card_le _
    _ ≤ (q.map (algebraMap (ZMod g) (Fbar g))).natDegree := card_roots' _
    _ = q.natDegree := natDegree_map _

include hd hu hP in
theorem irreducible_P (hPd : P.natDegree = d) : Irreducible P := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hPd
    omega
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit h
    omega
  · by_contra hne
    push_neg at hne
    have hab' : a * b ≠ 0 := hab ▸ hP0
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hab'
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab'
    have ha : a.natDegree ≠ 0 := fun h =>
      hne.1 (isUnit_iff_degree_eq_zero.2 ((degree_eq_iff_natDegree_eq ha0).2 h))
    have hb : b.natDegree ≠ 0 := fun h =>
      hne.2 (isUnit_iff_degree_eq_zero.2 ((degree_eq_iff_natDegree_eq hb0).2 h))
    have h1 := le_natDegree_of_dvd hd u hu hP (Dvd.intro b hab.symm) ha
    have h2 := le_natDegree_of_dvd hd u hu hP (Dvd.intro_left a hab.symm) hb
    have h3 : P.natDegree = a.natDegree + b.natDegree := by rw [hab, natDegree_mul ha0 hb0]
    omega

include hP in
theorem coeff_zero_P : P.coeff 0 ≠ 0 := by
  intro h0
  have hPm : P.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := by
    rw [hP]; exact (orbQ_monic u).ne_zero
  have h0r : (0 : Fbar g) ∈ rootsBar P := by
    rw [rootsBar, mem_roots hPm, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
  obtain ⟨i, -, hi⟩ := (mem_rootsBar_P u hP).1 h0r
  exact pow_ne_zero _ u.ne_zero hi.symm

end Formalism.BasicNotions.Examples₂.NZ
