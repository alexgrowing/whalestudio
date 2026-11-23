import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma geo_mul (x l : ℕ) (hx : 1 ≤ x) :
    (∑ i ∈ Finset.range l, x ^ i) * (x - 1) = x ^ l - 1 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have := geom_sum_mul_add y l
  simp only [Nat.add_sub_cancel]
  omega

private lemma div_id (N a b S : ℕ) (ha : 0 < a) (hS : S * a = b) (hb : b ∣ N) (hb0 : 0 < b) :
    S * (N / b) = N / a := by
  obtain ⟨c, rfl⟩ := hb
  rw [Nat.mul_div_cancel_left c hb0]
  subst hS
  rw [show S * a * c = a * (S * c) by ring, Nat.mul_div_cancel_left _ ha]

private lemma sub_one_dvd (x e : ℕ) : x - 1 ∣ x ^ e - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow x 1 e

private lemma ms_sum {α : Type*} (n : ℕ) (g : ℕ → α) :
    (Multiset.range n).map g = ∑ j ∈ Finset.range n, ({g j} : Multiset α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ih, add_comm,
      Multiset.singleton_add]

private lemma list_sum {α : Type*} (l : ℕ) (F : ℕ → Multiset α) :
    ((List.range l).map F).sum = ∑ i ∈ Finset.range l, F i := by
  induction l with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private lemma block_mul {α : Type*} (l m' : ℕ) (g : ℕ → α) :
    ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m', ({g (i + l * j)} : Multiset α) =
      ∑ n ∈ Finset.range (l * m'), ({g n} : Multiset α) := by
  induction m' with
  | zero => simp
  | succ m ih =>
    calc ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range (m + 1), ({g (i + l * j)} : Multiset α)
        = ∑ i ∈ Finset.range l, (∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            {g (i + l * m)}) := Finset.sum_congr rfl fun i _ => Finset.sum_range_succ _ m
      _ = ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            ∑ i ∈ Finset.range l, ({g (i + l * m)} : Multiset α) := Finset.sum_add_distrib
      _ = ∑ n ∈ Finset.range (l * (m + 1)), ({g n} : Multiset α) := by
          rw [ih, Nat.mul_succ, Finset.sum_range_add]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]

private lemma perm_map {α : Type*} (l m : ℕ) (hc : Nat.Coprime l m) (hm : 0 < m) (G : ℕ → α)
    (hG : ∀ n, G (n + m) = G n) :
    (Multiset.range m).map (fun j => G (l * j)) = (Multiset.range m).map G := by
  have hper : Function.Periodic G m := hG
  have hinj : Set.InjOn (fun j => l * j % m) (Finset.range m : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < m := by simpa using hx
    have hy' : y < m := by simpa using hy
    have h1 : l * x ≡ l * y [MOD m] := hxy
    have h2 : x ≡ y [MOD m] := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hx' hy'
  have himg : (Finset.range m).image (fun j => l * j % m) = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hm)
    · rw [Finset.card_image_of_injOn hinj]
  rw [ms_sum, ms_sum]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun j _ => by rw [hper.map_mod_nat]

private def lbk (Q q : ℕ) (p : ℕ × ℕ) : Multiset (ℕ × ZMod (Q - 1)) :=
  (Multiset.range p.1).map fun j =>
    ((1 : ℕ), ((p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))

private lemma lbk_dvd (Q q l m' k : ℕ) :
    ((List.range l).map fun i => lbk Q (q ^ l) (m', k * q ^ i)).sum = lbk Q q (l * m', k) := by
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j =>
    ((1 : ℕ), ((k * q ^ j * ((Q - 1) / (q ^ (l * m') - 1)) : ℕ) : ZMod (Q - 1))) with hGdef
  have h1 : ∀ i, lbk Q (q ^ l) (m', k * q ^ i) =
      ∑ j ∈ Finset.range m', ({G (i + l * j)} : Multiset _) := by
    intro i
    rw [← ms_sum (n := m') (g := fun j => G (i + l * j))]
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef, ← pow_mul, pow_add, mul_assoc]
  have h2 : lbk Q q (l * m', k) = (Multiset.range (l * m')).map G := rfl
  rw [list_sum, h2, ms_sum, ← block_mul]
  exact Finset.sum_congr rfl fun i _ => h1 i

private lemma lbk_ndvd (Q q l f m k : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f)
    (hm : 0 < m) (hmf : m ∣ f) (hnd : ¬ l ∣ m) :
    lbk Q (q ^ l) (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) = lbk Q q (m, k) := by
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' (by omega)
  have hql : 1 < (q ^ l) ^ m := Nat.one_lt_pow hm.ne' (Nat.one_lt_pow hl.ne_zero (by omega))
  have hT : (∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ m - 1) = (q ^ l) ^ m - 1 := by
    have := geo_mul (q ^ m) l hqm.le
    simp only [← pow_mul] at this ⊢
    rw [this, Nat.mul_comm l m]
  have hd1 : (q ^ l) ^ m - 1 ∣ Q - 1 := by
    obtain ⟨e, rfl⟩ := hmf
    rw [hQ, pow_mul]
    exact sub_one_dvd _ e
  have hd2 : q ^ m - 1 ∣ Q - 1 := (Dvd.intro_left _ hT).trans hd1
  have hC := div_id (Q - 1) (q ^ m - 1) ((q ^ l) ^ m - 1) _ (by omega) hT hd1 (by omega)
  have hC2 : (Q - 1) / (q ^ m - 1) * (q ^ m - 1) = Q - 1 := Nat.div_mul_cancel hd2
  set C := (Q - 1) / (q ^ m - 1) with hCdef
  set T := ∑ i ∈ Finset.range l, q ^ (m * i) with hTdef
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j => ((1 : ℕ), ((k * q ^ j * C : ℕ) : ZMod (Q - 1))) with hGdef
  have hG : ∀ n, G (n + m) = G n := by
    intro n
    obtain ⟨u, hu⟩ : ∃ u, q ^ m = u + 1 := ⟨q ^ m - 1, by omega⟩
    have hCu : C * u = Q - 1 := by rw [hu] at hC2; simpa using hC2
    have : k * q ^ (n + m) * C = k * q ^ n * C + k * q ^ n * (Q - 1) := by
      rw [pow_add, hu, ← hCu]; ring
    simp only [hGdef, this]
    push_cast [ZMod.natCast_self]
    simp [ZMod.natCast_self]
  have hL : lbk Q (q ^ l) (m, k * T) = (Multiset.range m).map fun j => G (l * j) := by
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef]
    rw [← hC, pow_mul]
    congr 2
    ring
  rw [hL, perm_map l m ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd) hm G hG]
  rfl

private lemma lbkL (Q q l f : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1) → (∀ p ∈ liftAll q l L, p.1 ∣ f) →
      ((liftAll q l L).map (lbk Q (q ^ l))).sum = (L.map (lbk Q q)).sum := by
  intro L
  induction L with
  | nil => intro _ _; simp [liftAll]
  | cons p L ih =>
    intro h0 hd
    obtain ⟨m, k⟩ := p
    have hsplit : liftAll q l ((m, k) :: L) = (if l ∣ m then liftL q l [(m, k)] else
        [(m, k * ∑ i ∈ Finset.range l, q ^ (m * i))]) ++ liftAll q l L := by
      simp [liftAll]
    rw [hsplit] at hd ⊢
    have hdL : ∀ p ∈ liftAll q l L, p.1 ∣ f := fun p hp => hd p (List.mem_append_right _ hp)
    rw [List.map_append, List.sum_append, ih (fun p hp => h0 p (List.mem_cons_of_mem _ hp)) hdL,
      List.map_cons, List.sum_cons]
    congr 1
    by_cases hlm : l ∣ m
    · obtain ⟨m', rfl⟩ := hlm
      have : liftL q l [(l * m', k)] = (List.range l).map fun i => (m', k * q ^ i) := by
        simp [liftL, Nat.mul_div_cancel_left _ hl.pos]
      rw [if_pos (dvd_mul_right _ _), this, List.map_map]
      exact lbk_dvd Q q l m' k
    · rw [if_neg hlm] at hd ⊢
      have hmf : m ∣ f := hd (m, _) (List.mem_append_left _ (List.mem_singleton.2 rfl))
      simpa using lbk_ndvd Q q l f m k hq hl hQ (h0 (m, k) List.mem_cons_self) hmf hlm

private lemma splitsL (q l f : ℕ) (hl : l.Prime) (L : List (ℕ × ℕ))
    (hd : ∀ p ∈ liftAll q l L, p.1 ∣ f) : ∀ p ∈ L, p.1 ∣ l * f := by
  rintro ⟨m, k⟩ hp
  by_cases hlm : l ∣ m
  · have h1 : (m / l, k * q ^ 0) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp only [if_pos hlm, liftL]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.mem_map.2 ⟨0, List.mem_range.2 hl.pos, rfl⟩
    have h2 := hd _ h1
    obtain ⟨m', rfl⟩ := hlm
    rw [Nat.mul_div_cancel_left _ hl.pos] at h2
    exact Nat.mul_dvd_mul_left l h2
  · have h1 : (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp [if_neg hlm]
    exact (hd _ h1).mul_left l

theorem UpperTheory.Gal.InertialTypesAlt.liftBlocks :
    LiftBlocks := by
  intro a l Q hl ha hs
  obtain ⟨q, D, L⟩ := a
  obtain ⟨hq, hD, hL⟩ := ha
  obtain ⟨f, hf, hQ, hdiv⟩ := hs
  have hq' : 2 ≤ q := hq
  have hQ' : Q = (q ^ l) ^ f := hQ
  have hdiv' : ∀ p ∈ liftAll q l L, p.1 ∣ f := hdiv
  have hL0 : ∀ p ∈ L, 0 < p.1 := fun p hp => (hL p hp).1
  refine ⟨⟨l * f, Nat.mul_pos hl.pos hf, by rw [hQ', pow_mul], splitsL q l f hl L hdiv'⟩, ?_⟩
  have hS := geo_mul q l (by omega)
  have hql : 1 < q ^ l := Nat.one_lt_pow hl.ne_zero (by omega)
  have hDid : (∑ i ∈ Finset.range l, q ^ i) * ((Q - 1) / (q ^ l - 1)) = (Q - 1) / (q - 1) :=
    div_id (Q - 1) (q - 1) (q ^ l - 1) _ (by omega) hS (by rw [hQ']; exact sub_one_dvd _ f) (by omega)
  have hDpart : ((⟨q, D, L⟩ : Lbl).lift l).D.map (fun p =>
        (p.1, ((p.2 * ((Q - 1) / (((⟨q, D, L⟩ : Lbl).lift l).q - 1)) : ℕ) : ZMod (Q - 1)))) =
      D.map (fun p => (p.1, ((p.2 * ((Q - 1) / (q - 1)) : ℕ) : ZMod (Q - 1)))) := by
    show (D.map _).map _ = _
    rw [List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp]
    rw [← hDid, mul_assoc]
    rfl
  have hLpart := lbkL Q q l f hq' hl hQ' L hL0 hdiv'
  unfold Lbl.blocks
  rw [hDpart]
  congr 1
