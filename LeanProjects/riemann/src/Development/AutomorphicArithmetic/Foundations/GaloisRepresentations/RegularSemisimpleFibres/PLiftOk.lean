import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Gal.InertialTypesAlt.coprime_pow_sub_one_self {q m : ℕ} (hm : 0 < m) (hq : 2 ≤ q) : Nat.Coprime (q ^ m - 1) q := by
  have hpos : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
  have e : q ^ m - 1 + 1 = q ^ m := by omega
  have a := Nat.gcd_dvd_left (q ^ m - 1) q
  have b := Nat.gcd_dvd_right (q ^ m - 1) q
  have c : Nat.gcd (q ^ m - 1) q ∣ q ^ m - 1 + 1 := by
    rw [e]
    exact b.trans (dvd_pow_self q hm.ne')
  exact Nat.dvd_one.1 ((Nat.dvd_add_right a).1 c)

private theorem UpperTheory.Gal.InertialTypesAlt.reg_dvd {q l m k : ℕ} (i : ℕ) (hq : 2 ≤ q) (hl : 0 < l) (hm : 0 < m) (hd : l ∣ m)
    (h : GlobalTheory.Shin.Reg q m k) : GlobalTheory.Shin.Reg (q ^ l) (m / l) (k * q ^ i) := by
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left c hl]
  intro j hj hjc hmod
  have hcop : Nat.gcd (q ^ (l * c) - 1) (q ^ i) = 1 :=
    Nat.Coprime.pow_right i (UpperTheory.Gal.InertialTypesAlt.coprime_pow_sub_one_self hm hq)
  refine h (l * j) (Nat.mul_pos hl hj) (Nat.mul_lt_mul_of_pos_left hjc hl) ?_
  rw [← pow_mul] at hmod
  apply Nat.ModEq.cancel_right_of_coprime hcop
  have e : k * q ^ (l * j) * q ^ i = k * q ^ i * (q ^ l) ^ j := by
    rw [← pow_mul]; ring
  rw [e]
  exact hmod

private theorem UpperTheory.Gal.InertialTypesAlt.reg_ndvd {q l m k : ℕ} (hq : 2 ≤ q) (hl : l.Prime) (hm : 0 < m) (hd : ¬ l ∣ m)
    (h : GlobalTheory.Shin.Reg q m k) : GlobalTheory.Shin.Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) := by
  intro j hj hjm hmod
  have hpos : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
  have hgt : 1 < q ^ m := Nat.one_lt_pow hm.ne' (by omega)
  have hx : q ^ m - 1 + 1 = q ^ m := by omega
  have hgeo := geom_sum_mul_add (q ^ m - 1) l
  rw [hx] at hgeo
  have hS : (∑ i ∈ Finset.range l, q ^ (m * i)) = ∑ i ∈ Finset.range l, (q ^ m) ^ i :=
    Finset.sum_congr rfl fun i _ => pow_mul q m i
  rw [← hS] at hgeo
  set S := ∑ i ∈ Finset.range l, q ^ (m * i) with hSdef
  have hbig : 1 < (q ^ m) ^ l := Nat.one_lt_pow hl.ne_zero hgt
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0] at hgeo
    omega
  have hmodulus : (q ^ l) ^ m - 1 = (q ^ m - 1) * S := by
    have : (q ^ l) ^ m = (q ^ m) ^ l := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [this, ← hgeo, Nat.mul_comm]
    simp
  rw [hmodulus] at hmod
  have e1 : k * (q ^ l) ^ j ≡ k [MOD q ^ m - 1] := by
    apply Nat.ModEq.mul_right_cancel' hS0
    have e : k * (q ^ l) ^ j * S = k * S * (q ^ l) ^ j := by ring
    rw [e]
    exact hmod
  have hone : q ^ m ≡ 1 [MOD q ^ m - 1] := by
    have : (q ^ m - 1) + 1 ≡ 0 + 1 [MOD q ^ m - 1] :=
      Nat.ModEq.add_right 1 (by simp [Nat.ModEq])
    rwa [hx] at this
  have hcop : Nat.Coprime m l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm
  have hr0 : (l * j) % m ≠ 0 := by
    intro h0
    have h1 : m ∣ l * j := Nat.dvd_of_mod_eq_zero h0
    have h2 : m ∣ j := hcop.dvd_of_dvd_mul_left h1
    have := Nat.le_of_dvd hj h2
    omega
  have hrm : (l * j) % m < m := Nat.mod_lt _ hm
  have hpow : q ^ (l * j) ≡ q ^ ((l * j) % m) [MOD q ^ m - 1] := by
    have hsplit : q ^ (l * j) = (q ^ m) ^ ((l * j) / m) * q ^ ((l * j) % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hsplit]
    have := (hone.pow ((l * j) / m)).mul_right (q ^ ((l * j) % m))
    simpa using this
  refine h _ (Nat.pos_of_ne_zero hr0) hrm ?_
  have e2 : k * q ^ ((l * j) % m) ≡ k * q ^ (l * j) [MOD q ^ m - 1] := (hpow.mul_left k).symm
  refine e2.trans ?_
  rw [pow_mul]
  exact e1

private theorem UpperTheory.Gal.InertialTypesAlt.deg_append (A B : List (ℕ × ℕ)) :
    GlobalTheory.Shin.deg (A ++ B) = GlobalTheory.Shin.deg A + GlobalTheory.Shin.deg B := by
  simp [GlobalTheory.Shin.deg]

private theorem UpperTheory.Gal.InertialTypesAlt.block_dvd (q l : ℕ) (p : ℕ × ℕ) (hd : l ∣ p.1) :
    GlobalTheory.Shin.deg (GlobalTheory.Shin.liftL q l [p]) = p.1 := by
  have h : ((List.range l).map fun i => (p.1 / l, p.2 * q ^ i)).map Prod.fst = List.replicate l (p.1 / l) := by
    rw [List.map_map]
    apply List.eq_replicate_iff.2
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    rfl
  have h2 : GlobalTheory.Shin.deg (GlobalTheory.Shin.liftL q l [p]) = (List.replicate l (p.1 / l)).sum := by
    rw [← h]
    simp [GlobalTheory.Shin.deg, GlobalTheory.Shin.liftL]
  rw [h2, List.sum_replicate, smul_eq_mul]
  exact Nat.mul_div_cancel' hd

private theorem UpperTheory.Gal.InertialTypesAlt.liftAll_spec (q l : ℕ) (L : List (ℕ × ℕ)) (hq : 2 ≤ q) (hl : l.Prime)
    (h : ∀ p ∈ L, 0 < p.1 ∧ GlobalTheory.Shin.Reg q p.1 p.2) :
    GlobalTheory.Shin.deg (GlobalTheory.Shin.liftAll q l L) = GlobalTheory.Shin.deg L ∧
      ∀ p ∈ GlobalTheory.Shin.liftAll q l L, 0 < p.1 ∧ GlobalTheory.Shin.Reg (q ^ l) p.1 p.2 := by
  induction L with
  | nil => simp [GlobalTheory.Shin.liftAll, GlobalTheory.Shin.deg]
  | cons p L ih =>
    obtain ⟨ih1, ih2⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨hp0, hpR⟩ := h p List.mem_cons_self
    have hsplit : GlobalTheory.Shin.liftAll q l (p :: L) =
        (if l ∣ p.1 then GlobalTheory.Shin.liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]) ++
          GlobalTheory.Shin.liftAll q l L := by
      simp only [GlobalTheory.Shin.liftAll, List.flatMap_cons]
    have hdegp : GlobalTheory.Shin.deg (p :: L) = p.1 + GlobalTheory.Shin.deg L := by simp [GlobalTheory.Shin.deg]
    rw [hsplit, UpperTheory.Gal.InertialTypesAlt.deg_append, ih1, hdegp]
    by_cases hd : l ∣ p.1
    · rw [if_pos hd]
      refine ⟨by rw [UpperTheory.Gal.InertialTypesAlt.block_dvd q l p hd], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · simp only [GlobalTheory.Shin.liftL, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        exact ⟨Nat.div_pos (Nat.le_of_dvd hp0 hd) hl.pos, UpperTheory.Gal.InertialTypesAlt.reg_dvd i hq hl.pos hp0 hd hpR⟩
      · exact ih2 x hx
    · rw [if_neg hd]
      refine ⟨by simp [GlobalTheory.Shin.deg], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hp0, UpperTheory.Gal.InertialTypesAlt.reg_ndvd hq hl hp0 hd hpR⟩
      · exact ih2 x hx

theorem UpperTheory.Gal.InertialTypesAlt.liftOk :
    LiftOk := by
  intro a l hl hok
  obtain ⟨hq, hD, hL⟩ := hok
  obtain ⟨h1, h2⟩ := UpperTheory.Gal.InertialTypesAlt.liftAll_spec a.q l a.L hq hl hL
  have hD' : GlobalTheory.Shin.deg (a.D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range l, a.q ^ i)) = GlobalTheory.Shin.deg a.D := by
    simp [GlobalTheory.Shin.deg, List.map_map, Function.comp_def]
  refine ⟨⟨?_, ?_, h2⟩, ?_⟩
  · show 2 ≤ a.q ^ l
    calc 2 ≤ a.q := hq
      _ ≤ a.q ^ l := Nat.le_self_pow hl.ne_zero a.q
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
    exact hD r hr
  · show GlobalTheory.Shin.deg (a.D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range l, a.q ^ i)) + GlobalTheory.Shin.deg (GlobalTheory.Shin.liftAll a.q l a.L) =
      GlobalTheory.Shin.deg a.D + GlobalTheory.Shin.deg a.L
    rw [hD', h1]
