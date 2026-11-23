import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem pow_two_pow (y b : ℤ) (t : ℕ) (ht : 2 ≤ t) (hb : Odd b) (hy : y = 1 + 2 ^ t * b) (j : ℕ) :
    ∃ b' : ℤ, Odd b' ∧ y ^ 2 ^ j = 1 + 2 ^ (t + j) * b' := by
  induction j with
  | zero => exact ⟨b, hb, by simpa using hy⟩
  | succ j ih =>
    obtain ⟨b', hb', h⟩ := ih
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    refine ⟨b' + 2 * (2 ^ (s + j) * b' ^ 2), hb'.add_even (even_two_mul _), ?_⟩
    rw [pow_succ 2 j, pow_mul, h]
    ring

private theorem exists_pow_modEq (y b z : ℤ) (t : ℕ) (ht : 2 ≤ t) (hb : Odd b) (hy : y = 1 + 2 ^ t * b)
    (hz : (2 : ℤ) ^ t ∣ z - 1) (j : ℕ) : ∃ n : ℕ, (2 : ℤ) ^ (t + j) ∣ y ^ n - z := by
  induction j with
  | zero => exact ⟨0, by simpa using dvd_sub_comm.1 hz⟩
  | succ j ih =>
    obtain ⟨n, d, hd⟩ := ih
    obtain ⟨b', ⟨b₁, rfl⟩, h⟩ := pow_two_pow y b t ht hb hy j
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    obtain ⟨w, hw⟩ := hz
    rcases Int.even_or_odd' d with ⟨d₁, rfl | rfl⟩
    · exact ⟨n, d₁, by rw [hd]; ring⟩
    · refine ⟨n + 2 ^ j, d₁ + b₁ + 1 + 2 ^ (s + 1) * w * (2 * b₁ + 1) + 2 ^ (s + j + 1) * (2 * d₁ + 1) * (2 * b₁ + 1), ?_⟩
      rw [pow_add, h, eq_add_of_sub_eq hd, eq_add_of_sub_eq hw]
      ring

private theorem cond_dvd_iff {O : Type} [CommRing O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) {M : ℕ} (h : M ∣ N) :
    ψ.conductor ∣ M ↔ ∀ u, ZMod.unitsMap h u = 1 → ψ.toUnitHom u = 1 := by
  rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ h, DirichletCharacter.mem_conductorSet_iff,
    DirichletCharacter.factorsThrough_iff_ker_unitsMap h]
  rfl

private theorem pow_hom {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) (u : (ZMod N)ˣ) :
    (χ ^ k).toUnitHom u = χ.toUnitHom u ^ k := by
  ext
  simp [MulChar.pow_apply_coe]

private theorem dyadic_character_power_ne_one {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (p o : ℕ)
    (hp : Odd p) (hp1 : 1 < p) (ho : 1 ≤ o) (hR : 8 * o * p ^ 2 < 2 ^ c2 ψ) (u : (ZMod N)ˣ)
    (hu : ((ZMod.unitsMap (Nat.ordProj_dvd N 2) u : (ZMod (ordProj[2] N))ˣ) : ZMod (ordProj[2] N)) = p) :
    (psi2 ψ).toUnitHom u ^ (4 * o) ≠ 1 := by
  intro h
  obtain ⟨-, -, -, hc, hcN, -⟩ := compCond O N ψ 2 Nat.prime_two
  obtain ⟨k, hk⟩ := (compOrd O N ψ 2 Nat.prime_two).2.1
  obtain ⟨j, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (n := o) (by omega)
  have hp2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp1
  obtain ⟨s, b, hb, hsb⟩ := Nat.exists_eq_two_pow_mul_odd (n := p ^ 2 - 1) (by omega)
  have hs : 2 ≤ s := by
    obtain ⟨r, rfl⟩ := hp
    have h4 : 2 ^ 2 ∣ 2 ^ s * b := hsb ▸ ⟨r ^ 2 + r, by
      have : (2 * r + 1) ^ 2 = 2 ^ 2 * (r ^ 2 + r) + 1 := by ring
      omega⟩
    exact (Nat.pow_dvd_pow_iff_le_right one_lt_two).1
      ((Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hb)).dvd_of_dvd_mul_right h4)
  have hy : ((p : ℤ) ^ 2) = 1 + 2 ^ s * (b : ℤ) := by
    have : p ^ 2 = 1 + 2 ^ s * b := by omega
    exact_mod_cast this
  obtain ⟨b', hb', hy'⟩ := pow_two_pow _ _ s hs (by exact_mod_cast hb) hy (j + 1)
  have hlt : s + (j + 1) < c2 ψ := by
    refine (Nat.pow_lt_pow_iff_right one_lt_two).1 (lt_of_le_of_lt ?_ hR)
    have h1 : 2 ^ s ≤ p ^ 2 := le_trans (Nat.le_mul_of_pos_right _ hb.pos) (by omega)
    have h2 : 2 ^ j ≤ o := hom ▸ Nat.le_mul_of_pos_right _ hm.pos
    calc 2 ^ (s + (j + 1)) = 2 * 2 ^ j * 2 ^ s := by ring
      _ ≤ 8 * o * p ^ 2 := by gcongr; norm_num
  have h1 : (psi2 ψ).toUnitHom (u ^ (2 * 2 ^ (j + 1))) = 1 := by
    have e1 : (psi2 ψ).toUnitHom (u ^ (2 * 2 ^ (j + 1))) ^ m = 1 := by
      rw [← h, map_pow, ← pow_mul, hom]; congr 1; ring
    have e2 : (psi2 ψ).toUnitHom (u ^ (2 * 2 ^ (j + 1))) ^ 2 ^ k = 1 := by
      rw [← pow_hom, ← hk, psi2, pow_orderOf_eq_one]; ext; simp
    exact (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm))).1 ⟨e2, e1⟩
  have hd : 2 ^ (s + (j + 1)) ∣ N := (pow_dvd_pow 2 hlt.le).trans hcN
  have hle : s + (j + 1) ≤ N.factorization 2 := (Nat.prime_two.pow_dvd_iff_le_factorization (NeZero.ne N)).1 hd
  obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le hle
  have hcd : (psi2 ψ).conductor ∣ 2 ^ (s + (j + 1)) := by
    refine (cond_dvd_iff _ hd).2 fun w hw => ?_
    have hz : (2 : ℤ) ^ (s + (j + 1)) ∣ (((w : ZMod N).val : ℕ) : ℤ) - 1 := by
      have e := congrArg Units.val hw
      rw [ZMod.unitsMap_val, ← ZMod.natCast_val, Units.val_one] at e
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((((w : ZMod N).val : ℕ) : ℤ) - 1) (2 ^ (s + (j + 1)))).1 (by
        push_cast; rw [e, sub_self])
      exact_mod_cast this
    obtain ⟨n, hn⟩ := exists_pow_modEq _ b' _ _ (by omega) hb' hy' hz i
    rw [← hi] at hn
    have e : ZMod.unitsMap (Nat.ordProj_dvd N 2) ((u ^ (2 * 2 ^ (j + 1))) ^ n) = ZMod.unitsMap (Nat.ordProj_dvd N 2) w := by
      ext
      rw [map_pow, map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu, ZMod.unitsMap_val, ← ZMod.natCast_val]
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ N.factorization 2)).2 (dvd_trans (by simp) hn)
      rw [Int.cast_sub, sub_eq_zero, Int.cast_natCast] at this
      rw [← this, pow_mul]
      push_cast
      rfl
    have e' : proj 2 N ((u ^ (2 * 2 ^ (j + 1))) ^ n) = proj 2 N w := by
      rw [← MonoidHom.div_mem_ker_iff, (projFacts N 2 Nat.prime_two).2.2.2.2.2.2.1, MonoidHom.div_mem_ker_iff, e]
    have hA := (compAlg O N 2 Nat.prime_two).1 ψ
    rw [psi2, hA, ← e', ← hA, map_pow]
    rw [psi2] at h1
    rw [h1, one_pow]
  rw [← hc] at hcd
  exact absurd ((Nat.pow_dvd_pow_iff_le_right one_lt_two).1 hcd) (by omega)

private theorem teichmuller_power_eq {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N] {l e o : ℕ} (hl : l.Prime)
    {ψ : DirichletCharacter O N} (H : HostData l e ψ o) (hψ : 0 < orderOf ψ) : th0 l ψ ^ (4 * o) = psi2 ψ ^ (4 * o) := by
  obtain ⟨-, hmul, hone, -, hpow, -, hprod, -⟩ := compAlg O N 2 Nat.prime_two
  have hk : comp 2 (kap l ψ) = 1 := by
    obtain ⟨k, hk⟩ := (compOrd O N (kap l ψ) 2 Nat.prime_two).2.1
    have e1 : comp 2 (kap l ψ) ^ 2 ^ k = 1 := hk ▸ pow_orderOf_eq_one _
    have e2 : comp 2 (kap l ψ) ^ l ^ (orderOf ψ).factorization l = 1 := by
      rw [← hpow, ← (partOrd _ l hl ψ hψ).1, kap, pow_orderOf_eq_one, hone]
    exact (pow_eq_one_iff_of_coprime (Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hl).2 H.l_odd.symm))).1 ⟨e1, e2⟩
  have h2 : psi2 ψ = comp 2 (th0 l ψ) := by
    rw [psi2]
    conv_lhs => rw [← dirichletPrimeToLPart_mul_lPowerPart l ψ, hmul, hk, mul_one]
  rw [h2]
  conv_lhs => rw [← hprod (th0 l ψ), ← Finset.prod_pow]
  refine Finset.prod_eq_single_of_mem 2 ?_ fun r hr h => ?_
  · exact Nat.mem_primeFactors.2 ⟨Nat.prime_two, H.N_even.two_dvd, NeZero.ne N⟩
  · rw [show 4 * o = 2 * o * 2 by ring, pow_mul, H.ord r (Nat.prime_of_mem_primeFactors hr) h, one_pow]

private theorem eq_one_of_congr {O : Type} [CommRing O] [IsLocalRing O] {x : O} {n : ℕ} (hn : IsUnit (n : O)) (hx : x ^ n = 1)
    (h : residue O x = 1) : x = 1 := by
  have hu : IsUnit (∑ i ∈ Finset.range n, x ^ i) := by
    rw [← residue_ne_zero_iff_isUnit] at hn ⊢
    simpa [h] using hn
  have := geom_sum_mul x n
  rw [hx, sub_self] at this
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)

private theorem res_ne {l : ℕ} [hl : Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] {e o : ℕ} {ψ : DirichletCharacter c.O N}
    (H : HostData l e ψ o) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpT : p ∈ UpperTheory.V.HV.Tb l ψ) (u : (ZMod N)ˣ)
    (hu : ((ZMod.unitsMap (Nat.ordProj_dvd N 2) u : (ZMod (ordProj[2] N))ˣ) : ZMod (ordProj[2] N)) = p) :
    residue c.O (ψ.toUnitHom u : c.Oˣ) ^ 4 ≠ 1 := by
  intro h
  have hψ : 0 < orderOf ψ := orderOf_pos ψ
  obtain ⟨hk, -, hth, -⟩ := partOrd _ l hl.out ψ hψ
  set s := (orderOf ψ).factorization l
  have e0 : ψ ^ l ^ s = th0 l ψ ^ l ^ s := by
    conv_lhs => rw [← dirichletPrimeToLPart_mul_lPowerPart l ψ, mul_pow, ← hk, kap, pow_orderOf_eq_one, mul_one]
    rw [hk]
  have en : (th0 l ψ).toUnitHom u ^ orderOf (lPrime l ψ) = 1 := by
    rw [← pow_hom, th0, pow_orderOf_eq_one]; ext; simp
  have e1 : ((th0 l ψ).toUnitHom u ^ 4) ^ l ^ s = 1 := by
    ext1
    refine eq_one_of_congr ((UpperTheory.V.Base.dvrFacts l c.O).2.2.2.2.2.2.2.2 _ hth) ?_ ?_
    · rw [← Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, mul_comm _ (orderOf _), mul_comm 4, mul_assoc, pow_mul, en, one_pow,
        Units.val_one]
    · rw [pow_right_comm, ← pow_hom, ← e0, pow_hom, pow_right_comm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        map_pow, map_pow, h, one_pow]
  have e2 : (th0 l ψ).toUnitHom u ^ 4 = 1 :=
    (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left s (hl.out.coprime_iff_not_dvd.2 hth))).1
      ⟨e1, by rw [pow_right_comm, en, one_pow]⟩
  refine dyadic_character_power_ne_one ψ p o (hp.odd_of_ne_two hp2) hp.one_lt H.o_pos (H.R p hpT) u hu ?_
  rw [← pow_hom, ← teichmuller_power_eq hl.out H hψ, pow_hom, pow_mul, e2, one_pow]

private theorem exists_dec (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (p : ℕ) (hp : p.Prime)
    (hpl : p = l ∨ (p ≠ l ∧ p ≡ 1 [MOD l])) (A : ValuationSubring Ω) (hA : A.valuation (p : Ω) < 1) :
    ∃ σ ∈ Dec (F := ℚ) A, (∀ m : ℕ, m.Coprime p → ∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ p) ∧
      PadicInt.toZModPow 1 (cycZ ℚ Ω l σ : ℤ_[l]) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨γ, hγ, hγ'⟩ := UpperTheory.V.LDataCardLeFinrank.decFrob Ω p A hA
  rcases hpl with rfl | ⟨h1, h2⟩
  · obtain ⟨τ, hτ, hτ'⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω p A hA (cycZ ℚ Ω p γ)⁻¹
    refine ⟨γ * τ, mul_mem hγ (Ine_le_Dec A hτ), fun m hm ζ hζ => ?_, ?_⟩
    · rw [AlgEquiv.mul_apply, (UpperTheory.V.LDataCardLeFinrank.ineFixRoots ℚ Ω p A hA m hm ζ hζ).2 τ hτ, hγ' m hm ζ hζ]
    · rw [map_mul, hτ', mul_inv_cancel, Units.val_one, map_one]
  · refine ⟨γ, hγ, hγ', ?_⟩
    have : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
    have : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
      have : NeZero (l ^ i) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
      have : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
      infer_instance
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
    have ha : γ ζ = ζ ^ (PadicInt.toZModPow 1 (cycZ ℚ Ω l γ : ℤ_[l])).val :=
      cyclotomicCharacter.spec l γ.toRingEquiv ζ hζ.pow_eq_one
    rw [hγ' _ (((Nat.coprime_primes hl.out hp).2 h1.symm).pow_left 1) ζ hζ.pow_eq_one,
      (hζ.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff,
      ZMod.natCast_zmod_val] at ha
    rw [← ha]
    exact ((ZMod.natCast_eq_natCast_iff p 1 (l ^ 1)).2 (by rwa [pow_one])).trans Nat.cast_one

private theorem res_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (hloc : IsLocalHom (algebraMap ℤ_[l] O)) (x : ℤ_[l]) (hx : PadicInt.toZModPow 1 x = 1) :
    residue O (algebraMap ℤ_[l] O x) = 1 := by
  have h5 : x - 1 ∈ maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hx,
      map_one, sub_self]
  have h6 := (residue_eq_zero_iff _).2 (_root_.map_nonunit (algebraMap ℤ_[l] O) _ h5)
  rwa [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h6

theorem UpperTheory.V.UnitaryThreeInertia.exists_sigma :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    ∀ v ∈ F.Tb, ∃ x : F.D v, F.ηv v x = 1 ∧ IsUnit ((F.Ψv v x : c.O) ^ 2 - 1) ∧ cycMod ℚ Ω l 1 x = 1 := by
  intro Ω _ _ _ l hl c N _ e ψ o H S A F hF v hv
  obtain ⟨p, hp, hp2, hpT, hpl, hpv⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ UpperTheory.V.HV.Tb l ψ ∧ (p = l ∨ (p ≠ l ∧ p ≡ 1 [MOD l])) ∧
      ((p : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.1.asIdeal := by
    rcases hv with rfl | hv
    · exact ⟨l, hl.out, H.l_odd, Finset.mem_insert_self _ _, Or.inl rfl, hF.vl⟩
    · obtain ⟨p, hp, hpv⟩ := (hF.Sb v).1 hv
      have hp' := hp
      simp only [UpperTheory.V.HV.Sb, Finset.mem_filter] at hp'
      obtain ⟨h1, h2, h3⟩ := hp'
      have hpp := Nat.prime_of_mem_primeFactors h1
      have h4 := ((compOrd c.O N (kap l ψ) p hpp).2.2.2 l ((orderOf ψ).factorization l) hl.out h2.symm
        (by rw [← (partOrd _ l hl.out ψ (orderOf_pos ψ)).1, kap, pow_orderOf_eq_one]) h3).1
      refine ⟨p, hpp, ?_, Finset.mem_insert_of_mem hp, Or.inr ⟨h2, h4⟩, hpv⟩
      rintro rfl
      exact hl.out.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_iff_dvd' one_le_two).1 h4.symm))
  have hA : (A v).valuation (p : Ω) < 1 := by simpa using (hF.isOver v _).2 hpv
  obtain ⟨σ, hσ, h1, h2⟩ := exists_dec Ω l p hp hpl (A v) hA
  have hx : σ ^ 2 ∈ F.D v := hF.D v ▸ pow_mem hσ 2
  refine ⟨⟨σ ^ 2, hx⟩, ?_, ?_, ?_⟩
  · show (F.η.comp F.π) (σ ^ 2) = 1
    rw [map_pow, Int.units_sq]
  · show IsUnit ((((F.Ψ.comp F.π) (σ ^ 2) : c.Oˣ) : c.O) ^ 2 - 1)
    have : NeZero (ordProj[2] N) := ⟨(Nat.ordProj_pos N 2).ne'⟩
    have hcop : (ordProj[2] N).Coprime p := ((Nat.coprime_primes Nat.prime_two hp).2 hp2.symm).pow_left _
    have hu : ZMod.unitsMap (Nat.ordProj_dvd N 2) (Chr.cls ℚ Ω N σ) = ZMod.unitOfCoprime p hcop.symm := by
      refine (DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 _ (Nat.ordProj_dvd N 2)) σ).trans ?_
      refine (Chr.clsFacts ℚ Ω _).2.2.1 σ _ fun ζ hζ => ?_
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ, h1 _ hcop ζ hζ]
    have h3 := res_ne c H p hp hp2 hpT (Chr.cls ℚ Ω N σ) (by rw [hu, ZMod.coe_unitOfCoprime])
    have h4 : residue c.O (UpperTheory.V.Base.chiO ℚ Ω l c.O σ : c.Oˣ) = 1 := by
      exact res_one l c.O (UpperTheory.V.Base.dvrFacts l c.O).2.2.1 _ h2
    rw [← residue_ne_zero_iff_isUnit, hF.Ψ, map_pow, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply]
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, map_sub, map_pow, map_mul, map_one, h4, one_pow, one_mul, ← pow_mul]
    exact sub_ne_zero.2 h3
  · show cycMod ℚ Ω l 1 (σ ^ 2) = 1
    have : cycMod ℚ Ω l 1 σ = 1 := Units.ext h2
    rw [map_pow, this, one_pow]
