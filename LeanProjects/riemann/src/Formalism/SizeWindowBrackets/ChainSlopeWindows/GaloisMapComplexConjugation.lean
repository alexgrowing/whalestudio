import Formalism.SizeWindowBrackets.GaloisToProductIsIso
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LHost

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

lemma cast_eq_natCast_iff {N : ℕ} [NeZero N] (x : ZMod N) (c k : ℕ) :
    (x.cast : ZMod c) = (k : ZMod c) ↔ x.val ≡ k [MOD c] := by
  rw [← ZMod.natCast_val, ZMod.natCast_eq_natCast_iff]

lemma cast_eq_one_iff {N : ℕ} [NeZero N] (x : ZMod N) (c : ℕ) :
    (x.cast : ZMod c) = 1 ↔ x.val ≡ 1 [MOD c] := by
  rw [← cast_eq_natCast_iff, Nat.cast_one]

lemma unitsMap_eq_one_iff {N c : ℕ} [NeZero N] (h : c ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h u = 1 ↔ (u : ZMod N).val ≡ 1 [MOD c] := by
  rw [Units.ext_iff, ZMod.unitsMap_val, Units.val_one, cast_eq_one_iff]

lemma unitsMap_eq_unitOfCoprime_iff {N c k : ℕ} [NeZero N] (h : c ∣ N) (hk : k.Coprime c) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h u = ZMod.unitOfCoprime k hk ↔ (u : ZMod N).val ≡ k [MOD c] := by
  rw [Units.ext_iff, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, cast_eq_natCast_iff]

lemma mem_localUnits_iff {N : ℕ} [NeZero N] (p : ℕ) (u : (ZMod N)ˣ) :
    u ∈ localUnits N p ↔ (u : ZMod N).val ≡ 1 [MOD ordCompl[p] N] := by
  unfold localUnits
  rw [MonoidHom.mem_ker, unitsMap_eq_one_iff]

lemma isFrobUnit_iff {N : ℕ} [NeZero N] (p : ℕ) (w : (ZMod N)ˣ) :
    IsFrobUnit N p w ↔ (w : ZMod N).val ≡ p [MOD ordCompl[p] N] ∧ (w : ZMod N).val ≡ 1 [MOD ordProj[p] N] := by
  unfold IsFrobUnit
  rw [cast_eq_natCast_iff, cast_eq_one_iff]

lemma units_ext_modEq {N : ℕ} [NeZero N] {u v : (ZMod N)ˣ} (h : (u : ZMod N).val ≡ (v : ZMod N).val [MOD N]) :
    u = v := by
  apply Units.ext
  have := (ZMod.natCast_eq_natCast_iff _ _ N).2 h
  simpa using this

lemma exists_unit_crt {N a b : ℕ} (hN : N = a * b) (hab : a.Coprime b) (ha : a ∣ N) (hb : b ∣ N)
    (x : (ZMod a)ˣ) (y : (ZMod b)ˣ) :
    ∃ u : (ZMod N)ˣ, ZMod.unitsMap ha u = x ∧ ZMod.unitsMap hb u = y := by
  subst hN
  let E := ZMod.chineseRemainder hab
  refine ⟨Units.map E.symm.toMonoidHom (MulEquiv.prodUnits.symm (x, y)), ?_, ?_⟩
  · apply Units.ext
    change ((E.symm ((x : ZMod a), (y : ZMod b))).cast : ZMod a) = x
    have h3 : ∀ z : ZMod (a * b), (E z).1 = (z.cast : ZMod a) := fun z => Prod.fst_zmod_cast z
    rw [← h3, E.apply_symm_apply]
  · apply Units.ext
    change ((E.symm ((x : ZMod a), (y : ZMod b))).cast : ZMod b) = y
    have h3 : ∀ z : ZMod (a * b), (E z).2 = (z.cast : ZMod b) := fun z => Prod.snd_zmod_cast z
    rw [← h3, E.apply_symm_apply]

theorem frobenius_unit_spec : FrobUnitSpec := by
  intro N p hN hp
  have : NeZero N := ⟨hN⟩
  have hcop : (ordProj[p] N).Coprime (ordCompl[p] N) := (Nat.coprime_ordCompl hp hN).pow_left _
  have hex : ∃ w, IsFrobUnit N p w := by
    obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (Nat.ordProj_mul_ordCompl_eq_self N p).symm hcop
      (Nat.ordProj_dvd N p) (Nat.ordCompl_dvd N p) 1 (ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp hN))
    refine ⟨u, (isFrobUnit_iff p u).2 ⟨?_, ?_⟩⟩
    · exact (unitsMap_eq_unitOfCoprime_iff _ _ u).1 hu2
    · exact (unitsMap_eq_one_iff _ u).1 hu1
  have hspec : IsFrobUnit N p (frobUnit N p) := by
    unfold frobUnit
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hspec, fun w hw => ?_⟩
  rw [isFrobUnit_iff] at hspec hw
  apply units_ext_modEq
  have h1 := hw.1.trans hspec.1.symm
  have h2 := hw.2.trans hspec.2.symm
  have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h2, h1⟩
  rwa [Nat.ordProj_mul_ordCompl_eq_self] at this

lemma frobUnit_modEq {N p : ℕ} [NeZero N] (hp : p.Prime) :
    ((frobUnit N p : (ZMod N)ˣ) : ZMod N).val ≡ p [MOD ordCompl[p] N] ∧
      ((frobUnit N p : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD ordProj[p] N] :=
  (isFrobUnit_iff p _).1 (frobenius_unit_spec N p (NeZero.ne N) hp).1

theorem unramified_spec : UnramSpec := by
  intro N p hN hp hpN
  have : NeZero N := ⟨hN⟩
  have hM : ordCompl[p] N = N := (Nat.ordCompl_eq_self_iff_zero_or_not_dvd N hp).2 (Or.inr hpN)
  constructor
  · rw [eq_bot_iff]
    intro u hu
    rw [mem_localUnits_iff, hM] at hu
    rw [Subgroup.mem_bot]
    apply units_ext_modEq
    refine hu.trans ?_
    have : ((1 : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD N] := by
      rw [← cast_eq_one_iff]; simp
    exact this.symm
  · have h := (frobUnit_modEq (N := N) hp).1
    rw [hM] at h
    have := (ZMod.natCast_eq_natCast_iff _ _ N).2 h
    simpa using this

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem dirichlet_character_spec : DirCharSpec H := by
  intro N r ψ
  refine ⟨fun u => ?_, fun x hx => MulChar.map_nonunit _ hx⟩
  unfold dirChar
  rw [MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
  rfl

lemma dirChar_unit {N : ℕ} (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (u : (ZMod N)ˣ) :
    dirChar r ψ (u : ZMod N) = ψ (Multiplicative.toAdd (r u)) := (dirichlet_character_spec N r ψ).1 u

lemma mem_inertia_iff {N : ℕ} (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (p : ℕ) (x : E0 × H) :
    x ∈ (cftData q1 d r).inertia p ↔ ∃ u ∈ localUnits N p, Multiplicative.toAdd (r u) = x := by
  change Multiplicative.ofAdd x ∈ (localUnits N p).map r ↔ _
  rw [Subgroup.mem_map]
  rfl

lemma trivial_on_inertia_iff {N : ℕ} [NeZero N] (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H))
    (ψ : AddChar (E0 × H) ℂ) (p : ℕ) :
    (∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) ↔ (dirChar r ψ).conductor ∣ ordCompl[p] N := by
  rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ (Nat.ordCompl_dvd N p),
    DirichletCharacter.mem_conductorSet_iff,
    DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)]
  constructor
  · intro h u hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one]
    exact h _ ((mem_inertia_iff q1 d r p _).2 ⟨u, hu, rfl⟩)
  · intro h x hx
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff q1 d r p _).1 hx
    have := h hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one] at this
    exact this

theorem inertia_conductor : InertiaConductor H := by
  intro N q1 d r ψ p hN hp
  have : NeZero N := ⟨hN⟩
  rw [trivial_on_inertia_iff]
  constructor
  · intro h hpc
    exact Nat.not_dvd_ordCompl hp hN (hpc.trans h)
  · intro h
    exact Nat.dvd_ordCompl_of_dvd_not_dvd (DirichletCharacter.conductor_dvd_level _) h

lemma cosetMean_of_trivial (I : AddSubgroup (E0 × H)) (h : E0 × H) (ψ : AddChar (E0 × H) ℂ)
    (hI : ∀ x ∈ I, ψ x = 1) : cosetMean I h ψ = ψ h := by
  classical
  unfold cosetMean
  have h0 : ((univ.filter (fun x => x ∈ I)).card : ℂ) ≠ 0 := by
    have : (0 : E0 × H) ∈ univ.filter (fun x => x ∈ I) := by simp [I.zero_mem]
    exact_mod_cast (Finset.card_pos.2 ⟨_, this⟩).ne'
  rw [div_eq_iff h0, Finset.sum_congr rfl (g := fun _ => ψ h)]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · intro x hx
    rw [AddChar.map_add_eq_mul, hI x (by simpa using hx), mul_one]

lemma cosetMean_of_nontrivial (I : AddSubgroup (E0 × H)) (h : E0 × H) (ψ : AddChar (E0 × H) ℂ)
    (hI : ¬ ∀ x ∈ I, ψ x = 1) : cosetMean I h ψ = 0 := by
  classical
  unfold cosetMean
  push Not at hI
  obtain ⟨y, hy, hy1⟩ := hI
  have key : ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x) = 0 := by
    have h1 : ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x)
        = ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + (y + x)) := by
      symm
      apply Finset.sum_bij (fun x _ => y + x)
      · intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact I.add_mem hy hx
      · intro a _ b _ hab
        exact add_left_cancel hab
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb
        exact ⟨-y + b, by simpa using I.add_mem (I.neg_mem hy) hb, by simp⟩
      · intro x _
        rfl
    have h2 : ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + (y + x))
        = ψ y * ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      ring
    rw [h2] at h1
    have h3 : (1 - ψ y) * ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4).symm hy1
    · exact h4
  rw [key, zero_div]

theorem primitive_value_ramified : PrimValRamified H := by
  intro N q1 d r ψ p i hp hi
  rw [primitive_value_pow (cftData q1 d r) ψ p i hp hi]
  refine ⟨fun h => ?_, fun h => cosetMean_of_nontrivial _ _ _ h⟩
  rw [cosetMean_of_trivial _ _ _ h, AddChar.map_nsmul_eq_pow]

lemma cosetMean_eq_primitive {N : ℕ} [NeZero N] (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H))
    (ψ : AddChar (E0 × H) ℂ) (p i : ℕ) (hp : p.Prime) (hi : i ≠ 0) :
    cosetMean ((cftData q1 d r).inertia p) (i • (cftData q1 d r).frob p) ψ
      = (dirChar r ψ).primitiveCharacter (p : ZMod (dirChar r ψ).conductor) ^ i := by
  by_cases h : ∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1
  · rw [cosetMean_of_trivial _ _ _ h, AddChar.map_nsmul_eq_pow]
    congr 1
    have hc : (dirChar r ψ).conductor ∣ ordCompl[p] N := (trivial_on_inertia_iff q1 d r ψ p).1 h
    change ψ (Multiplicative.toAdd (r (frobUnit N p))) = _
    rw [← dirChar_unit]
    conv_lhs => rw [← DirichletCharacter.changeLevel_primitiveCharacter (dirChar r ψ)]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    congr 1
    rw [cast_eq_natCast_iff]
    exact (frobUnit_modEq hp).1.of_dvd hc
  · rw [cosetMean_of_nontrivial _ _ _ h]
    have hpc : p ∣ (dirChar r ψ).conductor := by
      by_contra hpc
      exact h ((inertia_conductor N q1 d r ψ p (NeZero.ne N) hp).2 hpc)
    rw [MulChar.map_nonunit, zero_pow hi]
    rw [ZMod.isUnit_iff_coprime]
    intro hcop
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpc)

theorem primitive_value_primitive : PrimValPrimitive H := by
  intro N q1 d r ψ n hN hn
  have : NeZero N := ⟨hN⟩
  unfold primVal
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod, map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hi : n.factorization p ≠ 0 := by
    have := (Nat.support_factorization n ▸ hp : p ∈ n.factorization.support)
    exact Finsupp.mem_support_iff.1 this
  rw [cosetMean_eq_primitive q1 d r ψ p _ hpp hi, Nat.cast_pow, map_pow]

end

open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)

lemma hostN_ne_zero (e : ℕ) {q d : ℕ} (h : HostHyp q d) : hostN e q d ≠ 0 :=
  Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) h.1.ne_zero) h.2.1.ne_zero

lemma parts_of_eq {N p k m : ℕ} (hp : p.Prime) (hN : N = p ^ k * m) (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    ordProj[p] N = p ^ k ∧ ordCompl[p] N = m := by
  subst hN
  have h2 := Nat.ordCompl_pow_mul_of_not_dvd k hp hm
  have h1 := Nat.ordProj_mul_ordCompl_eq_self (p ^ k * m) p
  rw [h2] at h1
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm0) h1, h2⟩

lemma HostHyp_ne {q d : ℕ} (h : HostHyp q d) : q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d := by
  obtain ⟨_, _, h3, h4, _⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem extension_local_parts : HostLocalParts := by
  intro e q d h
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have hq := h.1
  have hd := h.2.1
  have h2q : ¬ 2 ∣ q := fun hh => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hh).symm
  have h2d : ¬ 2 ∣ d := fun hh => hd2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).1 hh).symm
  have hq2' : ¬ q ∣ 2 ^ (e + 2) := fun hh =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hh))
  have hd2' : ¬ d ∣ 2 ^ (e + 2) := fun hh =>
    hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).1 (hd.dvd_of_dvd_pow hh))
  have hqd' : ¬ q ∣ d := fun hh => hqd ((Nat.prime_dvd_prime_iff_eq hq hd).1 hh)
  have hdq' : ¬ d ∣ q := fun hh => hqd ((Nat.prime_dvd_prime_iff_eq hd hq).1 hh).symm
  have hp0 : (2 : ℕ) ^ (e + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · exact parts_of_eq Nat.prime_two (by unfold hostN; ring)
      (fun hh => (Nat.prime_two.dvd_mul.1 hh).elim h2q h2d) (Nat.mul_ne_zero hq.ne_zero hd.ne_zero)
  · have := parts_of_eq (N := hostN e q d) (k := 1) (m := 2 ^ (e + 2) * d) hq (by unfold hostN; ring)
      (fun hh => (hq.dvd_mul.1 hh).elim hq2' hqd') (Nat.mul_ne_zero hp0 hd.ne_zero)
    rwa [pow_one] at this
  · have := parts_of_eq (N := hostN e q d) (k := 1) (m := 2 ^ (e + 2) * q) hd (by unfold hostN; ring)
      (fun hh => (hd.dvd_mul.1 hh).elim hd2' hdq') (Nat.mul_ne_zero hp0 hq.ne_zero)
    rwa [pow_one] at this

lemma jac_two_d {q d : ℕ} (h : HostHyp q d) : jacobiSym ((2 : ℕ) : ℤ) d = 1 := by
  have h8 : d % 8 = 7 := by have := h.2.2.2.1; omega
  have hodd : Odd d := Nat.odd_iff.2 (by omega)
  rw [Nat.cast_ofNat, jacobiSym.at_two hodd, ZMod.χ₈_nat_mod_eight, h8]
  rfl

lemma jac_two_q {q d : ℕ} (h : HostHyp q d) : jacobiSym ((2 : ℕ) : ℤ) q = -1 := by
  have h8 : q % 8 = 3 := h.2.2.1
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  rw [Nat.cast_ofNat, jacobiSym.at_two hodd, ZMod.χ₈_nat_mod_eight, h8]
  rfl

lemma jac_q_d {q d : ℕ} (h : HostHyp q d) : jacobiSym (q : ℤ) d = 1 := by
  have h4 : d % 4 = 3 := by have := h.2.2.2.1; omega
  have hodd : Odd d := Nat.odd_iff.2 (by omega)
  have h1 := FrobeniusOrbits.hostRecip q d h
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four h4] at h1
  linarith

lemma jac_d_q {q d : ℕ} (h : HostHyp q d) : jacobiSym (d : ℤ) q = -1 := by
  have h4 : q % 4 = 3 := by have := h.2.2.1; omega
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  have h1 := h.2.2.2.2
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four h4] at h1
  linarith

lemma jac_flip {l m : ℕ} (hl : l % 4 = 3) (hm : Odd m) : jacobiSym (m : ℤ) l = jacobiSym (-(l : ℤ)) m := by
  rw [jacobiSym.neg _ hm]
  have hl' : Odd l := Nat.odd_iff.2 (by omega)
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hm) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hl']
  · rw [ZMod.χ₄_nat_three_mod_four h3, jacobiSym.quadratic_reciprocity_three_mod_four h3 hl]
    ring

lemma sgn2_toAdd_eq_ite (s : ℤˣ) : Multiplicative.toAdd (sgn2 s) = if (s : ℤ) = 1 then 0 else 1 := by
  change (if s = 1 then (0 : ZMod 2) else 1) = _
  have : s = 1 ↔ (s : ℤ) = 1 := by rw [Units.ext_iff, Units.val_one]
  simp only [this]

lemma legU_of_modEq {N l : ℕ} [NeZero N] [Fact l.Prime] (h : l ∣ N) (u : (ZMod N)ˣ) (k : ℕ)
    (hk : (u : ZMod N).val ≡ k [MOD l]) : ((legU N l h u : ℤˣ) : ℤ) = jacobiSym (k : ℤ) l := by
  unfold legU
  rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom, ZMod.unitsMap_val, (cast_eq_natCast_iff _ _ _).2 hk,
    ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast]

lemma recMap_of_modEq {e q d : ℕ} [Fact q.Prime] [Fact d.Prime] [NeZero (hostN e q d)] (u : (ZMod (hostN e q d))ˣ)
    (kd kq k2 : ℕ) (hk2 : k2.Coprime (2 ^ (e + 2)))
    (h1 : (u : ZMod (hostN e q d)).val ≡ kd [MOD d]) (h2 : (u : ZMod (hostN e q d)).val ≡ kq [MOD q])
    (h3 : (u : ZMod (hostN e q d)).val ≡ k2 [MOD 2 ^ (e + 2)]) :
    Multiplicative.toAdd (recMap e q d u)
      = ((if jacobiSym (kd : ℤ) d = 1 then 0 else 1, if jacobiSym (kq : ℤ) q = 1 then 0 else 1),
        Additive.ofMul (hcl e (ZMod.unitOfCoprime k2 hk2))) := by
  change ((Multiplicative.toAdd (sgn2 (legU _ d (d_dvd_hostN e q d) u)),
      Multiplicative.toAdd (sgn2 (legU _ q (q_dvd_hostN e q d) u))),
      Additive.ofMul (hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) = _
  rw [sgn2_toAdd_eq_ite, sgn2_toAdd_eq_ite, legU_of_modEq _ u kd h1, legU_of_modEq _ u kq h2,
    (unitsMap_eq_unitOfCoprime_iff _ hk2 u).2 h3]

lemma unitOfCoprime_modEq {N m c : ℕ} [NeZero N] (hm : m.Coprime N) (hc : c ∣ N) :
    ((ZMod.unitOfCoprime m hm : (ZMod N)ˣ) : ZMod N).val ≡ m [MOD c] := by
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  exact (Nat.mod_modEq m N).of_dvd hc

lemma ite_zmod2 (J : ℤ) (hJ : J = 1 ∨ J = -1) :
    (((if J = 1 then (0 : ZMod 2) else 1) = 0 ↔ J = 1) ∧ ((if J = 1 then (0 : ZMod 2) else 1) = 1 ↔ J = -1)) := by
  rcases hJ with rfl | rfl
  · simp
  · simp

theorem reciprocity_kronecker : RecKronecker := by
  intro e q d _ _ h m hm hm2
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hodd : Odd m := by
    have : m.Coprime 2 := Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 (by omega)) hm2
    exact Nat.Coprime.odd_of_right this
  have hd4 : d % 4 = 3 := by have := h.2.2.2.1; omega
  have hq4 : q % 4 = 3 := by have := h.2.2.1; omega
  rw [recMap_of_modEq _ m m m hm2 (unitOfCoprime_modEq hm (d_dvd_hostN e q d))
    (unitOfCoprime_modEq hm (q_dvd_hostN e q d)) (unitOfCoprime_modEq hm (two_dvd_hostN e q d)),
    jac_flip hd4 hodd, jac_flip hq4 hodd]
  have hJd : jacobiSym (-(d : ℤ)) m = 1 ∨ jacobiSym (-(d : ℤ)) m = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.Coprime.coprime_dvd_right (d_dvd_hostN e q d) hm).symm
  have hJq : jacobiSym (-(q : ℤ)) m = 1 ∨ jacobiSym (-(q : ℤ)) m = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.Coprime.coprime_dvd_right (q_dvd_hostN e q d) hm).symm
  exact ⟨(ite_zmod2 _ hJd).1, (ite_zmod2 _ hJd).2, (ite_zmod2 _ hJq).1, (ite_zmod2 _ hJq).2, rfl⟩

def sQ (l : ℕ) [Fact l.Prime] (x : (ZMod l)ˣ) : ZMod 2 :=
  Multiplicative.toAdd (sgn2 ((quadraticChar (ZMod l)).toUnitHom x))

lemma sQ_one (l : ℕ) [Fact l.Prime] : sQ l 1 = 0 := by
  unfold sQ
  rw [map_one, map_one]
  rfl

lemma exists_sQ_eq_one (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) : ∃ x : (ZMod l)ˣ, sQ l x = 1 := by
  obtain ⟨x, hx⟩ := quadraticChar_exists_neg_one' (F := ZMod l) (by rwa [ZMod.ringChar_zmod_n])
  refine ⟨x, ?_⟩
  unfold sQ
  rw [sgn2_toAdd_eq_ite, MulChar.coe_toUnitHom, hx]
  simp

lemma zmod_two_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma exists_sQ_eq (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (a : ZMod 2) : ∃ x : (ZMod l)ˣ, sQ l x = a := by
  rcases zmod_two_eq_zero_or_eq_one a with rfl | rfl
  · exact ⟨1, sQ_one l⟩
  · exact exists_sQ_eq_one l hl

lemma recMap_apply (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (u : (ZMod (hostN e q d))ˣ) :
    Multiplicative.toAdd (recMap e q d u)
      = ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)),
        Additive.ofMul (hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := rfl

lemma host_crt (e : ℕ) {q d : ℕ} (h : HostHyp q d) (x2 : (ZMod (2 ^ (e + 2)))ˣ) (xq : (ZMod q)ˣ) (xd : (ZMod d)ˣ) :
    ∃ u : (ZMod (hostN e q d))ˣ, ZMod.unitsMap (two_dvd_hostN e q d) u = x2 ∧
      ZMod.unitsMap (q_dvd_hostN e q d) u = xq ∧ ZMod.unitsMap (d_dvd_hostN e q d) u = xd := by
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have c2q : (2 ^ (e + 2)).Coprime q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.1).2 hq2.symm)
  have c2d : (2 ^ (e + 2)).Coprime d :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.2.1).2 hd2.symm)
  have cqd : q.Coprime d := (Nat.coprime_primes h.1 h.2.1).2 hqd
  obtain ⟨v, hv1, hv2⟩ := exists_unit_crt (N := 2 ^ (e + 2) * q) rfl c2q (dvd_mul_right _ _) (dvd_mul_left _ _) x2 xq
  have hA : 2 ^ (e + 2) * q ∣ hostN e q d := Dvd.intro _ rfl
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := hostN e q d) (a := 2 ^ (e + 2) * q) (b := d) rfl
    (Nat.Coprime.mul_left c2d cqd) hA (d_dvd_hostN e q d) v xd
  refine ⟨u, ?_, ?_, hu2⟩
  · rw [← hv1, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  · rw [← hv2, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]

lemma exists_hcl (e : ℕ) (t : HA e) : ∃ x2 : (ZMod (2 ^ (e + 2)))ˣ, Additive.ofMul (hcl e x2) = t := by
  obtain ⟨x2, hx2⟩ := QuotientGroup.mk_surjective (Additive.toMul t)
  exact ⟨x2, by unfold FrobeniusOrbits.hcl; rw [hx2]; rfl⟩

theorem recSurjective_valid : RecSurjective := by
  intro e q d _ _ h y
  obtain ⟨hq2, hd2, -⟩ := HostHyp_ne h
  obtain ⟨xd, hxd⟩ := exists_sQ_eq d hd2 (Multiplicative.toAdd y).1.1
  obtain ⟨xq, hxq⟩ := exists_sQ_eq q hq2 (Multiplicative.toAdd y).1.2
  obtain ⟨x2, hx2⟩ := exists_hcl e (Multiplicative.toAdd y).2
  obtain ⟨u, h1, h2, h3⟩ := host_crt e h x2 xq xd
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [recMap_apply, h1, h2, h3, hxd, hxq, hx2]

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

lemma mem_host_inertia_iff (p : ℕ) (x : E0 × HA e) :
    x ∈ (hostData e q d).inertia p ↔ ∃ u ∈ localUnits (hostN e q d) p, Multiplicative.toAdd (recMap e q d u) = x :=
  mem_inertia_iff q d (recMap e q d) p x

lemma hcl_one (e : ℕ) : Additive.ofMul (hcl e 1) = (0 : HA e) := rfl

lemma host_unram (h : HostHyp q d) (p : ℕ) (hp : p.Coprime (hostN e q d)) (hpp : p.Prime) :
    (hostData e q d).inertia p = ⊥ ∧
      (hostData e q d).frob p = Multiplicative.toAdd (recMap e q d (ZMod.unitOfCoprime p hp)) := by
  have hN := hostN_ne_zero e h
  have hpN : ¬ p ∣ hostN e q d := fun hh => hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hp hh)
  obtain ⟨h1, h2⟩ := unramified_spec (hostN e q d) p hN hpp hpN
  constructor
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_host_inertia_iff p x).1 hx
    rw [h1, Subgroup.mem_bot] at hu
    rw [hu, map_one]
    exact AddSubgroup.zero_mem _
  · change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) p)) = _
    congr 2
    apply Units.ext
    rw [h2, ZMod.coe_unitOfCoprime]

lemma host_inertia_two (h : HostHyp q d) (x : E0 × HA e) : x ∈ (hostData e q d).inertia 2 ↔ x.1 = 0 := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hM := (extension_local_parts e q d h).1.2
  rw [mem_host_inertia_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_localUnits_iff, hM] at hu
    rw [recMap_apply, (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_left d q)),
      (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_right q d)), sQ_one, sQ_one]
    rfl
  · intro hx
    obtain ⟨x2, hx2⟩ := exists_hcl e x.2
    obtain ⟨u, h1, h2, h3⟩ := host_crt e h x2 1 1
    refine ⟨u, ?_, ?_⟩
    · rw [mem_localUnits_iff, hM]
      exact (Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes h.1 h.2.1).2 (HostHyp_ne h).2.2)).1
        ⟨(unitsMap_eq_one_iff _ u).1 h2, (unitsMap_eq_one_iff _ u).1 h3⟩
    · rw [recMap_apply, h1, h2, h3, sQ_one, sQ_one, hx2]
      exact Prod.ext hx.symm rfl

lemma host_inertia_q (h : HostHyp q d) (x : E0 × HA e) : x ∈ (hostData e q d).inertia q ↔ x = 0 ∨ x = sg := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hM := (extension_local_parts e q d h).2.1.2
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have c2d : (2 ^ (e + 2)).Coprime d :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.2.1).2 hd2.symm)
  rw [mem_host_inertia_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_localUnits_iff, hM] at hu
    rw [recMap_apply, (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_left d _)),
      (unitsMap_eq_one_iff (two_dvd_hostN e q d) u).2 (hu.of_dvd (dvd_mul_right _ d)), sQ_one, hcl_one]
    rcases zmod_two_eq_zero_or_eq_one (sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)) with h0 | h0 <;> rw [h0]
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
    · obtain ⟨xq, hxq⟩ := exists_sQ_eq_one q hq2
      obtain ⟨u, h1, h2, h3⟩ := host_crt e h 1 xq 1
      refine ⟨u, ?_, ?_⟩
      · rw [mem_localUnits_iff, hM]
        exact (Nat.modEq_and_modEq_iff_modEq_mul c2d).1
          ⟨(unitsMap_eq_one_iff _ u).1 h1, (unitsMap_eq_one_iff _ u).1 h3⟩
      · rw [recMap_apply, h1, h2, h3, sQ_one, hxq, hcl_one]
        rfl

lemma host_inertia_d (h : HostHyp q d) (x : E0 × HA e) : x ∈ (hostData e q d).inertia d ↔ x = 0 ∨ x = sgc0 := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hM := (extension_local_parts e q d h).2.2.2
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have c2q : (2 ^ (e + 2)).Coprime q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.1).2 hq2.symm)
  rw [mem_host_inertia_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_localUnits_iff, hM] at hu
    rw [recMap_apply, (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_left q _)),
      (unitsMap_eq_one_iff (two_dvd_hostN e q d) u).2 (hu.of_dvd (dvd_mul_right _ q)), sQ_one, hcl_one]
    rcases zmod_two_eq_zero_or_eq_one (sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u)) with h0 | h0 <;> rw [h0]
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
    · obtain ⟨xd, hxd⟩ := exists_sQ_eq_one d hd2
      obtain ⟨u, h1, h2, h3⟩ := host_crt e h 1 1 xd
      refine ⟨u, ?_, ?_⟩
      · rw [mem_localUnits_iff, hM]
        exact (Nat.modEq_and_modEq_iff_modEq_mul c2q).1
          ⟨(unitsMap_eq_one_iff _ u).1 h1, (unitsMap_eq_one_iff _ u).1 h2⟩
      · rw [recMap_apply, h1, h2, h3, sQ_one, hxd, hcl_one]
        rfl

lemma unitOfCoprime_one (c : ℕ) (h : (1 : ℕ).Coprime c) : ZMod.unitOfCoprime 1 h = 1 := by
  apply Units.ext
  simp

lemma host_frob_two (h : HostHyp q d) : (hostData e q d).frob 2 = sg := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hP, hM⟩ := (extension_local_parts e q d h).1
  obtain ⟨w1, w2⟩ := frobUnit_modEq (N := hostN e q d) Nat.prime_two
  rw [hM] at w1
  rw [hP] at w2
  change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) 2)) = _
  rw [recMap_of_modEq _ 2 2 1 (Nat.coprime_one_left _) (w1.of_dvd (dvd_mul_left d q)) (w1.of_dvd (dvd_mul_right q d)) w2,
    jac_two_d h, jac_two_q h, unitOfCoprime_one, hcl_one]
  rfl

lemma host_frob_q (h : HostHyp q d) (hq : q.Coprime (2 ^ (e + 2))) :
    (hostData e q d).frob q = ((0, 0), Additive.ofMul (hcl e (ZMod.unitOfCoprime q hq))) := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hP, hM⟩ := (extension_local_parts e q d h).2.1
  obtain ⟨w1, w2⟩ := frobUnit_modEq (N := hostN e q d) h.1
  rw [hM] at w1
  rw [hP] at w2
  change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) q)) = _
  rw [recMap_of_modEq _ q 1 q hq (w1.of_dvd (dvd_mul_left d _)) w2 (w1.of_dvd (dvd_mul_right _ d)),
    jac_q_d h, Nat.cast_one, jacobiSym.one_left]
  rfl

lemma host_frob_d (h : HostHyp q d) (hd : d.Coprime (2 ^ (e + 2))) :
    (hostData e q d).frob d = ((0, 1), Additive.ofMul (hcl e (ZMod.unitOfCoprime d hd))) := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hP, hM⟩ := (extension_local_parts e q d h).2.2
  obtain ⟨w1, w2⟩ := frobUnit_modEq (N := hostN e q d) h.2.1
  rw [hM] at w1
  rw [hP] at w2
  change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) d)) = _
  rw [recMap_of_modEq _ 1 d d hd w2 (w1.of_dvd (dvd_mul_left q _)) (w1.of_dvd (dvd_mul_right _ q)),
    jac_d_q h, Nat.cast_one, jacobiSym.one_left]
  rfl

end

theorem extension_local : HostLocal := by
  intro e q d _ _ h
  exact ⟨fun p hp hpp => host_unram h p hp hpp, ⟨host_inertia_two h, host_frob_two h⟩,
    ⟨host_inertia_q h, host_frob_q h⟩, ⟨host_inertia_d h, host_frob_d h⟩⟩

lemma coprime_hostN (e : ℕ) {q d p : ℕ} (h : HostHyp q d) (hp : p.Prime) (h2 : p ≠ 2) (hq : p ≠ q) (hd : p ≠ d) :
    p.Coprime (hostN e q d) := by
  unfold hostN
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 h2))
    ((Nat.coprime_primes hp h.1).2 hq)) ((Nat.coprime_primes hp h.2.1).2 hd)

theorem extension_facts : HostFactsHost := by
  intro e q d _ _ h
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have cq : q.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2)
  refine ⟨h.1, h.2.1, hq2, hd2, hqd, ?_, ?_, ?_, host_inertia_d h⟩
  · intro p hp h2 hq hd
    exact (host_unram h p (coprime_hostN e h hp h2 hq hd) hp).1
  · rintro p (rfl | hp) x hx
    · have := (host_inertia_two h x).1 hx
      change x.1.1 = 0
      rw [this]
      rfl
    · have hp' : p = q := hp
      rw [hp'] at hx
      rcases (host_inertia_q h x).1 hx with rfl | rfl <;> rfl
  · rintro p (rfl | hp)
    · rw [host_frob_two h]
      rfl
    · have hp' : p = q := hp
      rw [hp', host_frob_q h cq]
      rfl

theorem balance_for_extension : BalanceHost := by
  intro e q d _ _ h ell a t w ha hw N hN
  exact colour_balance (hostData e q d) (extension_facts e q d h) ell a t w ha hw N hN

lemma chC_val {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (chC : AddChar (E0 × H) ℂ) g = if g.1.1 = 0 then 1 else -1 := rfl

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

lemma chC_trivial_two (h : HostHyp q d) : ∀ x ∈ (hostData e q d).inertia 2, (chC : AddChar (E0 × HA e) ℂ) x = 1 := by
  intro x hx
  rw [chC_val, (host_inertia_two h x).1 hx]
  simp

lemma chC_trivial_q (h : HostHyp q d) : ∀ x ∈ (hostData e q d).inertia q, (chC : AddChar (E0 × HA e) ℂ) x = 1 := by
  intro x hx
  rw [chC_val]
  rcases (host_inertia_q h x).1 hx with rfl | rfl <;> simp [sg]

lemma chC_nontrivial_d (h : HostHyp q d) :
    ¬ ∀ x ∈ (hostData e q d).inertia d, (chC : AddChar (E0 × HA e) ℂ) x = 1 := by
  intro hh
  have h1 := hh sgc0 ((host_inertia_d h _).2 (Or.inr rfl))
  rw [chC_val] at h1
  simp [sgc0] at h1
  norm_num at h1

lemma jac_self (d : ℕ) (hd : 1 < d) : jacobiSym (d : ℤ) d = 0 := by
  rw [jacobiSym.mod_left, Int.emod_self, jacobiSym.zero_left hd]

lemma cosetMean_chC (h : HostHyp q d) (p i : ℕ) (hp : p.Prime) (hi : i ≠ 0) :
    cosetMean ((hostData e q d).inertia p) (i • (hostData e q d).frob p) chC
      = (((jacobiSym (p : ℤ) d) ^ i : ℤ) : ℂ) := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  by_cases hpd : p = d
  · subst hpd
    rw [cosetMean_of_nontrivial _ _ _ (chC_nontrivial_d h), jac_self p hp.one_lt, zero_pow hi]
    simp
  by_cases hp2 : p = 2
  · subst hp2
    rw [cosetMean_of_trivial _ _ _ (chC_trivial_two h), AddChar.map_nsmul_eq_pow, host_frob_two h, jac_two_d h, chC_val]
    simp [sg]
  by_cases hpq : p = q
  · subst hpq
    have cq : p.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2)
    rw [cosetMean_of_trivial _ _ _ (chC_trivial_q h), AddChar.map_nsmul_eq_pow, host_frob_q h cq, jac_q_d h, chC_val]
    simp
  have hcop := coprime_hostN e h hp hp2 hpq hpd
  obtain ⟨h1, h2⟩ := host_unram (e := e) h p hcop hp
  have c2 : p.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  rw [cosetMean_of_trivial _ _ _ (by
      intro x hx
      rw [h1, AddSubgroup.mem_bot] at hx
      rw [hx, AddChar.map_zero_eq_one]), AddChar.map_nsmul_eq_pow, h2,
    recMap_of_modEq _ p p p c2 (unitOfCoprime_modEq hcop (d_dvd_hostN e q d))
      (unitOfCoprime_modEq hcop (q_dvd_hostN e q d)) (unitOfCoprime_modEq hcop (two_dvd_hostN e q d)), chC_val]
  have hJ : jacobiSym (p : ℤ) d = 1 ∨ jacobiSym (p : ℤ) d = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hp h.2.1).2 hpd
  rcases hJ with hJ | hJ <;> rw [hJ] <;> simp

end

theorem character_conductor : ChConductor := by
  intro e q d _ _ h
  have hN := hostN_ne_zero e h
  constructor
  · have i2 := (inertia_conductor (H := HA e) (hostN e q d) q d (recMap e q d) chC 2 hN Nat.prime_two).1
      (chC_trivial_two h)
    have iq := (inertia_conductor (H := HA e) (hostN e q d) q d (recMap e q d) chC q hN h.1).1
      (chC_trivial_q h)
    have id : d ∣ (dirChar (recMap e q d) chC).conductor := by
      by_contra hh
      exact chC_nontrivial_d h
        ((inertia_conductor (H := HA e) (hostN e q d) q d (recMap e q d) chC d hN h.2.1).2 hh)
    have hdvd : (dirChar (recMap e q d) chC).conductor ∣ 2 ^ (e + 2) * q * d :=
      DirichletCharacter.conductor_dvd_level _
    have c2 : ((dirChar (recMap e q d) chC).conductor).Coprime (2 ^ (e + 2)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 i2).symm
    have cq : ((dirChar (recMap e q d) chC).conductor).Coprime q :=
      ((Nat.Prime.coprime_iff_not_dvd h.1).2 iq).symm
    exact Nat.dvd_antisymm (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.mul_right c2 cq) hdvd) id
  · intro n hn
    let φ : ℤ →* ℤ :=
      { toFun := fun a => jacobiSym a d
        map_one' := jacobiSym.one_left d
        map_mul' := fun a b => jacobiSym.mul_left a b d }
    have hφ : jacobiSym (n : ℤ) d = ∏ p ∈ n.primeFactors, (jacobiSym (p : ℤ) d) ^ n.factorization p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
      rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod]
      change φ _ = _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro p _
      rw [Nat.cast_pow, map_pow]
      rfl
    rw [hφ, Int.cast_prod]
    unfold primVal
    apply Finset.prod_congr rfl
    intro p hp
    have hi : n.factorization p ≠ 0 := by
      have := (Nat.support_factorization n ▸ hp : p ∈ n.factorization.support)
      exact Finsupp.mem_support_iff.1 this
    exact cosetMean_chC h p _ (Nat.prime_of_mem_primeFactors hp) hi

theorem dirichlet_character_injective : DirCharInjective := by
  intro e q d _ _ h ψ ψ' hψ
  apply DFunLike.ext
  intro x
  obtain ⟨u, hu⟩ := recSurjective_valid e q d h (Multiplicative.ofAdd x)
  have h1 := dirChar_unit (recMap e q d) ψ u
  have h2 := dirChar_unit (recMap e q d) ψ' u
  rw [hu] at h1 h2
  have h3 : dirChar (recMap e q d) ψ (u : ZMod (hostN e q d)) = dirChar (recMap e q d) ψ' (u : ZMod (hostN e q d)) := by
    rw [hψ]
  rw [h1, h2] at h3
  exact h3

lemma sign_injective : ∀ s s' : ℤˣ, Multiplicative.toAdd (sgn2 s) = Multiplicative.toAdd (sgn2 s') → s = s' := by decide

lemma sgn2_toAdd_surjective : ∀ x : ZMod 2, ∃ s : ℤˣ, Multiplicative.toAdd (sgn2 s) = x := by decide

lemma galois_map_mul (e : ℕ) (g g' : FrobeniusOrbits.GG e) : galoisToProduct e (g * g') = galoisToProduct e g + galoisToProduct e g' := by
  unfold galoisToProduct
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
  rfl

lemma galois_map_one (e : ℕ) : galoisToProduct e 1 = 0 := by
  unfold galoisToProduct
  simp only [Prod.fst_one, Prod.snd_one, map_one]
  rfl

lemma galois_map_injective (e : ℕ) : Function.Injective (galoisToProduct e) := by
  intro g g' hg
  unfold galoisToProduct at hg
  simp only [Prod.mk.injEq] at hg
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  exact Prod.ext (Prod.ext (sign_injective _ _ h2) (sign_injective _ _ h1)) (Additive.ofMul.injective h3)

theorem galois_map_iso : GaloisToProductIsIso := by
  intro e
  refine ⟨⟨galois_map_injective e, ?_⟩, galois_map_mul e⟩
  rintro ⟨⟨x, y⟩, t⟩
  obtain ⟨s, hs⟩ := sgn2_toAdd_surjective x
  obtain ⟨s', hs'⟩ := sgn2_toAdd_surjective y
  exact ⟨((s', s), Additive.toMul t), by unfold galoisToProduct; simp only [hs, hs']; rfl⟩

lemma galois_map_apply (e : ℕ) (g : FrobeniusOrbits.GG e) :
    galoisToProduct e g = ((if ((g.1.2 : ℤˣ) : ℤ) = 1 then 0 else 1, if ((g.1.1 : ℤˣ) : ℤ) = 1 then 0 else 1),
      Additive.ofMul g.2) := by
  unfold galoisToProduct
  rw [sgn2_toAdd_eq_ite, sgn2_toAdd_eq_ite]

section Field

open NumberField Ideal
open Formalism.FrobeniusOrbits (hostE galE aE bE hostGalois hostGalSpec hostInertia hostDecomp hostFrob_of)
open Formalism.TwoAdicCyclotomicDecomposition (IsLayer galMap layerGalois odd_cyc_frob odd_frob_sgn odd_card_under odd_intCast_mem_iff)

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

lemma galE_mul' (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galE e ζ a b (σ * τ) = galE e ζ a b σ * galE e ζ a b τ :=
  (hostGalois e q d h.toHypOdd L ζ a b hL).2.2.1 σ τ

lemma galE_one' (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) :
    galE e ζ a b (1 : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) = 1 := by
  have := galE_mul' h hL 1 1
  rw [mul_one] at this
  exact mul_eq_left.mp this.symm

lemma galois_map_mul_inv (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b)
    (σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galoisToProduct e (galE e ζ a b (σ * τ⁻¹)) = galoisToProduct e (galE e ζ a b σ) - galoisToProduct e (galE e ζ a b τ) := by
  rw [eq_sub_iff_add_eq, ← galois_map_mul, ← galE_mul' h hL, inv_mul_cancel_right]

lemma sgn2_toAdd_eq_zero_iff : ∀ s : ℤˣ, Multiplicative.toAdd (sgn2 s) = 0 ↔ s = 1 := by decide

lemma galois_map_first_eq_zero_iff (g : FrobeniusOrbits.GG e) : (galoisToProduct e g).1 = 0 ↔ g.1 = 1 := by
  change ((Multiplicative.toAdd (sgn2 g.1.2), Multiplicative.toAdd (sgn2 g.1.1)) : E0) = 0 ↔ _
  rw [Prod.ext_iff, Prod.ext_iff]
  change (Multiplicative.toAdd (sgn2 g.1.2) = 0 ∧ Multiplicative.toAdd (sgn2 g.1.1) = 0) ↔ (g.1.1 = 1 ∧ g.1.2 = 1)
  rw [sgn2_toAdd_eq_zero_iff, sgn2_toAdd_eq_zero_iff, and_comm]

lemma galois_map_sign : galoisToProduct e (FrobeniusOrbits.sg e) = sg := by
  rw [galois_map_apply]
  simp [FrobeniusOrbits.sg, sg]

lemma galois_map_complex_conjugation : galoisToProduct e (((1, -1), 1) : FrobeniusOrbits.GG e) = sgc0 := by
  rw [galois_map_apply]
  simp [sgc0]

variable [Fact q.Prime] [Fact d.Prime]

lemma field_inertia (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [hPl : P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ galoisToProduct e (galE e ζ a b σ) ∈ (hostData e q d).inertia p := by
  have hI := hostInertia e q d h L ζ a b hL σ
  have hinj := galois_map_injective e
  by_cases hp2 : p = 2
  · subst hp2
    have : P.LiesOver (span {(2 : ℤ)}) := by simpa using hPl
    rw [hI.1 P, host_inertia_two h, galois_map_first_eq_zero_iff]
  by_cases hpq : p = q
  · subst hpq
    rw [hI.2.1 P, host_inertia_q h, ← galois_map_one e, ← galois_map_sign, hinj.eq_iff, hinj.eq_iff]
  by_cases hpd : p = d
  · subst hpd
    rw [hI.2.2 P, host_inertia_d h, ← galois_map_one e, ← galois_map_complex_conjugation, hinj.eq_iff, hinj.eq_iff]
  have hp : p.Prime := Fact.out
  rw [(hostFrob_of hostGalois hostGalSpec e q d h.toHypOdd L ζ a b hL p hp2 hpq hpd P).2.2 σ,
    (host_unram h p (coprime_hostN e h hp hp2 hpq hpd) hp).1, AddSubgroup.mem_bot, ← galois_map_one e, hinj.eq_iff,
    ← galE_one' h hL, (hostGalois e q d h.toHypOdd L ζ a b hL).2.2.2.1.eq_iff]

lemma field_frob_of (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ₀ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (h₀ : IsArithFrobAt ℤ σ₀ P)
    (h1 : galoisToProduct e (galE e ζ a b σ₀) - (hostData e q d).frob p ∈ (hostData e q d).inertia p)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    IsArithFrobAt ℤ σ P ↔
      galoisToProduct e (galE e ζ a b σ) - (hostData e q d).frob p ∈ (hostData e q d).inertia p := by
  constructor
  · intro hσ
    have h2 : ∀ x : 𝓞 (hostE ζ a b), (σ * σ₀⁻¹) • x - x ∈ P :=
      AddSubgroup.mem_inertia.mp (hσ.mul_inv_mem_inertia h₀)
    rw [field_inertia h hL p P, galois_map_mul_inv h hL] at h2
    have := AddSubgroup.add_mem _ h2 h1
    rwa [sub_add_sub_cancel] at this
  · intro hσ
    have h2 := AddSubgroup.sub_mem _ hσ h1
    rw [sub_sub_sub_cancel_right, ← galois_map_mul_inv h hL, ← field_inertia h hL p P] at h2
    have := FrobeniusOrbits.Frob.frob_mul_inertia P (σ * σ₀⁻¹) σ₀ (AddSubgroup.mem_inertia.mpr h2) h₀
    rwa [inv_mul_cancel_right] at this

omit [Fact q.Prime] [Fact d.Prime] in

lemma exists_frob_odd (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    ∃ σ₀ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ₀ P ∧
      (∀ hp : p.Coprime (2 ^ (e + 2)), (galE e ζ a b σ₀).2 = hcl e (ZMod.unitOfCoprime p hp)) ∧
      (p ≠ q → (((galE e ζ a b σ₀).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p) ∧
      (p ≠ d → (((galE e ζ a b σ₀).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p) := by
  have hqd := h.toHypOdd
  have hp : p.Prime := Fact.out
  obtain ⟨hEgal, -, -, -⟩ := hostGalois e q d hqd L ζ a b hL
  obtain ⟨hLgal, -, -, -⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b hL
  have := hEgal
  have := hLgal
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  have : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P (span {(p : ℤ)})
  have : Finite (𝓞 L ⧸ Q) := by
    have hpb : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
  let σ₀ : Gal(hostE ζ a b/ℚ) := τ.restrictNormal (hostE ζ a b)
  have hσ₀ : ∀ x : hostE ζ a b, ((σ₀ x : hostE ζ a b) : L) = τ x :=
    fun x => AlgEquiv.restrictNormal_commutes τ (hostE ζ a b) x
  have hσ₀F : IsArithFrobAt ℤ σ₀ P := by
    intro x
    have hx := hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)
    rw [odd_card_under p Q] at hx
    rw [odd_card_under p P]
    rw [Ideal.over_def Q P, Ideal.under_def, Ideal.mem_comap]
    convert hx using 1
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_pow, MulSemiringAction.toAlgHom_apply]
    congr 1
    show (((σ₀ • x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L) =
      τ (((x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L)
    exact hσ₀ x
  have hval := (hostGalSpec e q d hqd L ζ a b hL σ₀).2.2.2 τ hσ₀
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [hL.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [hL.2.2.1]; push_cast; rfl
  refine ⟨σ₀, hσ₀F, fun hc => ?_, fun hpq => ?_, fun hpd => ?_⟩
  · rw [hval]
    change hcl e (galMap hL.1 a b τ).1 = _
    congr 1
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    exact odd_cyc_frob hL.1 p hp2 Q τ hτ
  · rw [hval]
    refine odd_frob_sgn p hp2 Q τ hτ a _ ha ?_
    rw [dvd_neg]
    intro hd'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hqd.1).mp (by exact_mod_cast hd'))
  · rw [hval]
    refine odd_frob_sgn p hp2 Q τ hτ b _ hb ?_
    rw [dvd_neg]
    intro hd'
    exact hpd ((Nat.prime_dvd_prime_iff_eq hp hqd.2.1).mp (by exact_mod_cast hd'))

omit [Fact q.Prime] [Fact d.Prime] in

lemma exists_frob_two (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [hPl : P.LiesOver (span {((2 : ℕ) : ℤ)})] :
    ∃ σ₀ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ₀ P ∧ (galE e ζ a b σ₀).1 = (-1, 1) := by
  have hqd := h.toHypOdd
  obtain ⟨hq2, hd2, -⟩ := HostHyp_ne h
  obtain ⟨hEgal, -, -, -⟩ := hostGalois e q d hqd L ζ a b hL
  have := hEgal
  have : P.LiesOver (span {(2 : ℤ)}) := by simpa using hPl
  have : Finite (𝓞 (hostE ζ a b) ⧸ P) := by
    have hpb : span {(2 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      norm_num
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨σ₀, h₀⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(hostE ζ a b/ℚ) P
  have cq : q.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2)
  have cd : d.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.2.1 Nat.prime_two).2 hd2)
  have hD := (hostDecomp e q d h L ζ a b hL (ZMod.unitOfCoprime q cq) (ZMod.unitOfCoprime d cd)
    (ZMod.coe_unitOfCoprime q cq) (ZMod.coe_unitOfCoprime d cd) σ₀).1 P
  have hb1 : (galE e ζ a b σ₀).1.2 = 1 := (FrobeniusOrbits.mem_Psi_iff _).1 (hD.1 h₀.mem_stabilizer)
  have ha1 : (galE e ζ a b σ₀).1.1 = -1 := by
    rcases Int.units_eq_one_or (galE e ζ a b σ₀).1.1 with h1 | h1
    · exfalso
      have hin : ∀ x : 𝓞 (hostE ζ a b), σ₀ • x - x ∈ P :=
        ((hostInertia e q d h L ζ a b hL σ₀).1 P).2 (Prod.ext h1 hb1)
      have hq8 : q % 8 = 3 := h.2.2.1
      have hq4 : q % 4 = 3 := by omega
      have haE : (aE ζ a b) ^ 2 = -(q : hostE ζ a b) := by
        apply Subtype.ext
        push_cast
        exact hL.2.1
      let W : 𝓞 (hostE ζ a b) := ⟨(1 + aE ζ a b) / 2, FrobeniusOrbits.Inertia.omega_integral hq4 haE⟩
      have hF := h₀ W
      rw [odd_card_under 2 P, MulSemiringAction.toAlgHom_apply] at hF
      have h3 : W ^ 2 - W ∈ P := by
        have := P.sub_mem (hin W) hF
        convert this using 1
        ring
      set c : ℤ := ((q : ℤ) + 1) / 4 with hc
      have h4 : 4 * c = (q : ℤ) + 1 := by omega
      have h4E : 4 * (c : hostE ζ a b) = (q : hostE ζ a b) + 1 := by exact_mod_cast h4
      have hW : W ^ 2 - W = ((-c : ℤ) : 𝓞 (hostE ζ a b)) := by
        apply RingOfIntegers.coe_injective
        simp only [map_sub, map_pow, map_intCast]
        change ((1 + aE ζ a b) / 2) ^ 2 - (1 + aE ζ a b) / 2 = ((-c : ℤ) : hostE ζ a b)
        push_cast
        linear_combination (1 / 4 : hostE ζ a b) * haE + (1 / 4 : hostE ζ a b) * h4E
      rw [hW, odd_intCast_mem_iff 2 P] at h3
      omega
    · exact h1
  exact ⟨σ₀, h₀, Prod.ext ha1 hb1⟩

theorem extension_data_field : HostDataField := by
  intro e q d _ _ h L _ _ ζ a b hL p _ P _ _ σ
  refine ⟨field_inertia h hL p P σ, ?_⟩
  have hp : p.Prime := Fact.out
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨σ₀, h₀, h1⟩ := exists_frob_two h hL P
    refine field_frob_of h hL 2 P σ₀ h₀ ?_ σ
    rw [host_inertia_two h, host_frob_two h, galois_map_apply, h1]
    simp [sg]
  obtain ⟨σ₀, h₀, hH, ha, hb⟩ := exists_frob_odd h hL p hp2 P
  have c2 : p.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  refine field_frob_of h hL p P σ₀ h₀ ?_ σ
  rw [galois_map_apply, hH c2]
  by_cases hpq : p = q
  · subst hpq
    rw [hb hqd, h.2.2.2.2, host_frob_q h c2, host_inertia_q h]
    by_cases hs : (((galE e ζ a b σ₀).1.1 : ℤˣ) : ℤ) = 1 <;> simp [hs, sg]
  by_cases hpd : p = d
  · subst hpd
    rw [ha hqd.symm, FrobeniusOrbits.hostRecip q p h, host_frob_d h c2, host_inertia_d h]
    by_cases hs : (((galE e ζ a b σ₀).1.2 : ℤˣ) : ℤ) = 1 <;> simp [hs, sgc0]
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hcop := coprime_hostN e h hp hp2 hpq hpd
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hd4 : d % 4 = 3 := by have := h.2.2.2.1; omega
  have hq4 : q % 4 = 3 := by have := h.2.2.1; omega
  rw [ha hpq, hb hpd, (host_unram h p hcop hp).2,
    recMap_of_modEq _ p p p c2 (unitOfCoprime_modEq hcop (d_dvd_hostN e q d))
      (unitOfCoprime_modEq hcop (q_dvd_hostN e q d)) (unitOfCoprime_modEq hcop (two_dvd_hostN e q d)),
    jac_flip hd4 hodd, jac_flip hq4 hodd, sub_self]
  exact AddSubgroup.zero_mem _

end Field

end Formalism.LFunctionChainParameters.LHost
