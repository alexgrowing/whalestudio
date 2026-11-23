import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DecompTypeI
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdDiff
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdBound

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits

namespace Rd

theorem cycRat (m : ℕ) : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun h h0 => absurd (Set.mem_singleton_iff.1 h) h0, fun x => ?_⟩
    have htop : Algebra.adjoin ℚ ((Polynomial.cyclotomic 0 ℚ).rootSet
        (Polynomial.cyclotomic 0 ℚ).SplittingField) = ⊤ :=
      Polynomial.SplittingField.adjoin_rootSet _
    rw [Polynomial.cyclotomic_zero, Polynomial.rootSet_one, Algebra.adjoin_empty] at htop
    have hx : x ∈ (⊥ : Subalgebra ℚ (CyclotomicField 0 ℚ)) := by
      rw [show (⊥ : Subalgebra ℚ (CyclotomicField 0 ℚ)) = ⊤ from htop]
      exact Algebra.mem_top
    exact (bot_le : (⊥ : Subalgebra ℚ (CyclotomicField 0 ℚ)) ≤ _) hx
  · haveI : NeZero m := ⟨hm.ne'⟩
    haveI : NeZero (m : ℚ) := ⟨by exact_mod_cast hm.ne'⟩
    exact CyclotomicField.isCyclotomicExtension m ℚ

theorem dvd_discr_of_inertia {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} (hl : l.Prime)
    (h : ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})],
      ∃ σ : E ≃ₐ[ℚ] E, σ ≠ 1 ∧ ∀ x : 𝓞 E, σ • x - x ∈ P) : (l : ℤ) ∣ discr E := by
  by_contra hn
  have : Fact l.Prime := ⟨hl⟩
  have hl' := Nat.prime_iff_prime_int.mp hl
  have hpr : (span {(l : ℤ)}).IsPrime := (span_singleton_prime hl'.ne_zero).mpr hl'
  obtain ⟨⟨P, h1, h2⟩⟩ : Nonempty ((span {(l : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hpb : span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl'.ne_zero
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpb P
  have hun := (not_dvd_discr_iff_forall_liesOver E (𝓞 E) hl').mp hn P (h1.isMaximal hP0) h2
  have hcard := card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (span {(l : ℤ)}) P
  rw [ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P (E ≃ₐ[ℚ] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, Subgroup.card_eq_one] at hcard
  obtain ⟨σ, hσ1, hσ⟩ := h P
  have h3 : σ ∈ P.inertia (E ≃ₐ[ℚ] E) := AddSubgroup.mem_inertia.mpr hσ
  rw [hcard, Subgroup.mem_bot] at h3
  exact hσ1 h3

theorem hcl_eq_one {e : ℕ} {v : (ZMod (2 ^ (e + 2)))ˣ} (h : hcl e v = 1) : v = 1 ∨ v = -1 := by
  unfold hcl at h
  rw [QuotientGroup.eq_one_iff] at h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← hk, ← two_mul, zpow_mul]
    simp
  · right
    rw [← hk, zpow_add, zpow_mul]
    simp

variable {φ : Frame} (H : HostRaw φ)

instance neZeroN : NeZero H.condN :=
  ⟨by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity⟩

theorem log_rd_eq : Real.log H.rd = SS H.art.ker := by
  have := cycRat H.condN
  let : Algebra H.E (CyclotomicField H.condN ℚ) := H.cycEmb.toRingHom.toAlgebra
  have h1 := log_rd H.cycZeta_prim H.E H.art.ker (fun σ u hσ => by
    have h2 := H.art_spec u σ hσ
    rw [MonoidHom.mem_ker, ← H.gal.symm.map_eq_one_iff]
    constructor
    · intro h3
      exact AlgEquiv.ext fun x => H.cycEmb.injective ((h2 x).trans (h3 x))
    · intro h3 x
      rw [h3] at h2
      exact (h2 x).symm)
  have h0 : (0 : ℝ) < |(discr H.E : ℝ)| := by simpa using discr_ne_zero H.E
  rw [HostRaw.rd, Real.log_rpow h0, one_div_mul_eq_div, h1, SS, ← abel]

theorem rd_pos : 0 < H.rd := by
  unfold Formalism.HC.HostRaw.rd
  apply Real.rpow_pos_of_pos
  apply abs_pos.2
  exact_mod_cast NumberField.discr_ne_zero H.E

theorem two_dvd : 2 ^ (φ.e + 2) ∣ H.condN := (H.tower_dvd.mul_right _).mul_right _

theorem hH_art (u : (ZMod H.condN)ˣ) : φ.hH (H.art u).2 = hcl φ.e (ZMod.unitsMap (two_dvd H) u) := by
  apply H.art_h
  show (ZMod.castHom (two_dvd H) (ZMod (2 ^ (φ.e + 2)))) (u : ZMod H.condN) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem q_mul_d_ne_zero : H.q * H.d ≠ 0 := by
  intro h0
  have h1 := H.QS_coprime
  rw [h0, Nat.coprime_zero_right] at h1
  have h2 := H.tower_dvd
  rw [h1, Nat.dvd_one] at h2
  have h3 : 2 ^ 1 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [h2] at h3
  norm_num at h3

theorem div_d : H.condN / H.d = H.QS * H.q := by
  show H.QS * H.q * H.d / H.d = H.QS * H.q
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (right_ne_zero_of_mul (q_mul_d_ne_zero H)))

theorem div_q : H.condN / H.q = H.QS * H.d := by
  show H.QS * H.q * H.d / H.q = H.QS * H.d
  rw [show H.QS * H.q * H.d = H.QS * H.d * H.q by ring]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (left_ne_zero_of_mul (q_mul_d_ne_zero H)))

theorem q_ne_d : H.q ≠ H.d := by
  intro h
  have h1 := H.hyp.2.2.1
  have h2 := H.hyp.2.2.2.1
  rw [h] at h1
  omega

theorem exists_d (C : HostCore H) : ∃ u ∈ KK H.condN (H.QS * H.q), u ∉ H.art.ker := by
  by_contra h
  push Not at h
  have hc : Nat.Coprime (H.QS * H.q) H.d := Nat.Coprime.mul_left H.QS_coprime.coprime_mul_left_right
    ((Nat.coprime_primes H.hyp.1 H.hyp.2.1).mpr (q_ne_d H))
  have h1 := KK_gcd (φ.chD.comp H.art).ker (dvd_mul_right (H.QS * H.q) H.d) (dvd_mul_left H.d (H.QS * H.q))
    (fun u hu => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.mp (h u hu), map_one])
    (fun u hu => by
      apply Units.ext
      refine (C.art_ch u).trans ?_
      rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast Int.natCast_modEq_iff.mpr (mem_KK.mp hu)), jacobiSym.one_left]
      rfl) (-1) (by rw [hc, mem_KK]; exact Nat.modEq_one)
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, H.art_neg_one] at h1
  exact absurd h1 (show ¬ (-1 : ℤˣ) = 1 by decide)

theorem exists_two : ∃ u ∈ KK H.condN (ordCompl[2] H.condN), u ∉ H.art.ker := by
  by_contra h
  push Not at h
  have hc : Nat.Coprime (ordCompl[2] H.condN) (2 ^ (φ.e + 2)) :=
    ((Nat.coprime_ordCompl Nat.prime_two (NeZero.ne _)).pow_left _).symm
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (two_dvd H)
    (ZMod.unitOfCoprime 3 (Nat.Coprime.pow_right _ (by norm_num)))
  have h1 := KK_gcd (φ.hH.comp ((MonoidHom.snd _ _).comp H.art)).ker (Nat.ordCompl_dvd _ 2) (two_dvd H)
    (fun u hu => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.mem_ker.mp (h u hu), map_one, map_one])
    (fun u hu => by
      refine (hH_art H u).trans ?_
      rw [MonoidHom.mem_ker.mp ((mem_ker_iff (two_dvd H) u).mpr (mem_KK.mp hu))]
      rfl) u (by rw [hc, mem_KK]; exact Nat.modEq_one)
  have h2 := (hH_art H u).symm.trans h1
  rw [hu] at h2
  have h3 : 2 ^ 4 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by have := H.two_le_e; omega)
  rcases hcl_eq_one h2 with h4 | h4
  · have h5 := congrArg Units.val h4
    rw [ZMod.coe_unitOfCoprime, Units.val_one] at h5
    have h6 : ((2 : ℕ) : ZMod (2 ^ (φ.e + 2))) = 0 := by
      push_cast at h5 ⊢
      linear_combination h5
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).mp h6)
    omega
  · have h5 := congrArg Units.val h4
    rw [ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one] at h5
    have h6 : ((4 : ℕ) : ZMod (2 ^ (φ.e + 2))) = 0 := by
      push_cast at h5 ⊢
      linear_combination h5
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).mp h6)
    omega

theorem rho_d : rho H.art.ker (H.condN / H.d) ≤ 1 / 2 := by
  rw [div_d]
  refine rho_le_half _ (dvd_mul_right _ _) fun u hu v hv h1 h2 => ?_
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [map_mul, (H.art_d u (mem_KK.mp hu)).resolve_left h1, (H.art_d v (mem_KK.mp hv)).resolve_left h2]
  exact Prod.ext (show ((1, -1) : G0) * (1, -1) = 1 by decide) (mul_one _)

theorem rho_q : rho H.art.ker (H.condN / H.q) ≤ 1 / 2 := by
  rw [div_q]
  have : Fact H.q.Prime := ⟨H.hyp.1⟩
  have hf : H.QS * H.d ∣ H.condN := ⟨H.q, mul_right_comm _ _ _⟩
  have hq : H.q ∣ H.condN := (dvd_mul_left _ _).mul_right _
  have hc : Nat.Coprime (H.QS * H.d) H.q := Nat.Coprime.mul_left H.QS_coprime.coprime_mul_right_right
    ((Nat.coprime_primes H.hyp.2.1 H.hyp.1).mpr (q_ne_d H).symm)
  have hcyc : IsCyclic (ZMod.unitsMap hf).ker := by
    refine isCyclic_of_injective ((ZMod.unitsMap hq).comp (ZMod.unitsMap hf).ker.subtype) ?_
    rw [injective_iff_map_eq_one]
    rintro ⟨u, hu⟩ h1
    have h2 := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨(mem_ker_iff hf u).mp hu, (mem_ker_iff hq u).mp h1⟩
    rw [mul_right_comm, ← mem_ker_iff dvd_rfl, ZMod.unitsMap_self, MonoidHom.mem_ker, MonoidHom.id_apply] at h2
    exact Subtype.ext h2
  obtain ⟨⟨g, hg⟩, hgen⟩ := hcyc.exists_generator
  have hg2 := H.art_q g ((mem_ker_iff hf g).mp hg)
  have key : ∀ u ∈ KK H.condN (H.QS * H.d), H.art u ≠ 1 → H.art u = H.art g := by
    intro u hu h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨u, (mem_ker_iff hf u).mpr (mem_KK.mp hu)⟩)
    have h2 : g ^ k = u := congrArg Subtype.val hk
    rw [← h2, map_zpow] at h1 ⊢
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, zpow_ofNat, hg2, one_zpow] at h1
      exact absurd rfl h1
    · rw [zpow_add, zpow_mul, zpow_ofNat, hg2, one_zpow, one_mul, zpow_one]
  refine rho_le_half _ hf fun u hu v hv h1 h2 => ?_
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [map_mul, key u hu h1, key v hv h2, ← sq, hg2]

end Rd

open Rd

variable {φ : Frame} (H : HostRaw φ)

theorem discr_primes (C : HostCore H) :
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr H.E → p ∣ H.condN) ∧ (2 : ℤ) ∣ discr H.E ∧ (H.d : ℤ) ∣ discr H.E := by
  have := H.galois
  refine ⟨fun p hp h => ?_, ?_, ?_⟩
  · have := cycRat H.condN
    let : Algebra H.E (CyclotomicField H.condN ℚ) := H.cycEmb.toRingHom.toAlgebra
    have h1 := h.trans (discr_dvd_discr H.E (CyclotomicField H.condN ℚ))
    rw [Int.natCast_dvd, IsCyclotomicExtension.Rat.natAbs_discr H.condN] at h1
    exact hp.dvd_of_dvd_pow (h1.trans (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))))
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine dvd_discr_of_inertia Nat.prime_two fun P _ _ => ?_
    obtain ⟨u, hu, h1⟩ := exists_two H
    refine ⟨H.gal.symm (H.art u), fun h2 => h1 (H.gal.symm.map_eq_one_iff.mp h2), ?_⟩
    exact (C.inertia 2 P _).mpr ⟨u, mem_KK.mp hu, H.gal.apply_symm_apply _⟩
  · refine dvd_discr_of_inertia H.hyp.2.1 fun P _ _ => ⟨H.gal.symm φ.iod, fun h2 => ?_,
      (C.inertia_d P _).mpr (Or.inr (H.gal.apply_symm_apply _))⟩
    exact absurd (congrArg (fun g : φ.GG => g.1) (H.gal.symm.map_eq_one_iff.mp h2))
      (show ¬ ((1, -1) : G0) = 1 by decide)

theorem rd_ge (C : HostCore H) : (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d ≤ H.rd := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have h1 := le_SS H.art.ker (two_dvd H) H.hyp.2.1 (dvd_mul_left _ _) (by have := H.hyp.2.2.2.1; omega)
    (fun u hu => hcl_eq_one (by rw [← hH_art, MonoidHom.mem_ker.mp hu]; exact map_one _))
    (by rw [div_d]; exact half_le_rho _ (dvd_mul_right _ _) (exists_d H C))
  rw [← Real.log_le_log_iff (by positivity) (rd_pos H), log_rd_eq, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num), Real.log_sqrt hd.le, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div]
  exact h1

theorem rd_le : H.rd ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have hq : (0 : ℝ) < H.q := by exact_mod_cast H.hyp.1.pos
  have hS : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have h1 := SS_le H.art.ker ((dvd_pow_self 2 (by omega)).trans (two_dvd H)) H.hyp.1 H.hyp.2.1
    ((dvd_mul_left _ _).mul_right _) (dvd_mul_left _ _) (by have := H.hyp.2.2.1; omega)
    (by have := H.hyp.2.2.2.1; omega) (q_ne_d H) (rho_q H) (rho_d H)
  have hN : Real.log (H.condN : ℝ) = Real.log H.QS + Real.log H.q + Real.log H.d := by
    rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) hd.ne', Real.log_mul hS.ne' hq.ne']
  rw [hN] at h1
  rw [← Real.log_le_log_iff (rd_pos H) (by positivity), log_rd_eq, Real.log_mul (by positivity) (by positivity),
    Real.log_div hS.ne' (by norm_num), Real.log_sqrt (by positivity), Real.log_mul hq.ne' hd.ne']
  linarith

theorem rd_sq_ge (C : HostCore H) : (4 * φ.ord : ℝ) ≤ H.rd ^ 2 := by
  have h1 := log_index_le H.art.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr C.art_surj, Subgroup.card_top, φ.natCard_GG] at h1
  have h0 : (0 : ℝ) < φ.ord := by exact_mod_cast φ.ord_pos
  rw [← Real.log_le_log_iff (by positivity) (pow_pos (rd_pos H) 2), Real.log_pow, log_rd_eq]
  exact_mod_cast h1

end Formalism.HC.Der

end
