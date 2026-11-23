import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycLift

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem root_eq_of_sub_mem {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ}
    (hm : (m : S) ∉ P) {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hgeom := geom_sum₂_mul x y m
  rw [hx, hy, sub_self] at hgeom
  rcases mul_eq_zero.1 hgeom with hG | hG
  · exfalso
    have hq : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.2 hxy
    have h1 := congrArg (Ideal.Quotient.mk P) hG
    rw [map_sum, map_zero] at h1
    simp only [map_mul, map_pow, hq] at h1
    have h2 : ∀ i ∈ Finset.range m, (Ideal.Quotient.mk P y) ^ i * (Ideal.Quotient.mk P y) ^ (m - 1 - i) =
        (Ideal.Quotient.mk P y) ^ (m - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h3 | h3
    · apply hm
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact h3
    · have h4 : (Ideal.Quotient.mk P y) ^ m = 1 := by rw [← map_pow, hy, map_one]
      have h5 : (Ideal.Quotient.mk P y) ^ m = 0 := by
        rw [show m = m - 1 + 1 by omega, pow_succ, h3, zero_mul]
      rw [h4] at h5
      exact one_ne_zero h5
  · exact sub_eq_zero.1 hG

theorem val_modEq_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) (x : ℕ) :
    (u : ZMod N).val ≡ x [MOD M] ↔ ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = (x : ZMod M) := by
  rw [show ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = ((u : ZMod N).val : ZMod M) from
    ZMod.cast_eq_val _, ZMod.natCast_eq_natCast_iff]

theorem val_modEq_one_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    (u : ZMod N).val ≡ 1 [MOD M] ↔ ZMod.unitsMap h u = 1 := by
  rw [val_modEq_iff h u 1, Nat.cast_one, Units.val_eq_one]

theorem exists_unit_modEq {M N : ℕ} [NeZero N] (h : M ∣ N) (x : ℕ) (hx : x.Coprime M) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD M] := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime x hx)
  exact ⟨u, (val_modEq_iff h u x).2 (by rw [hu, ZMod.coe_unitOfCoprime])⟩

section Cyc

variable (N : ℕ) [NeZero N]

def zO : 𝓞 (Cond.Cyc N) := (Cond.z_spec N).toInteger

theorem zO_prim : IsPrimitiveRoot (zO N) N := by
  exact (Cond.z_spec N).toInteger_isPrimitiveRoot

theorem tauN_zO (u : (ZMod N)ˣ) : tauN N u • zO N = zO N ^ (u : ZMod N).val := by
  apply RingOfIntegers.ext
  show (tauN N u) ((zO N : 𝓞 (Cond.Cyc N)) : Cond.Cyc N) =
    (((zO N) ^ (u : ZMod N).val : 𝓞 (Cond.Cyc N)) : Cond.Cyc N)
  push_cast
  exact tauN_root N u _ (Cond.z_spec N).pow_eq_one

theorem ringHom_ext_zO {R : Type*} [CommRing R] (f g : 𝓞 (Cond.Cyc N) →+* R) (h : f (zO N) = g (zO N))
    (x : 𝓞 (Cond.Cyc N)) : f x = g x := by
  have hx : x ∈ Algebra.adjoin ℤ {zO N} := by
    rw [show Algebra.adjoin ℤ {zO N} = ⊤ from IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (Cond.z_spec N)]
    exact Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun x _ => f x = g x) (fun y hy => ?_) (fun r => ?_)
    (fun y z _ _ h1 h2 => ?_) (fun y z _ _ h1 h2 => ?_) hx
  · rw [Set.mem_singleton_iff.1 hy]
    exact h
  · simp only [algebraMap_int_eq, eq_intCast, map_intCast]
  · rw [map_add, map_add, h1, h2]
  · rw [map_mul, map_mul, h1, h2]

variable (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime] [Q.LiesOver (span {(l : ℤ)})]

theorem charP_quot : CharP (𝓞 (Cond.Cyc N) ⧸ Q) l := by
  constructor
  intro x
  have hu : Q.under ℤ = span {(l : ℤ)} := (Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)})).symm
  rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem,
    show ((x : ℕ) : 𝓞 (Cond.Cyc N)) = algebraMap ℤ (𝓞 (Cond.Cyc N)) (x : ℤ) by simp, ← Ideal.mem_comap]
  change (x : ℤ) ∈ Q.under ℤ ↔ _
  rw [hu, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

theorem zO_sub_mem_iff (a b : ℕ) : zO N ^ a - zO N ^ b ∈ Q ↔ a ≡ b [MOD ordCompl[l] N] := by
  haveI := charP_quot N l Q
  have hl : l.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have hnN : ordProj[l] N * ordCompl[l] N = N := Nat.ordProj_mul_ordCompl_eq_self N l
  have hN'0 : 0 < ordCompl[l] N := Nat.ordCompl_pos l hN0
  have hζ := zO_prim N
  have key1 : ∀ c, Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) = 1 := by
    intro c
    have h1 : (Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) - 1) ^ (ordProj[l] N) = 0 := by
      rw [sub_pow_char_pow, ← map_pow, ← pow_mul, one_pow,
        show ordCompl[l] N * c * l ^ N.factorization l = N * c by
          rw [mul_right_comm, mul_comm (ordCompl[l] N), hnN],
        pow_mul, hζ.pow_eq_one, one_pow, map_one, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero)).1 h1)
  rw [← Ideal.Quotient.eq]
  constructor
  · intro h
    have h1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ (ordProj[l] N)) ^ b := by
      apply root_eq_of_sub_mem Q (m := ordCompl[l] N)
      · intro hmem
        have h2 : ((ordCompl[l] N : ℕ) : 𝓞 (Cond.Cyc N) ⧸ Q) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
          exact hmem
        rw [CharP.cast_eq_zero_iff _ l] at h2
        exact Nat.not_dvd_ordCompl hl hN0 h2
      · have ex : ordProj[l] N * (a * ordCompl[l] N) = N * a := by
          rw [mul_left_comm, hnN, mul_comm]
        rw [← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]
      · have ex : ordProj[l] N * (b * ordCompl[l] N) = N * b := by
          rw [mul_left_comm, hnN, mul_comm]
        rw [← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]
      · rw [← Ideal.Quotient.eq]
        have e1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ a) ^ (ordProj[l] N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        have e2 : (zO N ^ (ordProj[l] N)) ^ b = (zO N ^ b) ^ (ordProj[l] N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        rw [e1, e2, map_pow (Ideal.Quotient.mk Q) (zO N ^ a), map_pow (Ideal.Quotient.mk Q) (zO N ^ b), h]
    have hprim : IsPrimitiveRoot (zO N ^ (ordProj[l] N)) (ordCompl[l] N) :=
      hζ.pow_of_dvd (pow_ne_zero _ hl.ne_zero) (Nat.ordProj_dvd N l)
    have e : ∀ c, (zO N ^ (ordProj[l] N)) ^ c = (zO N ^ (ordProj[l] N)) ^ (c % ordCompl[l] N) := fun c => by
      conv_lhs => rw [← Nat.mod_add_div c (ordCompl[l] N), pow_add, pow_mul, hprim.pow_eq_one, one_pow, mul_one]
    rw [e a, e b] at h1
    exact hprim.pow_inj (Nat.mod_lt _ hN'0) (Nat.mod_lt _ hN'0) h1
  · intro h
    rcases le_total b a with hab | hab
    · obtain ⟨c, hc⟩ : ordCompl[l] N ∣ a - b := (Nat.modEq_iff_dvd' hab).1 h.symm
      have hac : a = b + ordCompl[l] N * c := by omega
      rw [hac, pow_add, map_mul, key1, mul_one]
    · obtain ⟨c, hc⟩ : ordCompl[l] N ∣ b - a := (Nat.modEq_iff_dvd' hab).1 h
      have hbc : b = a + ordCompl[l] N * c := by omega
      rw [hbc, pow_add, map_mul, key1, mul_one]

theorem tauN_inertia_iff (u : (ZMod N)ˣ) :
    (∀ y : 𝓞 (Cond.Cyc N), tauN N u • y - y ∈ Q) ↔ (u : ZMod N).val ≡ 1 [MOD ordCompl[l] N] := by
  constructor
  · intro h
    have h1 : zO N ^ (u : ZMod N).val - zO N ^ 1 ∈ Q := by
      rw [pow_one, ← tauN_zO]
      exact h _
    exact (zO_sub_mem_iff N l Q _ 1).1 h1
  · intro hu y
    have hfg := ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u)))
      (Ideal.Quotient.mk Q) ?_ y
    · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply] at hfg
      exact Ideal.Quotient.eq.1 hfg
    · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
      rw [tauN_zO]
      have h1 := (zO_sub_mem_iff N l Q _ 1).2 hu
      rw [pow_one] at h1
      exact Ideal.Quotient.eq.2 h1

theorem tauN_frob (u : (ZMod N)ˣ) (hu : (u : ZMod N).val ≡ l [MOD ordCompl[l] N]) : IsArithFrobAt ℤ (tauN N u) Q := by
  haveI := charP_quot N l Q
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = l := by
    rw [← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)}),
      Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]
  unfold IsArithFrobAt
  intro y
  rw [hcard]
  simp only [MulSemiringAction.toAlgHom_apply]
  have hfg := ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u)))
    ((frobenius (𝓞 (Cond.Cyc N) ⧸ Q) l).comp (Ideal.Quotient.mk Q)) ?_ y
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow] at hfg
    exact Ideal.Quotient.eq.1 hfg
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow]
    rw [tauN_zO]
    exact Ideal.Quotient.eq.2 ((zO_sub_mem_iff N l Q _ l).2 hu)

end Cyc

variable {φ : Frame} (H : HostRaw φ)

theorem inertia : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  have := cyc_isGalois H.condN
  obtain ⟨Q, _, _, h1, -⟩ := exists_over (emb H) l P
  rw [h1]
  constructor
  · rintro ⟨τ, h2, h3⟩
    obtain ⟨u, rfl⟩ := (tauN H.condN).surjective τ
    exact ⟨u, (tauN_inertia_iff _ l Q u).mp h3, (gal_eq_art_iff H σ u).mpr h2⟩
  · rintro ⟨u, h2, h3⟩
    exact ⟨_, (gal_eq_art_iff H σ u).mp h3, (tauN_inertia_iff _ l Q u).mpr h2⟩

private lemma lift_lemma' (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ Q : Ideal (𝓞 (Cond.Cyc H.condN)), Q.IsPrime ∧ Q.LiesOver (span {(l : ℤ)}) ∧
      Q.comap (RingOfIntegers.mapRingHom (emb H).toRingHom) = P := by
  classical
  letI : Algebra (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) := (RingOfIntegers.mapRingHom (emb H).toRingHom).toAlgebra
  haveI : Algebra.IsIntegral (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) :=
    ⟨fun y => (RingOfIntegers.isIntegral y).tower_top⟩
  have hinj : Function.Injective (RingOfIntegers.mapRingHom (emb H).toRingHom) := by
    intro x y hxy
    apply RingOfIntegers.ext
    have h1 := congrArg (fun z : 𝓞 (Cond.Cyc H.condN) => (z : Cond.Cyc H.condN)) hxy
    exact (emb H).toRingHom.injective h1
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 (Cond.Cyc H.condN))) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have hx0 : x = 0 := hinj (hx.trans (map_zero _).symm)
    rw [hx0]
    exact P.zero_mem)
  refine ⟨Q, hQp, ⟨?_⟩, hQ⟩
  have hP : span {(l : ℤ)} = P.under ℤ := Ideal.LiesOver.over
  rw [hP, ← hQ]
  show Ideal.comap (algebraMap ℤ (𝓞 H.E)) (Ideal.comap (algebraMap (𝓞 H.E) (𝓞 (Cond.Cyc H.condN))) Q) =
    Ideal.comap (algebraMap ℤ (𝓞 (Cond.Cyc H.condN))) Q
  rw [Ideal.comap_comap]
  congr 1
  exact RingHom.ext_int _ _

theorem frob_of_modEq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN])
    (h : H.gal σ = H.art u) : IsArithFrobAt ℤ σ P := by
  obtain ⟨Q, hQp, hQl, hQ⟩ := lift_lemma' H l P
  haveI := hQp
  haveI := hQl
  have hτ := tauN_frob H.condN l Q u hu
  have hact : ∀ x : 𝓞 H.E, RingOfIntegers.mapRingHom (emb H).toRingHom (σ • x) =
      tauN H.condN u • RingOfIntegers.mapRingHom (emb H).toRingHom x := by
    intro x
    apply RingOfIntegers.ext
    exact (gal_eq_art_iff H σ u).1 h x
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = Nat.card (ℤ ⧸ Q.under ℤ) := by
    rw [← Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)}), ← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)})]
  unfold IsArithFrobAt at hτ ⊢
  intro x
  rw [hcard, ← hQ, Ideal.mem_comap]
  simp only [MulSemiringAction.toAlgHom_apply] at hτ ⊢
  rw [map_sub, map_pow, hact]
  exact hτ _

theorem exists_frob (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ (F : H.E ≃ₐ[ℚ] H.E) (w : (ZMod H.condN)ˣ), IsArithFrobAt ℤ F P ∧
      (w : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal F = H.art w := by
  have hl : l.Prime := Fact.out
  have hcop : l.Coprime (ordCompl[l] H.condN) := Nat.coprime_ordCompl hl (NeZero.ne _)
  obtain ⟨w, hw⟩ := exists_unit_modEq (Nat.ordCompl_dvd H.condN l) l hcop
  exact ⟨H.gal.symm (H.art w), w, frob_of_modEq H l P _ w hw (by simp), hw, by simp⟩

theorem frob_any : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  refine ⟨fun hσ => ?_, fun ⟨u, h1, h2⟩ => frob_of_modEq H l P σ u h1 h2⟩
  obtain ⟨F, w, hF, hw, hFw⟩ := exists_frob H l P
  have hM := Nat.ordCompl_dvd H.condN l
  rw [frob_iff_inertia P F σ hF, inertia H l P, map_mul, map_inv, hFw] at hσ
  obtain ⟨u, hu, h1⟩ := hσ
  refine ⟨u * w, ?_, by rw [map_mul, ← h1, inv_mul_cancel_right]⟩
  rw [val_modEq_one_iff hM] at hu
  rw [val_modEq_iff hM] at hw ⊢
  rw [map_mul, hu, one_mul, hw]

theorem decomp : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), σ ∈ MulAction.stabilizer _ P ↔
      ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  obtain ⟨F, w, hF, hw, hFw⟩ := exists_frob H l P
  have hM := Nat.ordCompl_dvd H.condN l
  rw [val_modEq_iff hM] at hw
  constructor
  · intro hσ
    obtain ⟨k, ρ, hρ, rfl⟩ := Decomp.stab_eq_inertia_mul l P F σ hF hσ
    obtain ⟨u, hu, h1⟩ := (inertia H l P ρ).mp hρ
    refine ⟨u * w ^ k, k, ?_, by rw [map_mul, map_mul, map_pow, map_pow, h1, hFw]⟩
    rw [val_modEq_one_iff hM] at hu
    rw [val_modEq_iff hM, map_mul, hu, one_mul, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow]
  · rintro ⟨u, k, hu, h1⟩
    have h2 : ∀ x : 𝓞 H.E, (σ * (F ^ k)⁻¹) • x - x ∈ P := by
      rw [inertia H l P]
      refine ⟨u * (w ^ k)⁻¹, ?_, by rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, h1, hFw]⟩
      rw [val_modEq_iff hM] at hu
      have h3 : ZMod.unitsMap hM u = ZMod.unitsMap hM (w ^ k) :=
        Units.ext (by rw [hu, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow])
      rw [val_modEq_one_iff hM, map_mul, map_inv, h3, mul_inv_cancel]
    have h4 := Subgroup.mul_mem _ (Decomp.mem_stab_of _ P (smul_mem_of_inertia _ P h2))
      (Subgroup.pow_mem _ hF.mem_stabilizer k)
    rwa [inv_mul_cancel_right] at h4

end Formalism.HC.Der

end
