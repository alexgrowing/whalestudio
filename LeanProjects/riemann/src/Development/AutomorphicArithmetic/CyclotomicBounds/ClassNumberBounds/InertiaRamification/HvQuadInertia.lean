import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ConductorDvdFieldConductorOfMem
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Places
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ResDeg
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bounds

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] {n d q₁ : ℕ} {ch ps : DirichletCharacter ℂ N}
  {Y : Subgroup (DirichletCharacter ℂ N)}

private theorem hv_unr_iff (l : ℕ) [Fact l.Prime] (X : Subgroup (DirichletCharacter ℂ N)) :
    (∀ ψ ∈ X, ¬ l ∣ ψ.conductor) ↔ X ≤ (localPart N l).ker := by
  constructor
  · intro h ψ hψ
    exact (MonoidHom.mem_ker).2 ((localPart_eq_one_iff l ψ).2.2 (h ψ hψ))
  · intro h ψ hψ
    exact (localPart_eq_one_iff l ψ).2.1 ((MonoidHom.mem_ker).1 (h hψ))

private theorem hv_unr_sup (l : ℕ) [Fact l.Prime] {X Y : Subgroup (DirichletCharacter ℂ N)}
    (hX : ∀ ψ ∈ X, ¬ l ∣ ψ.conductor) (hY : ∀ ψ ∈ Y, ¬ l ∣ ψ.conductor) :
    ∀ ψ ∈ X ⊔ Y, ¬ l ∣ ψ.conductor :=
  (hv_unr_iff l _).2 (sup_le ((hv_unr_iff l _).1 hX) ((hv_unr_iff l _).1 hY))

private theorem hv_unr_zpowers (l : ℕ) [Fact l.Prime] {φ : DirichletCharacter ℂ N}
    (h : ¬ l ∣ φ.conductor) : ∀ ψ ∈ Subgroup.zpowers φ, ¬ l ∣ ψ.conductor :=
  (hv_unr_iff l _).2 ((Subgroup.zpowers_le).2
    ((MonoidHom.mem_ker).2 ((localPart_eq_one_iff l φ).2.2 h)))

omit [NeZero N] in
private theorem hv_closure_pair (ch ps : DirichletCharacter ℂ N) :
    Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)) =
      Subgroup.zpowers ch ⊔ Subgroup.zpowers ps := by
  rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure]

omit [NeZero N] in
private theorem hv_not_dvd {l d : ℕ} (hl : l.Prime) (hd : d.Prime) (hne : l ≠ d)
    {ch : DirichletCharacter ℂ N} (h : IsImagQuad ch d) : ¬ l ∣ ch.conductor := by
  rw [h.2.2]
  exact fun h' => hne ((Nat.prime_dvd_prime_iff_eq hl hd).1 h')

omit [NeZero N] in
private theorem hv_mem (n : ℕ) (ch ps : DirichletCharacter ℂ N)
    (Y : Subgroup (DirichletCharacter ℂ N)) :
    ch ∈ hostCharsOf n ch ps Y ∧ ps ∈ hostCharsOf n ch ps Y ∧
      evenPart (condDvd N (4 * n)) ≤ hostCharsOf n ch ps Y :=
  ⟨Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)),
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)),
    le_sup_of_le_right le_sup_left⟩

private theorem hv_arith1 {n f g r : ℕ} (hn : 0 < n) (h : n * f * g = 4 * n * r) :
    g * f = 4 * r := by
  apply Nat.eq_of_mul_eq_mul_left hn
  linarith

private theorem hv_arith2 {f g r : ℕ} (h : 2 * g * f = 4 * r) : g * f = 2 * r := by
  linarith

omit [NeZero N] in
private theorem hv_mem_charKer (X : Subgroup (DirichletCharacter ℂ N)) (u : (ZMod N)ˣ) :
    u ∈ charKer X ↔ ∀ ψ ∈ X, ψ (u : ZMod N) = 1 := by
  simp only [charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, ← Units.val_eq_one,
    MulChar.coe_toUnitHom]

private theorem hv_inertia (l : ℕ) [Fact l.Prime] (X : Subgroup (DirichletCharacter ℂ N)) :
    inertiaUnits N l ⊔ charKer X = charKer (X ⊓ (localPart N l).ker) := by
  rw [← (annihilator_charKer ⊥ (inertiaUnits N l ⊔ charKer X)).2.1]
  congr 1
  ext ψ
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, (localPart_eq_one_iff l ψ).1, mem_annihilator_iff]
  constructor
  · intro h
    refine ⟨?_, fun u hu => h u (Subgroup.mem_sup_left hu)⟩
    rw [← (annihilator_charKer X ⊥).1, mem_annihilator_iff]
    exact fun u hu => h u (Subgroup.mem_sup_right hu)
  · rintro ⟨hX, hI⟩ u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    rw [Units.val_mul, map_mul, hI a ha, (hv_mem_charKer X b).1 hb ψ hX, one_mul]

private theorem hv_inertia_sup (l : ℕ) [Fact l.Prime] (A B : Subgroup (DirichletCharacter ℂ N))
    (hA : ∀ ψ ∈ A, ¬ l ∣ ψ.conductor) :
    inertiaUnits N l ⊔ charKer (A ⊔ B) = charKer (A ⊔ (B ⊓ (localPart N l).ker)) := by
  rw [hv_inertia, sup_inf_assoc_of_le _ ((hv_unr_iff l A).1 hA)]

private theorem hv_card (l : ℕ) [Fact l.Prime] (X : Subgroup (DirichletCharacter ℂ N)) :
    ramIdx l X * Nat.card ↥(X ⊓ (localPart N l).ker) = Nat.card X := by
  unfold ramIdx
  rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_left, Subgroup.relIndex,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : X ⊓ (localPart N l).ker ≤ X)).toEquiv, Subgroup.index_mul_card]

private theorem hv_fieldCond_ne (X : Subgroup (DirichletCharacter ℂ N)) : fieldCond X ≠ 0 :=
  ne_zero_of_dvd_ne_zero (NeZero.ne N) (((fieldCond_sup X ⊥ 1).2.2 N).2
    fun ψ _ => (mem_condDvd_iff N ψ).1.2 ψ.conductor_dvd_level)

private theorem hv_two (e : ℕ) (Y : Subgroup (DirichletCharacter ℂ N)) :
    realCycSup (2 ^ e) Y ⊓ (localPart N 2).ker =
      realCycSup (2 ^ e) Y ⊓ condDvd N (ordCompl[2] (fieldCond Y)) := by
  ext ψ
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_right fun hψ => ?_
  rw [MonoidHom.mem_ker, (localPart_eq_one_iff 2 ψ).2, (mem_condDvd_iff _ ψ).1]
  constructor
  · intro h2
    have hle : realCycSup (2 ^ e) Y ≤ condDvd N (4 * 2 ^ e * fieldCond Y) := by
      refine sup_le (fun φ hφ => ?_) (((fieldCond_sup Y ⊥ 1).2.2 _).1 (dvd_mul_left _ _))
      exact (mem_condDvd_iff _ φ).1.2 (((mem_condDvd_iff (4 * 2 ^ e) φ).1.1
        (((card_evenPart _).1 φ).1 hφ).1).trans (dvd_mul_right _ _))
    have h1 := (mem_condDvd_iff _ ψ).1.1 (hle hψ)
    have hc : Nat.Coprime ψ.conductor (4 * 2 ^ e) := by
      rw [show 4 * 2 ^ e = 2 ^ (e + 2) by ring]
      exact Nat.Coprime.pow_right _ ((Nat.prime_two.coprime_iff_not_dvd.2 h2).symm)
    exact Nat.dvd_ordCompl_of_dvd_not_dvd (hc.dvd_of_dvd_mul_left h1) h2
  · intro h1 h2
    exact Nat.not_dvd_ordCompl Nat.prime_two (hv_fieldCond_ne Y) (h2.trans h1)

theorem HostDataOf.at_two (h : HostDataOf n d q₁ ch ps Y) :
    n ∣ ramIdx 2 (hostCharsOf n ch ps Y) ∧ 2 ∣ ramIdx 2 (hostCharsOf n ch ps Y) ∧
      inertiaUnits N 2 ⊔ charKer (hostCharsOf n ch ps Y) =
        charKer (Subgroup.closure {ch, ps} ⊔
          (realCycSup n Y ⊓ condDvd N (ordCompl[2] (fieldCond Y)))) ∧
      ramIdx 2 (hostCharsOf n ch ps Y) *
          Nat.card ↥(realCycSup n Y ⊓ condDvd N (ordCompl[2] (fieldCond Y))) =
        Nat.card (realCycSup n Y) ∧
      resDeg 2 (hostCharsOf n ch ps Y) = Nat.lcm 2 (resDeg 2 (realCycSup n Y)) ∧
      (¬ 2 ∣ fieldCond Y →
        ramIdx 2 (hostCharsOf n ch ps Y) = n ∧
        resDeg 2 (hostCharsOf n ch ps Y) = Nat.lcm 2 (resDeg 2 Y) ∧
        numPlaces 2 (hostCharsOf n ch ps Y) * Nat.lcm 2 (resDeg 2 Y) = 4 * Nat.card Y ∧
        numPlaces 2 (evenPart (hostCharsOf n ch ps Y)) * Nat.lcm 2 (resDeg 2 Y) =
          2 * Nat.card Y) := by
  obtain ⟨-, s, o, -, hs, ho, -, -, hc, -⟩ := h.card
  obtain ⟨⟨e, he, rfl⟩, hN, hd, hd16, hq, hq8, hch, hps, hY'⟩ := h
  obtain ⟨m1, m2, m3⟩ := hv_mem (2 ^ e) ch ps Y
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  have hF := (fieldCond_evenPart_condDvd_two_pow (N := N) (k := e + 2) (h4 ▸ hN) (by omega)).2
  rw [← h4, Nat.add_sub_cancel] at hF
  have hdv : 2 ^ e ∣ ramIdx 2 (hostCharsOf (2 ^ e) ch ps Y) := by
    have hdv : ramIdx 2 (evenPart (condDvd N (4 * 2 ^ e))) ∣
        ramIdx 2 (hostCharsOf (2 ^ e) ch ps Y) :=
      Subgroup.card_dvd_of_le (Subgroup.map_mono m3)
    rwa [hF.1] at hdv
  have u1 := hv_not_dvd Nat.prime_two hd (by omega) hch
  have u2 := hv_not_dvd Nat.prime_two hq (by omega) hps
  have uE := hv_unr_sup 2 (hv_unr_zpowers 2 u1) (hv_unr_zpowers 2 u2)
  obtain ⟨v1, v2, -⟩ := IsImagQuad.values hd hq (by omega) hq8 hch hps
  have hneg : orderOf (-1 : ℂ) = 2 := by
    apply orderOf_eq_prime
    · norm_num
    · norm_num
  have e0 : hostCharsOf (2 ^ e) ch ps Y =
      (Subgroup.zpowers ch ⊔ Subgroup.zpowers ps) ⊔ realCycSup (2 ^ e) Y := by
    rw [hostCharsOf, hv_closure_pair]
  have hr0 : ramIdx 2 (hostCharsOf (2 ^ e) ch ps Y) = ramIdx 2 (realCycSup (2 ^ e) Y) := by
    rw [e0, (resDeg_sup 2 _ _ uE).2.1]
  have hf0 : resDeg 2 (hostCharsOf (2 ^ e) ch ps Y) =
      Nat.lcm 2 (resDeg 2 (realCycSup (2 ^ e) Y)) := by
    rw [e0, (resDeg_sup 2 _ _ uE).1,
      (resDeg_sup 2 _ _ (hv_unr_zpowers 2 u1)).1, resDeg_zpowers 2 ch u1, resDeg_zpowers 2 ps u2,
      show ch.primitiveCharacter ((2 : ℕ) : ZMod ch.conductor) = 1 from v1, orderOf_one,
      Nat.lcm_one_left, v2, hneg]
  refine ⟨hdv, (dvd_pow_self 2 (by omega)).trans hdv, ?_, ?_, hf0, fun h2 => ?_⟩
  · rw [e0, hv_inertia_sup 2 _ _ uE, hv_two, hv_closure_pair]
  · rw [hr0, ← hv_two, hv_card]
  have uY : ∀ ψ ∈ Y, ¬ 2 ∣ ψ.conductor :=
    (ramIdx_eq_one_iff 2 Y).1.1 ((ramIdx_eq_one_iff 2 Y).2.1.2 h2)
  have e1 : realCycSup (2 ^ e) Y = Y ⊔ evenPart (condDvd N (4 * 2 ^ e)) := sup_comm _ _
  have hr : ramIdx 2 (hostCharsOf (2 ^ e) ch ps Y) = 2 ^ e := by
    rw [hr0, e1, (resDeg_sup 2 _ _ uY).2.1, hF.1]
  have hf : resDeg 2 (hostCharsOf (2 ^ e) ch ps Y) = Nat.lcm 2 (resDeg 2 Y) := by
    rw [hf0, e1, (resDeg_sup 2 _ _ uY).1, hF.2, Nat.lcm_one_right]
  have hc0 : (fieldCond Y).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2
  have hs0 : s = 0 := by omega
  rw [hs0, pow_zero, one_mul] at ho
  have hp := ramIdx_mul_resDeg_mul_numPlaces 2 (hostCharsOf (2 ^ e) ch ps Y)
  rw [hr, hf, hc, ← ho] at hp
  have hg := hv_arith1 (Nat.two_pow_pos e) hp
  refine ⟨hr, hf, hg, ?_⟩
  rw [(split_of_splitsFor 2 _ m1 hch.2.1 v1).2.2.1] at hg
  exact hv_arith2 hg

end KStar.Ram
