import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFormula
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nf_nu_le {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_nu_iff] at hn
  exact le_emultiplicity_of_pow_dvd (hn u hu)

private theorem nf_exists_unit {a : ℕ} (ha : 1 ≤ a) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a := by
  have h : IsUnit (1 + (l : ℤ_[l]) ^ a) := by
    by_contra hn
    have h1 : ‖1 + (l : ℤ_[l]) ^ a‖ < 1 := PadicInt.not_isUnit_iff.mp hn
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    have h2 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ a := dvd_pow_self _ (by omega)
    exact PadicInt.prime_p.not_dvd_one ((dvd_add_left h2).mp h1)
  exact ⟨h.unit, by simp⟩

private theorem nf_mem_princ {a s : ℕ} (h : s ≤ a) {u : ℤ_[l]ˣ}
    (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) : u ∈ princ l s := by
  rw [mem_princ, hu]
  exact pow_dvd_pow _ h

private theorem nf_emult {a : ℕ} {u : ℤ_[l]ˣ} (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) :
    emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a := by
  rw [hu, emultiplicity_pow_self_of_prime PadicInt.prime_p]

theorem depth_le_of_princ_le {U : Subgroup ℤ_[l]ˣ} {s : ℕ} (h : princ l s ≤ U) :
    depth l U ≤ ((max 1 s : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := nf_exists_unit (l := l) (le_max_left 1 s)
  have hm : u ∈ U ⊓ princ l 1 :=
    ⟨h (nf_mem_princ (le_max_right 1 s) hu), nf_mem_princ (le_max_left 1 s) hu⟩
  have := nf_nu_le hm 1
  rwa [pow_one, nf_emult hu] at this

theorem nu_le_of_princ_le {U : Subgroup ℤ_[l]ˣ} {s tr : ℕ} (h : princ l s ≤ U) (htr : Odd tr) :
    nu l U tr ≤ ((max 1 s + padicValNat l tr : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := nf_exists_unit (l := l) (le_max_left 1 s)
  have hm : u ∈ U := h (nf_mem_princ (le_max_right 1 s) hu)
  by_cases hl : l = 2
  · subst hl
    rw [(nu_two_of_odd U htr).1]
    have := nf_nu_le hm 1
    rw [pow_one, nf_emult hu] at this
    exact this.trans (by exact_mod_cast Nat.le_add_right _ _)
  · have h1 : (l : ℤ_[l]) ∣ (u : ℤ_[l]) - 1 := by
      rw [hu]
      exact dvd_pow_self _ (by omega)
    have := nf_nu_le hm tr
    rw [emultiplicity_pow_sub_one_odd hl h1, nf_emult hu,
      ← padicValNat_eq_emultiplicity htr.pos.ne'] at this
    rw [Nat.cast_add]
    exact this

theorem nu_ne_top {U : Subgroup ℤ_[l]ˣ} (hU : IsOpen (U : Set ℤ_[l]ˣ)) {tr : ℕ} (htr : tr ≠ 0) :
    nu l U tr ≠ ⊤ := by
  obtain ⟨s, h⟩ := (isOpen_iff_princ_le U).mp hU
  obtain ⟨u, hu⟩ := nf_exists_unit (l := l) (a := s + 2) (by omega)
  have hm : u ∈ U := h (nf_mem_princ (by omega) hu)
  have h1 : (l : ℤ_[l]) ^ 2 ∣ (u : ℤ_[l]) - 1 := by
    rw [hu]
    exact pow_dvd_pow _ (by omega)
  have := nf_nu_le hm tr
  rw [emultiplicity_pow_sub_one_sq h1, nf_emult hu,
    ← padicValNat_eq_emultiplicity htr, ← Nat.cast_add] at this
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) this

private theorem nf_not_dvd_two (hl : l ≠ 2) : ¬ (l : ℤ_[l]) ∣ 2 := by
  intro h
  have h2 : (l : ℤ_[l]) ∣ ((2 : ℕ) : ℤ_[l]) := by simpa using h
  rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff] at h2
  exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)

theorem nu_of_neg_one_mem {U : Subgroup ℤ_[l]ˣ} (h : -1 ∈ U) {tr : ℕ} (htr : Odd tr) :
    nu l U tr = (if l = 2 then 1 else 0) ∧ (l ≠ 2 → Even (resOrder l U)) := by
  have key : ∀ {t : ℕ}, Odd t → nu l U t ≤ emultiplicity (l : ℤ_[l]) 2 := by
    intro t ht
    have := nf_nu_le h t
    have e : (((-1 : ℤ_[l]ˣ)) : ℤ_[l]) ^ t - 1 = -2 := by
      rw [Units.val_neg, Units.val_one, ht.neg_one_pow]; ring
    rwa [e, emultiplicity_neg] at this
  have odd : l ≠ 2 → ∀ {t : ℕ}, Odd t → nu l U t = 0 := by
    intro hl t ht
    have := key ht
    rw [emultiplicity_eq_zero.2 (nf_not_dvd_two hl)] at this
    exact le_antisymm this bot_le
  refine ⟨?_, fun hl => ?_⟩
  · split_ifs with hl
    · subst hl
      refine le_antisymm ?_ (nu_two_of_odd U htr).2
      have hs : emultiplicity ((2 : ℕ) : ℤ_[2]) 2 = 1 := by
        simpa using emultiplicity_pow_self_of_prime (PadicInt.prime_p (p := 2)) 1
      exact hs ▸ key htr
    · exact odd hl htr
  · by_contra hn
    have h0 := odd hl (Nat.not_even_iff_odd.mp hn)
    have := (nu_pos_iff U (resOrder l U)).mpr dvd_rfl
    exact this.ne' h0

end KStar.TotallyRealRoots
