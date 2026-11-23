import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSl
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.BasicNotions

theorem mod_eq_one_of_dvd {N M a : ℕ} (h : N % M = 1) (ha : a ∣ M) (h1 : 1 < a) : N % a = 1 := by
  rw [← Nat.mod_mod_of_dvd N ha, h]
  exact Nat.mod_eq_of_lt h1

theorem jacobi_neg_eq_one {d N : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (h4 : N % 4 = 1) (hdN : N % d = 1) :
    jacobiSym (-(d : ℤ)) N = 1 := by
  have hNodd : Odd N := Nat.odd_iff.2 (by omega)
  have hdodd : Odd d := hd.odd_of_ne_two hd2
  rw [jacobiSym.neg _ hNodd, ZMod.χ₄_nat_one_mod_four h4, one_mul,
    ← jacobiSym.quadratic_reciprocity_one_mod_four h4 hdodd]
  have hm : (N : ℤ) % (d : ℤ) = 1 := by
    rw [← Int.natCast_mod, hdN]
    rfl
  rw [jacobiSym.mod_left, hm, jacobiSym.one_left]

theorem excSplit_of_g_mod {D : D7} (L : SizeData₂ D) (hg : ∀ i, D.host.g i % LevelStarExponents.condE D = 1) :
    Formalism.MainNotions.J.ExcSplit L := by
  intro u p hp hE
  by_cases hpd : p = D.host.d
  · exact Or.inl hpd
  right
  have hq := D.q_prime
  have hd := D.d_prime
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hd2 : D.host.d ≠ 2 := by omega
  have hjac : ∀ N : ℕ, N % (D.host.QS * D.host.q * D.host.d) = 1 →
      jacobiSym (-(D.host.d : ℤ)) N = 1 := by
    intro N hN
    exact jacobi_neg_eq_one hd hd2
      (mod_eq_one_of_dvd hN ((((show 4 ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd).mul_right _).mul_right _) (by norm_num))
      (mod_eq_one_of_dvd hN (Dvd.intro_left _ rfl) hd.one_lt)
  have key : p ∈ D.host.small ∨ p = D.host.q ∨ jacobiSym (-(D.host.d : ℤ)) p = 1 := by
    unfold Formalism.MainNotions.LocalQuadraticParts.Exc at hE
    rcases (Nat.Prime.dvd_mul hp).1 hE with h | hT
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | hG
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | hd'
        · rcases (Nat.Prime.dvd_mul hp).1 h with h2 | hq'
          · exact Or.inl (Nat.mem_primeFactors.2 ⟨hp, h2, D.host.QS_pos.ne'⟩)
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 hq'))
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hd).1 hd') hpd
      · obtain ⟨g, hgm, hpg⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hG
        have hgi : ∃ i, g = D.host.g i := by
          simp only [SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton] at hgm
          rcases hgm with h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩
        obtain ⟨i, rfl⟩ := hgi
        have hpe := (Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime i)).1 hpg
        subst hpe
        exact Or.inr (Or.inr (hjac _ (by have h := hg i; unfold LevelStarExponents.condE at h; exact h)))
    · have hpe := (Nat.prime_dvd_prime_iff_eq hp (D.mem u).A.T_prime).1 hT
      subst hpe
      exact Or.inr (Or.inr (hjac _ (D.T_mod_cond u)))
  have hcls : D.host.cls p = PrimeClass.ram2 ∨ D.host.cls p = PrimeClass.ramQ ∨
      D.host.cls p = PrimeClass.splitK := by
    unfold Host.cls primeClass
    by_cases h1 : p ∈ D.host.small
    · rw [if_pos h1]; exact Or.inl rfl
    by_cases h2 : p = D.host.q
    · rw [if_neg h1, if_pos h2]; exact Or.inr (Or.inl rfl)
    rw [if_neg h1, if_neg h2, if_neg hpd, if_pos ((key.resolve_left h1).resolve_left h2)]
    exact Or.inr (Or.inr rfl)
  intro hin
  unfold Formalism.MainNotions.InertK at hin
  rcases hcls with h | h | h <;> rw [h] at hin <;> rcases hin with hin | hin <;> cases hin

theorem excSplit_large {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.J.ExcSplit (Fm.L x i) :=
  ⟨Fm.x1 + 1, fun x hx i => excSplit_of_g_mod (Fm.L x i) (Fm.params x (by linarith) i).g_mod⟩

end Formalism.MainNotions.DIV.Proofs

end
