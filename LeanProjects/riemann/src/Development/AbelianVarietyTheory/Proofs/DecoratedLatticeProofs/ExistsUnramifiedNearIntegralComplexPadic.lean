import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.ResidueUnr

open Polynomial

local notation "PX" => (Polynomial.X)
local notation "PC" => (Polynomial.C)

variable {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_padicInt (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  exact z.norm_le_one

theorem norm_aeval_le (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) (g : ℤ_[l][X]) : ‖aeval x g‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro i _
  rw [Algebra.smul_def, norm_mul, norm_pow]
  exact mul_le_one₀ (norm_algebraMap_padicInt _) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hx)

theorem norm_aeval_lt (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) (g : ℤ_[l][X])
    (hg : g.map (PadicInt.toZMod (p := l)) = 0) : ‖aeval x g‖ < 1 := by
  have hd : ∀ n, (PC (l : ℤ_[l])) ∣ PC (g.coeff n) := by
    intro n
    have h0 : PadicInt.toZMod (g.coeff n) = 0 := by
      have := congrArg (fun f => Polynomial.coeff f n) hg
      simpa [Polynomial.coeff_map] using this
    have hm : g.coeff n ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [← PadicInt.ker_toZMod]; exact h0
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
    exact map_dvd PC hm
  obtain ⟨h, rfl⟩ : (PC (l : ℤ_[l])) ∣ g := (Polynomial.C_dvd_iff_dvd_coeff _ _).2
    (fun n => by simpa using (Polynomial.C_dvd_iff_dvd_coeff _ _).1 (hd n) 0)
  rw [map_mul, aeval_C, norm_mul]
  have hl : ‖algebraMap ℤ_[l] (PadicAlgCl l) (l : ℤ_[l])‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  calc _ ≤ ‖algebraMap ℤ_[l] (PadicAlgCl l) (l : ℤ_[l])‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_aeval_le x hx h) (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hl

theorem exists_monic (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) : ∃ q : ℤ_[l][X], q.Monic ∧ aeval x q = 0 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at hx
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hx n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem exists_pow_near_one (x : PadicAlgCl l) (hx : ‖x‖ = 1) :
    ∃ m : ℕ, 0 < m ∧ ‖x ^ m - 1‖ < 1 := by
  obtain ⟨q, hqm, hq⟩ := exists_monic x hx.le
  have hq1 : q ≠ 1 := by rintro rfl; simp at hq
  set d := q.natDegree
  let r : ℕ → ℤ_[l][X] := fun k => (PX ^ k) %ₘ q
  have hr : ∀ k, aeval x (r k) = x ^ k := by
    intro k
    have h := congrArg (aeval x) (modByMonic_add_div (PX ^ k : ℤ_[l][X]) q)
    simpa [hq] using h
  have hdeg : ∀ k, (r k).natDegree < d := fun k => natDegree_modByMonic_lt _ hqm hq1
  let F : ℕ → (Fin d → ZMod l) := fun k i => PadicInt.toZMod ((r k).coeff i)
  obtain ⟨i, j, hij, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  have key : ∀ a b : ℕ, F a = F b → a < b → ∃ m : ℕ, 0 < m ∧ ‖x ^ m - 1‖ < 1 := by
    intro a b hab hlt
    have hsm : ‖x ^ b - x ^ a‖ < 1 := by
      rw [← hr b, ← hr a, ← map_sub]
      apply norm_aeval_lt x hx.le
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_sub, map_sub, Polynomial.coeff_zero]
      by_cases hn : n < d
      · have := congrFun hab ⟨n, hn⟩
        rw [sub_eq_zero]
        exact this.symm
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg b) (not_lt.1 hn)),
          coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg a) (not_lt.1 hn))]
        simp
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
    rw [e, norm_mul, norm_pow, hx, one_pow, one_mul] at hsm
    exact hsm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j hF h
  · exact key j i hF.symm h

theorem frob_inj (z : PadicAlgCl l) (hz : ‖z‖ ≤ 1) (h : ‖z ^ l - 1‖ < 1) : ‖z - 1‖ < 1 := by
  have hp := (Fact.out : l.Prime)
  have hpoly : (((PX - 1) ^ l - (PX ^ l - 1) : ℤ_[l][X])).map (PadicInt.toZMod (p := l)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, sub_pow_char, one_pow, sub_self]
  have h1 := norm_aeval_lt z hz _ hpoly
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at h1
  have h2 : ‖(z - 1) ^ l‖ < 1 := by
    have e : (z - 1) ^ l = ((z - 1) ^ l - (z ^ l - 1)) + (z ^ l - 1) := by ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 h2

theorem frob_pow (a : ℕ) : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖z ^ (l ^ a) - 1‖ < 1 → ‖z - 1‖ < 1 := by
  induction a with
  | zero => intro z _ h; simpa using h
  | succ a ih =>
    intro z hz h
    apply frob_inj z hz
    apply ih (z ^ l) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz)
    rw [← pow_mul, ← pow_succ']
    exact h

theorem one_le_norm_prod (s : Multiset ℂ_[l]) (h : ∀ a ∈ s, 1 ≤ ‖a‖) : 1 ≤ ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun b hb => h b (Multiset.mem_cons_of_mem hb)
    nlinarith

theorem exists_root_near (x : ℂ_[l]) (m : ℕ) (hm : 0 < m) (h : ‖x ^ m - 1‖ < 1) :
    ∃ ζ : ℂ_[l], ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  set P : ℂ_[l][X] := PX ^ m - PC 1
  have hPm : P.Monic := monic_X_pow_sub_C 1 hm.ne'
  have hcard : Multiset.card P.roots = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm hcard
  have hev := congrArg (eval x) hprod
  rw [eval_multiset_prod, Multiset.map_map] at hev
  by_contra hne
  push_neg at hne
  have hall : ∀ a ∈ P.roots, 1 ≤ ‖x - a‖ := by
    intro a ha
    apply hne a _
    have := (mem_roots hPm.ne_zero).1 ha
    simpa [P, sub_eq_zero] using this
  have := one_le_norm_prod (P.roots.map fun a => x - a) (by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    exact hall a ha)
  have e : (Multiset.map (eval x ∘ fun a => PX - PC a) P.roots).prod = (P.roots.map fun a => x - a).prod := by
    congr 1
    exact Multiset.map_congr rfl (fun a _ => by simp)
  rw [e] at hev
  rw [hev] at this
  simp [P] at this
  linarith

theorem exists_near_kur : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]), ‖x‖ ≤ 1 →
    ∃ y ∈ MaximalUnramifiedExtension l, ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1 := by
  intro l _ x hx
  obtain ⟨x', hx'⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x one_pos
  rw [dist_eq_norm] at hx'
  set X0 : ℂ_[l] := (x' : ℂ_[l]) with hX0
  have hn' : ‖X0‖ ≤ 1 := by
    have e : X0 = (X0 - x) + x := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_sub_rev]; exact hx'.le) hx)
  by_cases h0 : ‖X0‖ < 1
  · refine ⟨0, zero_mem _, by simp, ?_⟩
    rw [sub_zero]
    have e : x = (x - X0) + X0 := by ring
    rw [e]; exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx' h0)
  have h1 : ‖x'‖ = 1 := by rw [← PadicComplex.norm_extends]; exact le_antisymm hn' (not_lt.1 h0)
  obtain ⟨m0, hm0, hsm⟩ := exists_pow_near_one x' h1
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' l (Fact.out : l.Prime).ne_one
  have hz : ‖x' ^ m - 1‖ < 1 :=
    frob_pow a (x' ^ m) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h1.le) (by rw [← pow_mul, mul_comm]; exact hsm)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
  have hz' : ‖X0 ^ m - 1‖ < 1 := by
    have e : X0 ^ m - 1 = ((x' ^ m - 1 : PadicAlgCl l) : ℂ_[l]) := by simp [hX0, PadicComplex.coe_eq]
    rw [e, PadicComplex.norm_extends]; exact hz
  obtain ⟨ζ, hζ, hd⟩ := exists_root_near X0 m hmpos hz'
  refine ⟨ζ, ?_, ?_, ?_⟩
  · unfold MaximalUnramifiedExtension
    exact Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hmpos, hm, hζ⟩)
  · have : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζ, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hmpos.ne').1 this).le
  · have e : x - ζ = (x - X0) + (X0 - ζ) := by ring
    rw [e]; exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx' hd)

end GlobalTheory.ResidueUnr
