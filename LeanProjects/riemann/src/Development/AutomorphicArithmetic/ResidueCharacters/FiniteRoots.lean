import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial

namespace UpperTheory.N.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem finite_roots {M : ℕ} (hM : 0 < M) : {x : Om l | x ^ M = 1}.Finite := by
  classical
  refine (Polynomial.nthRoots M (1 : Om l)).toFinset.finite_toSet.subset fun x hx => ?_
  simpa [Polynomial.mem_nthRoots hM] using hx

def Kc (l : ℕ) [Fact l.Prime] (M : ℕ) (hM : 0 < M) : FinExt l :=
  ⟨IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}, by
    haveI := (finite_roots (l := l) hM).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩

theorem map_mem {M : ℕ} (hM : 0 < M) (S : IntermediateField ℚ_[l] (Om l)) (hS : ∀ x : Om l, x ^ M = 1 → x ∈ S)
    (σ : Om l →ₐ[ℚ_[l]] Om l) (x : Om l) (hx : x ∈ (Kc l M hM).1) : σ x ∈ S := by
  have key : (Kc l M hM).1 ≤ S.comap σ := IntermediateField.adjoin_le_iff.2 fun y hy => by
    refine hS _ ?_
    have hy' : y ^ M = 1 := hy
    rw [← map_pow, hy', map_one]
  exact key hx

theorem finrank_le {M : ℕ} (hM : 0 < M) : Module.finrank ℚ_[l] ↥(Kc l M hM).1 ≤ M := by
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) M
  have e : (Kc l M hM).1 = IntermediateField.adjoin ℚ_[l] {z} := by
    apply le_antisymm
    · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
      obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one (show x ^ M = 1 from hx)
      exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
    · exact IntermediateField.adjoin.mono _ _ _ (by rintro x rfl; exact hz.pow_eq_one)
  rw [e, IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral z)]
  have hne : (X ^ M - C 1 : ℚ_[l][X]) ≠ 0 := X_pow_sub_C_ne_zero hM 1
  have := natDegree_le_of_dvd (minpoly.dvd ℚ_[l] z (p := X ^ M - C 1) (by simp [hz.pow_eq_one])) hne
  rwa [natDegree_X_pow_sub_C] at this

theorem Ks_eq {M M' s : ℕ} (hM : 0 < M) (hM' : M = l ^ s * M') (hl : ¬ l ∣ M') :
    Ks (Kc l M hM) s = (Kc l M hM).1 := by
  have hM'0 : 0 < M' := Nat.pos_of_ne_zero (by rintro rfl; simp at hl)
  apply le_antisymm
  · refine sup_le inf_le_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_)
    have hx' : x ^ (l ^ s) = 1 := hx
    show x ^ M = 1
    rw [hM', pow_mul, hx', one_pow]
  · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    have hx' : x ^ M = 1 := hx
    have hcop : Nat.Coprime (l ^ s) M' := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl)
    have h0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne'] at hx'
      exact zero_ne_one hx'
    have hb : ((1 : ℕ) : ℤ) = (l ^ s : ℕ) * Nat.gcdA (l ^ s) M' + M' * Nat.gcdB (l ^ s) M' := by
      rw [← Nat.gcd_eq_gcd_ab, hcop]
    have e : x = (x ^ (l ^ s)) ^ Nat.gcdA (l ^ s) M' * (x ^ M') ^ Nat.gcdB (l ^ s) M' := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ h0, ← hb]; simp
    have hxK : x ∈ (Kc l M hM).1 := IntermediateField.subset_adjoin _ _ hx
    have h1 : x ^ (l ^ s) ∈ Ks (Kc l M hM) s := by
      refine (le_sup_left : K0 _ ≤ _) ⟨pow_mem hxK _, IntermediateField.subset_adjoin _ _ ⟨M', hM'0, hl, ?_⟩⟩
      rw [← pow_mul, ← hM', hx']
    have h2 : x ^ M' ∈ Ks (Kc l M hM) s := by
      refine (le_sup_right : _ ≤ Ks _ s) (IntermediateField.subset_adjoin _ _ ?_)
      show (x ^ M') ^ (l ^ s) = 1
      rw [← pow_mul, mul_comm, ← hM', hx']
    show x ∈ Ks (Kc l M hM) s
    rw [e]
    exact mul_mem (zpow_mem h1 _) (zpow_mem h2 _)

theorem lcm_pos {N : ℕ} (hN : 0 < N) : 0 < Nat.lcm l N := Nat.lcm_pos (Fact.out : l.Prime).pos hN

theorem Ks_lcm {N : ℕ} (hN : 0 < N) :
    Ks (Kc l (Nat.lcm l N) (lcm_pos hN)) (max 1 (N.factorization l)) = (Kc l (Nat.lcm l N) (lcm_pos hN)).1 := by
  have hp : l.Prime := Fact.out
  have hf : (Nat.lcm l N).factorization l = max 1 (N.factorization l) := by
    rw [Nat.factorization_lcm hp.ne_zero hN.ne', Finsupp.sup_apply, hp.factorization_self]
  refine Ks_eq (M' := ordCompl[l] (Nat.lcm l N)) _ ?_ (Nat.not_dvd_ordCompl hp (lcm_pos hN).ne')
  rw [← hf, Nat.ordProj_mul_ordCompl_eq_self]

theorem good_lcm {N : ℕ} (hN : 0 < N) (h2 : l ≠ 2) (LL : FinExt l)
    (hLL : ∀ x : Om l, x ^ Nat.lcm l N = 1 → x ∈ LL.1) :
    Good (Kc l (Nat.lcm l N) (lcm_pos hN)) (max 1 (N.factorization l)) LL := by
  refine ⟨le_max_left _ _, fun e => absurd e h2, (Ks_lcm hN).ge, fun τ x => ?_⟩
  have e2 : τ.liftNormal (Om l) (x : Om l) = τ x := AlgHom.liftNormal_commutes τ (Om l) x
  rw [← e2]
  exact map_mem _ _ hLL _ _ ((Ks_lcm hN).le x.2)

theorem good_lcm' {N : ℕ} (hN : 0 < N) (h2 : l = 2 → 4 ∣ N) (LL : FinExt l)
    (hLL : ∀ x : Om l, x ^ Nat.lcm l N = 1 → x ∈ LL.1) :
    Good (Kc l (Nat.lcm l N) (lcm_pos hN)) (max 1 (N.factorization l)) LL := by
  refine ⟨le_max_left _ _, fun e => le_max_of_le_right ?_, (Ks_lcm hN).ge, fun τ x => ?_⟩
  · exact ((Fact.out : l.Prime).pow_dvd_iff_le_factorization hN.ne').1 (by rw [e]; exact h2 e)
  · have e2 : τ.liftNormal (Om l) (x : Om l) = τ x := AlgHom.liftNormal_commutes τ (Om l) x
    rw [← e2]
    exact map_mem _ _ hLL _ _ ((Ks_lcm hN).le x.2)

theorem GK_normal {M : ℕ} (hM : 0 < M) : (GK (Kc l M hM)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [GK, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  have h1 : g⁻¹ x ∈ (Kc l M hM).1 :=
    map_mem hM _ (fun y hy => IntermediateField.subset_adjoin _ _ hy) (g⁻¹ : GQ l).toAlgHom x hx
  show g (n (g⁻¹ x)) = x
  rw [hn _ h1]
  exact g.apply_symm_apply x

theorem range_normal {M : ℕ} (hM : 0 < M) (K : FinExt l) (hle : GK (Kc l M hM) ≤ GK K) :
    (Subgroup.inclusion hle).range.Normal := by
  rw [Subgroup.inclusion_range]
  exact (GK_normal hM).subgroupOf _

theorem val_index_le {N : ℕ} (hN : 0 < N) (d : ℕ) :
    padicValNat l (Module.finrank ℚ_[l] ↥(Kc l (Nat.lcm l N) (lcm_pos hN)).1 / d) ≤ Nat.log l N + 1 := by
  have hp : l.Prime := Fact.out
  refine (padicValNat_le_nat_log _).trans ?_
  rw [← Nat.log_mul_base hp.one_lt hN.ne']
  refine Nat.log_mono_right ((Nat.div_le_self _ _).trans ((finrank_le _).trans ?_))
  rw [mul_comm]
  exact Nat.le_of_dvd (Nat.mul_pos hp.pos hN) (Nat.lcm_dvd_mul _ _)

end UpperTheory.N.Cyc

end
