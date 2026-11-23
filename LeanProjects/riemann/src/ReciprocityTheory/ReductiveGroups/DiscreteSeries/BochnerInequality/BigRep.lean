import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary

noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section BigRepA
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem big_ext {k : ℕ} {F G : Big n k M} (h : ∀ κ, F κ = G κ) : F = G := by
  exact PiLp.ext h

theorem mAct_apply (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n) (F : Big n k M) (κ) :
    (mAct E k a b F) κ = E a b (F κ) := rfl

theorem factorAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    (factorAd (M := M) k i a b F) κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  change ((if (κ i).1 = a then coord k (Function.update κ i (b, (κ i).2)) else 0) -
      (if (κ i).2 = b then coord k (Function.update κ i ((κ i).1, a)) else 0) :
      Big n k M →ₗ[ℂ] M) F = _
  rw [LinearMap.sub_apply]
  split_ifs <;> rfl

theorem commutator_add_sum_eq {R : Type*} [Ring R] {k : ℕ} (m m' : R) (s s' : Fin k → R)
    (h1 : ∀ j, m * s' j = s' j * m) (h2 : ∀ i, s i * m' = m' * s i)
    (h3 : ∀ i j, i ≠ j → s i * s' j = s' j * s i) :
    (m + ∑ i, s i) * (m' + ∑ j, s' j) - (m' + ∑ j, s' j) * (m + ∑ i, s i) =
      (m * m' - m' * m) + ∑ i, (s i * s' i - s' i * s i) := by
  simp only [add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : ∑ j, m * s' j = ∑ j, s' j * m := Finset.sum_congr rfl fun j _ => h1 j
  have e2 : ∑ i, s i * m' = ∑ i, m' * s i := Finset.sum_congr rfl fun i _ => h2 i
  have e3 : ∑ x, ∑ i, s i * s' x - ∑ x, ∑ i, s' i * s x = ∑ i, (s i * s' i - s' i * s i) := by
    rw [Finset.sum_comm (f := fun x i => s' i * s x), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_single x (fun i _ hix => sub_eq_zero.2 (h3 i x hix)) (by simp)
  rw [e1, e2, ← e3]
  abel

variable {E : Fin n → Fin n → Module.End ℂ M}

theorem mAct_rel (hE : IsGlRep E) (k : ℕ) (a b c d : Fin n) :
    mAct E k a b * mAct E k c d - mAct E k c d * mAct E k a b =
      (if b = c then mAct E k a d else 0) - (if d = a then mAct E k c b else 0) := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  have h := LinearMap.congr_fun (hE a b c d) (F κ)
  clear hE
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp_all [mAct_apply, Module.End.mul_apply, PiLp.sub_apply]

theorem mAct_factorAd_comm (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    mAct E k a b * factorAd k i c d = factorAd k i c d * mAct E k a b := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  simp only [Module.End.mul_apply, mAct_apply, factorAd_apply]
  split_ifs <;> simp [map_sub]

theorem factorAd_comm_of_ne (k : ℕ) {i j : Fin k} (hij : i ≠ j) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k j c d = factorAd k j c d * factorAd k i a b := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  simp only [Module.End.mul_apply, factorAd_apply, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Function.update_comm hij.symm]
  split_ifs <;> abel

theorem factorAd_commutator (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k i c d - factorAd k i c d * factorAd k i a b =
      (if b = c then factorAd k i a d else 0) - (if d = a then factorAd k i c b else 0) := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
  simp only [hbc, hda, if_true, if_false, LinearMap.sub_apply, LinearMap.zero_apply,
    Module.End.mul_apply, PiLp.sub_apply, PiLp.zero_apply, factorAd_apply, Function.update_self,
    Function.update_idem] <;>
  generalize κ i = p <;>
  obtain ⟨p1, p2⟩ := p <;>
  simp only <;>
  split_ifs <;> subst_vars <;> first | rfl | abel1 | (simp_all <;> abel1) | simp_all

end BigRepA
section BigRepB
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem bAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    (bAct E k a b F) κ = E a b (F κ) + ∑ i, (factorAd k i a b F) κ := by
  show coord k κ ((mAct E k a b + ∑ i, factorAd k i a b : Module.End ℂ (Big n k M)) F) =
    E a b (F κ) + ∑ i, coord k κ (factorAd k i a b F)
  rw [LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum]
  rfl

def swFst {k : ℕ} (i : Fin k) (a b : Fin n) : Equiv.Perm (Fin k → Fin n × Fin n) :=
  Function.Involutive.toPerm (fun κ => Function.update κ i (Equiv.swap a b (κ i).1, (κ i).2))
    (fun κ => by simp [Function.update_idem])

def swSnd {k : ℕ} (i : Fin k) (a b : Fin n) : Equiv.Perm (Fin k → Fin n × Fin n) :=
  Function.Involutive.toPerm (fun κ => Function.update κ i ((κ i).1, Equiv.swap a b (κ i).2))
    (fun κ => by simp [Function.update_idem])

theorem swFst_apply {k : ℕ} (i : Fin k) (a b : Fin n) (κ : Fin k → Fin n × Fin n) :
    swFst i a b κ = Function.update κ i (Equiv.swap a b (κ i).1, (κ i).2) := rfl

theorem swSnd_apply {k : ℕ} (i : Fin k) (a b : Fin n) (κ : Fin k → Fin n × Fin n) :
    swSnd i a b κ = Function.update κ i ((κ i).1, Equiv.swap a b (κ i).2) := rfl

theorem factorAd_adjoint (k : ℕ) (i : Fin k) (a b : Fin n) (F G : Big n k M) :
    inner ℂ (factorAd k i a b F) G = inner ℂ F (factorAd k i b a G) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [factorAd_apply, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
  congr 1
  · rw [← Equiv.sum_comp (swFst i a b)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [swFst_apply]
    simp only [Function.update_self, Function.update_idem]
    by_cases h : (κ i).1 = b
    · have hκ : Function.update κ i (b, (κ i).2) = κ := by
        conv_rhs => rw [← Function.update_eq_self i κ]
        rw [← h]
      rw [if_pos (by rw [h, Equiv.swap_apply_right]), if_pos h, hκ, h, Equiv.swap_apply_right]
    · have h' : Equiv.swap a b (κ i).1 ≠ a := by
        rwa [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
      rw [if_neg h', if_neg h, inner_zero_left, inner_zero_right]
  · rw [← Equiv.sum_comp (swSnd i a b)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [swSnd_apply]
    simp only [Function.update_self, Function.update_idem]
    by_cases h : (κ i).2 = a
    · have hκ : Function.update κ i ((κ i).1, a) = κ := by
        conv_rhs => rw [← Function.update_eq_self i κ]
        rw [← h]
      rw [if_pos (by rw [h, Equiv.swap_apply_left]), if_pos h, hκ, h, Equiv.swap_apply_left]
    · have h' : Equiv.swap a b (κ i).2 ≠ b := by
        rwa [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
      rw [if_neg h', if_neg h, inner_zero_left, inner_zero_right]

theorem mem_ncV_iff {k : ℕ} (F : Big n k M) :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  exact Iff.rfl

theorem ncV_mem {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) (κ : Fin k → Fin n × Fin n) :
    F κ ∈ V := by
  have h := (mem_ncV_iff F).1 hF κ
  split_ifs at h
  · exact h
  · rw [(Submodule.mem_bot ℂ).1 h]
    exact V.zero_mem

theorem ncV_eq_zero {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) {κ : Fin k → Fin n × Fin n}
    (j : Fin k) (hj : ε (κ j).1 = ε (κ j).2) : F κ = 0 := by
  have h := (mem_ncV_iff F).1 hF κ
  rw [if_neg (fun hc => hc j hj)] at h
  exact (Submodule.mem_bot ℂ).1 h

end BigRepB
section BigRep

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem bAct_isGlRep (hE : IsGlRep E) (k : ℕ) : IsGlRep (bAct E k) := by
  intro a b c d
  simp only [bAct]
  rw [commutator_add_sum_eq _ _ _ _ (fun j => mAct_factorAd_comm k j a b c d)
    (fun i => (mAct_factorAd_comm k i c d a b).symm) (fun i j hij => factorAd_comm_of_ne k hij a b c d),
    mAct_rel hE]
  simp only [factorAd_commutator]
  by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, Finset.sum_sub_distrib] <;> abel

theorem bAct_isKUnitary (hU : IsInfUnitary ε E) (k : ℕ) : IsKUnitary ε (bAct E k) := by
  intro a b hab F G
  simp only [bAct, LinearMap.add_apply, LinearMap.sum_apply, inner_add_left, inner_add_right,
    sum_inner, inner_sum, factorAd_adjoint]
  congr 1
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [mAct_apply, mAct_apply, hU a b, adjSign, if_pos hab, one_mul]

theorem ncV_kStable (hV : IsKStableSub ε E V) (k : ℕ) :
    IsKStableSub ε (bAct E k) (ncV ε V k) := by
  intro a b hab F hF
  rw [mem_ncV_iff]
  intro κ
  rw [bAct_apply]
  split_ifs with hc
  · refine add_mem (hV a b hab _ (ncV_mem hF κ)) (Submodule.sum_mem _ fun i _ => ?_)
    rw [factorAd_apply]
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs <;>
      first | exact ncV_mem hF _ | exact Submodule.zero_mem _
  · push_neg at hc
    obtain ⟨j, hj⟩ := hc
    rw [Submodule.mem_bot, ncV_eq_zero hF j hj, map_zero, zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [factorAd_apply]
    by_cases hij : i = j
    · subst hij
      have z1 : (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) = 0 := by
        split_ifs with h1
        · apply ncV_eq_zero hF i
          simp only [Function.update_self]
          rw [← hab, ← h1]
          exact hj
        · rfl
      have z2 : (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) = 0 := by
        split_ifs with h2
        · apply ncV_eq_zero hF i
          simp only [Function.update_self]
          rw [hab, ← h2]
          exact hj
        · rfl
      rw [z1, z2, sub_zero]
    · have hu : ∀ x : Fin n × Fin n, ε ((Function.update κ i x) j).1 = ε ((Function.update κ i x) j).2 := by
        intro x
        rw [Function.update_of_ne (Ne.symm hij)]
        exact hj
      have z1 : (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) = 0 := by
        split_ifs
        · exact ncV_eq_zero hF j (hu _)
        · rfl
      have z2 : (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) = 0 := by
        split_ifs
        · exact ncV_eq_zero hF j (hu _)
        · rfl
      rw [z1, z2, sub_zero]

theorem finiteDimensional_ncV (hV : FiniteDimensional ℂ V) (k : ℕ) :
    FiniteDimensional ℂ (ncV ε V k) := by
  haveI := hV
  let f : ncV ε V k →ₗ[ℂ] ((Fin k → Fin n × Fin n) → V) :=
    LinearMap.pi fun κ => LinearMap.codRestrict V ((coord k κ).comp (ncV ε V k).subtype)
      (fun F => ncV_mem F.2 κ)
  refine FiniteDimensional.of_injective f ?_
  intro F G h
  apply Subtype.ext
  apply big_ext
  intro κ
  exact congrArg Subtype.val (congrFun h κ)

end BigRep

end ReciprocityTheory.ChartRestriction.DS
