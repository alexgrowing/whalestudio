import Formalism.RealPlaceAnalysis.StatementC
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds

open Finset Polynomial

noncomputable section

namespace Formalism.REAL

def CharId_M {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Fin n → V) where
  toFun y := fun a => ∑ b, E a b (y b)
  map_add' y z := by funext a; simp [Finset.sum_add_distrib]
  map_smul' c y := by funext a; simp [Finset.smul_sum]

theorem CharId_M_apply {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (y : Fin n → V) (a : Fin n) :
    CharId_M E y a = ∑ b, E a b (y b) := rfl

def twistedAction {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) : Module.End ℂ (Fin n → V) where
  toFun y := fun x => E c d (y x) - if x = d then y c else 0
  map_add' y z := by
    funext x; by_cases h : x = d <;> simp [h] <;> abel
  map_smul' r y := by
    funext x; by_cases h : x = d <;> simp [h, smul_sub]

theorem CharId_T_apply {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (y : Fin n → V) (x : Fin n) :
    twistedAction E c d y x = E c d (y x) - if x = d then y c else 0 := rfl

theorem CharId_comm {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (c d : Fin n) :
    twistedAction E c d * CharId_M E = CharId_M E * twistedAction E c d := by
  apply LinearMap.ext
  intro y
  funext x
  simp only [Module.End.mul_apply, CharId_T_apply, CharId_M_apply, map_sum, map_sub]
  have key : ∀ b, E c d (E x b (y b)) = E x b (E c d (y b)) +
      ((if d = x then E c b (y b) else 0) - (if b = c then E x d (y b) else 0)) := by
    intro b
    have h := LinearMap.congr_fun (hE c d x b) (y b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_iff_eq_add', h]
    split_ifs <;> simp
  have hb : ∀ b, E x b (if b = d then y c else 0) = if b = d then E x b (y c) else 0 := by
    intro b
    split_ifs <;> simp
  simp only [key, hb, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hxd : x = d
  · subst hxd
    simp
    abel
  · simp [hxd, Ne.symm hxd]
    abel

theorem CharId_Mpow {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (y : Fin n → V) (a : Fin n) :
    (CharId_M E ^ k) y a = ∑ b, epow E k a b (y b) := by
  induction k generalizing y with
  | zero =>
    have h0 : ∀ b, epow E 0 a b (y b) = if a = b then y b else 0 := by
      intro b
      simp only [epow]
      split_ifs <;> simp
    simp [h0]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    simp only [epow, CharId_M_apply, map_sum, LinearMap.sum_apply,
      Module.End.mul_apply]
    exact Finset.sum_comm

def CharId_F {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (j : ℕ) : Submodule ℂ (Fin n → V) :=
  sInf {W | (∀ t : Fin n, j ≤ (t : ℕ) → Pi.single t v ∈ W) ∧
    ∀ c d, ∀ y ∈ W, twistedAction E c d y ∈ W}

theorem CharId_F_gen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (j : ℕ) (t : Fin n) (ht : j ≤ (t : ℕ)) :
    Pi.single t v ∈ CharId_F E v j := Submodule.mem_sInf.2 fun _ hW => hW.1 t ht

theorem twistedAction_mem_tailSubmodule {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (j : ℕ) (c d : Fin n) (y : Fin n → V)
    (hy : y ∈ CharId_F E v j) : twistedAction E c d y ∈ CharId_F E v j := Submodule.mem_sInf.2 fun W hW => hW.2 c d y (Submodule.mem_sInf.1 hy W hW)

theorem CharId_aeval_comm {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (q : ℂ[X]) (c d : Fin n) :
    twistedAction E c d * aeval (CharId_M E) q = aeval (CharId_M E) q * twistedAction E c d := by
  have hc : Commute (twistedAction E c d) (CharId_M E) := CharId_comm E hE c d
  rw [aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, (hc.pow_right i).eq]

theorem CharId_ker {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (v : V) (j : ℕ) (q : ℂ[X])
    (hgen : ∀ t : Fin n, j ≤ (t : ℕ) → aeval (CharId_M E) q (Pi.single t v) = 0) :
    ∀ y ∈ CharId_F E v j, aeval (CharId_M E) q y = 0 := by
  intro y hy
  have hW : LinearMap.ker (aeval (CharId_M E) q) ∈ {W : Submodule ℂ (Fin n → V) |
      (∀ t : Fin n, j ≤ (t : ℕ) → Pi.single t v ∈ W) ∧ ∀ c d, ∀ y ∈ W, twistedAction E c d y ∈ W} := by
    refine ⟨fun t ht => LinearMap.mem_ker.2 (hgen t ht), fun c d z hz => ?_⟩
    rw [LinearMap.mem_ker] at hz ⊢
    rw [← Module.End.mul_apply, ← CharId_aeval_comm E hE q c d, Module.End.mul_apply, hz, map_zero]
  exact LinearMap.mem_ker.1 (Submodule.mem_sInf.1 hy _ hW)

theorem CharId_card {n : ℕ} (t : Fin n) :
    (((univ.filter (fun a : Fin n => t < a)).card : ℕ) : ℂ) = (n : ℂ) - 1 - ((t : ℕ) : ℂ) := by
  have ht := t.isLt
  have hI : univ.filter (fun a : Fin n => t < a) = Finset.Ioi t := by
    ext a
    simp
  have h : (univ.filter (fun a : Fin n => t < a)).card = n - 1 - t := by
    rw [hI, Fin.card_Ioi]
  rw [h, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  simp

private theorem twistedAction_single_of_lt {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (x t a : Fin n) (hta : t < a) :
    twistedAction E a t (Pi.single a v) x = (if x = a then E x t v else 0) - (if x = t then v else 0) := by
  rw [CharId_T_apply]
  by_cases hxa : x = a
  · subst hxa
    simp [ne_of_gt hta]
  · simp [Pi.single_apply, hxa]

theorem CharId_sub_lsh_apply_single {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hv : IsHW E ν v) (t : Fin n) :
    (CharId_M E - algebraMap ℂ (Module.End ℂ (Fin n → V)) (lsh ν t)) (Pi.single t v) =
      ∑ a ∈ univ.filter (fun a => t < a), twistedAction E a t (Pi.single a v) := by
  funext x
  rw [Finset.sum_apply, Finset.sum_congr rfl
    (fun a ha => twistedAction_single_of_lt E v x t a (Finset.mem_filter.1 ha).2),
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const]
  have hs : ∑ c, E x c ((Pi.single t v : Fin n → V) c) = E x t v := by
    rw [Finset.sum_eq_single t]
    · simp
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · simp
  simp only [LinearMap.sub_apply, Module.algebraMap_end_apply, Pi.sub_apply, Pi.smul_apply,
    CharId_M_apply, hs, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_trichotomy x t with h | h | h
  · simp [h.ne, not_lt.2 h.le, hv.2 x t h]
  · subst h
    rw [← Nat.cast_smul_eq_nsmul ℂ, CharId_card]
    simp [hv.1 x, lsh, add_smul, sub_smul]
  · simp [h.ne', h, Pi.single_apply]

theorem CharId_kill {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℂ) (v : V)
    (hv : IsHW E ν v) :
    ∀ k j : ℕ, n ≤ j + k → ∀ q : ℂ[X],
      (∏ s ∈ univ.filter (fun s : Fin n => j ≤ (s : ℕ)), (X - C (lsh ν s))) ∣ q →
      ∀ y ∈ CharId_F E v j, aeval (CharId_M E) q y = 0 := by
  intro k
  induction k with
  | zero =>
    intro j hj q _ y hy
    exact CharId_ker E hE v j q (fun t ht => absurd t.isLt (by omega)) y hy
  | succ k ih =>
    intro j hj q hq y hy
    refine CharId_ker E hE v j q (fun t ht => ?_) y hy
    have hsub : insert t (univ.filter (fun s : Fin n => t.1 + 1 ≤ (s : ℕ))) ⊆
        univ.filter (fun s : Fin n => j ≤ (s : ℕ)) := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rcases hs with rfl | hs <;> omega
    have htn : t ∉ univ.filter (fun s : Fin n => t.1 + 1 ≤ (s : ℕ)) := by simp
    have hdvd := Finset.prod_dvd_prod_of_subset _ _ (fun s => X - C (lsh ν s)) hsub
    rw [Finset.prod_insert htn] at hdvd
    obtain ⟨w, hw⟩ := hdvd.trans hq
    have hq' : q = ((∏ s ∈ univ.filter (fun s : Fin n => t.1 + 1 ≤ (s : ℕ)), (X - C (lsh ν s))) * w) *
        (X - C (lsh ν t)) := by
      rw [hw]; ring
    rw [hq', map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, CharId_sub_lsh_apply_single E ν v hv t]
    refine ih (t.1 + 1) (by omega) _ (dvd_mul_right _ _) _ ?_
    refine Submodule.sum_mem _ fun a ha => twistedAction_mem_tailSubmodule E v _ a t _ (CharId_F_gen E v _ a ?_)
    have h := (Finset.mem_filter.1 ha).2
    exact h

theorem CharId_single {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (f : Fin n → Module.End ℂ V) (b : Fin n) (v : V) :
    ∑ c, f c ((Pi.single b v : Fin n → V) c) = f b v := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Pi.single_apply, hc]
  · simp

theorem CharId_on_v {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℂ) (v : V)
    (hv : IsHW E ν v) (a b : Fin n) :
    ∑ i ∈ range (n + 1),
      (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b v = 0 := by
  have hy : (Pi.single b v : Fin n → V) ∈ CharId_F E v 0 := CharId_F_gen E v 0 b (Nat.zero_le _)
  have hk := CharId_kill E hE ν v hv n 0 (by omega) (∏ s : Fin n, (X - C (lsh ν s))) (by simp) _ hy
  have hdeg : (∏ s : Fin n, (X - C (lsh ν s))).natDegree < n + 1 := by
    rw [natDegree_finset_prod_X_sub_C_eq_card]
    simp
  rw [aeval_eq_sum_range' hdeg] at hk
  have h := congrFun hk a
  simpa [LinearMap.sum_apply, Finset.sum_apply, CharId_Mpow, CharId_single] using h

def CharId_P {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (a b : Fin n) : Module.End ℂ V :=
  ∑ i ∈ range (n + 1),
    (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b

theorem CharId_P_apply {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (a b : Fin n) (x : V) :
    CharId_P E ν a b x = ∑ i ∈ range (n + 1),
      (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b x := by
  simp [CharId_P]

theorem CharId_P_commutator {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℂ) (a b c d : Fin n) :
    E c d * CharId_P E ν a b - CharId_P E ν a b * E c d =
      (if d = a then CharId_P E ν c b else 0) - (if b = c then CharId_P E ν a d else 0) := by
  unfold CharId_P
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have h : ∀ i ∈ range (n + 1),
      E c d * ((∏ s : Fin n, (X - C (lsh ν s))).coeff i • epow E i a b) -
        ((∏ s : Fin n, (X - C (lsh ν s))).coeff i • epow E i a b) * E c d =
      (if d = a then (∏ s : Fin n, (X - C (lsh ν s))).coeff i • epow E i c b else 0) -
        (if b = c then (∏ s : Fin n, (X - C (lsh ν s))).coeff i • epow E i a d else 0) := by
    intro i _
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, generatorPowCovariance_holds _ n E hE i a b c d]
    split_ifs <;> simp [smul_sub]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib]
  split_ifs <;> simp [smul_sub]

theorem characteristicIdentity_holds : CharId := by
  intro V _ _ n E ν v hE hv x hx a b
  let W : Submodule ℂ V := ⨅ (a : Fin n) (b : Fin n), LinearMap.ker (CharId_P E ν a b)
  have hW : W ∈ {W : Submodule ℂ V | v ∈ W ∧ ∀ a b, ∀ x ∈ W, E a b x ∈ W} := by
    refine ⟨?_, ?_⟩
    · simp only [W, Submodule.mem_iInf, LinearMap.mem_ker]
      intro a b
      rw [CharId_P_apply]
      exact CharId_on_v E hE ν v hv a b
    · intro c d y hy
      simp only [W, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      intro a b
      have h := LinearMap.congr_fun (CharId_P_commutator E hE ν a b c d) y
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hy a b, map_zero, zero_sub] at h
      split_ifs at h <;> simp_all
  have hxW : x ∈ W := Submodule.mem_sInf.1 hx W hW
  simp only [W, Submodule.mem_iInf, LinearMap.mem_ker] at hxW
  rw [← CharId_P_apply]
  exact hxW a b

end Formalism.REAL
