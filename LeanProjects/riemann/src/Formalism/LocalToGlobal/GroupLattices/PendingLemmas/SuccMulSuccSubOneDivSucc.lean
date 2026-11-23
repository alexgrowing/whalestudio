import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DelEquiv

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

section Apolar

open MvPolynomial

variable {σ : Type} [Fintype σ] [DecidableEq σ] {S : Type} [CommRing S]

def facS (S : Type) [CommRing S] (n : σ →₀ ℕ) : S := ∏ x ∈ n.support, ((n x).factorial : S)

theorem facS_univ (n : σ →₀ ℕ) : facS S n = ∏ x, ((n x).factorial : S) :=
  Finset.prod_subset (Finset.subset_univ _) fun x _ hx => by
    rw [Finsupp.notMem_support_iff.1 hx, Nat.factorial_zero, Nat.cast_one]

theorem facS_add_single (n : σ →₀ ℕ) (y : σ) :
    facS S (n + Finsupp.single y 1) = facS S n * ((n y : S) + 1) := by
  rw [facS_univ, facS_univ, ← Finset.mul_prod_erase univ _ (mem_univ y),
    ← Finset.mul_prod_erase univ (fun x => ((n x).factorial : S)) (mem_univ y)]
  have h1 : ∏ x ∈ univ.erase y, ((((n + Finsupp.single y 1 : σ →₀ ℕ)) x).factorial : S) = ∏ x ∈ univ.erase y, ((n x).factorial : S) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have : x ≠ y := (Finset.mem_erase.1 hx).1
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg this.symm, add_zero]
  rw [h1, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

def ap (P F : MvPolynomial σ S) : S := ∑ n ∈ P.support, facS S n * coeff n F * coeff n P

theorem ap_eq (P F : MvPolynomial σ S) (T : Finset (σ →₀ ℕ)) (h : P.support ⊆ T) :
    ap P F = ∑ n ∈ T, facS S n * coeff n F * coeff n P :=
  Finset.sum_subset h fun n _ hn => by rw [notMem_support_iff.1 hn, mul_zero]

theorem ap_add_left (P Q F : MvPolynomial σ S) : ap (P + Q) F = ap P F + ap Q F := by
  rw [ap_eq (P + Q) F (P.support ∪ Q.support) support_add, ap_eq P F (P.support ∪ Q.support) Finset.subset_union_left,
    ap_eq Q F (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_add, mul_add]

theorem ap_zero_left (F : MvPolynomial σ S) : ap 0 F = 0 := by simp [ap]

def apHom (F : MvPolynomial σ S) : MvPolynomial σ S →+ S where
  toFun P := ap P F
  map_zero' := ap_zero_left F
  map_add' P Q := ap_add_left P Q F

theorem ap_sum_left {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ S) (F : MvPolynomial σ S) :
    ap (∑ i ∈ s, P i) F = ∑ i ∈ s, ap (P i) F := map_sum (apHom F) P s

theorem ap_C_mul_left (c : S) (P F : MvPolynomial σ S) : ap (C c * P) F = c * ap P F := by
  rw [ap_eq (C c * P) F P.support (fun n hn => by
    rw [mem_support_iff, coeff_C_mul] at hn
    exact mem_support_iff.2 (right_ne_zero_of_mul hn)), ap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_C_mul]
  ring

theorem ap_sum_right {ι : Type} (s : Finset ι) (c : ι → S) (P : MvPolynomial σ S) (F : ι → MvPolynomial σ S) :
    ap P (∑ i ∈ s, C (c i) * F i) = ∑ i ∈ s, c i * ap P (F i) := by
  unfold ap
  simp only [coeff_sum, coeff_C_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n _ => ?_
  ring

theorem ap_mul_X (P F : MvPolynomial σ S) (y : σ) : ap (P * X y) F = ap P (pderiv y F) := by
  unfold ap
  rw [support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [addRightEmbedding_apply, coeff_mul_X, facS_add_single, coeff_pderiv]
  ring

theorem ap_C (a : S) (F : MvPolynomial σ S) : ap (C a) F = coeff 0 F * a := by
  rw [ap_eq (C a) F {0} (by
    intro n hn
    rw [mem_support_iff, coeff_C] at hn
    by_contra h
    exact hn (if_neg fun h0 => h (Finset.mem_singleton.2 h0.symm))), Finset.sum_singleton, coeff_C, if_pos rfl]
  simp [facS]

variable (L : σ → σ → S)

def linP (x : σ) : MvPolynomial σ S := ∑ y, C (L x y) * X y

def linT (y : σ) : MvPolynomial σ S := ∑ x, C (L x y) * X x

theorem pderiv_linP (x y : σ) : pderiv y (linP L x) = C (L x y) := by
  unfold linP
  rw [map_sum]
  simp only [pderiv_C_mul, pderiv_X, Pi.single_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (mem_univ y) h

theorem constantCoeff_linP (x : σ) : constantCoeff (linP L x) = 0 := by
  unfold linP
  rw [map_sum]
  exact Finset.sum_eq_zero fun y _ => by rw [map_mul, constantCoeff_X, mul_zero]

theorem constantCoeff_aeval_linP (F : MvPolynomial σ S) : constantCoeff (aeval (linP L) F) = constantCoeff F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p x _ => rw [map_mul, aeval_X, map_mul, map_mul, constantCoeff_linP, constantCoeff_X, mul_zero, mul_zero]

theorem pderiv_aeval_linP (F : MvPolynomial σ S) (y : σ) :
    pderiv y (aeval (linP L) F) = ∑ x, C (L x y) * aeval (linP L) (pderiv x F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p x0 hp =>
    rw [map_mul, aeval_X, pderiv_mul, hp, pderiv_linP]
    simp only [pderiv_mul, map_add, map_mul, aeval_X, pderiv_X, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun x _ => by ring
    · rw [Finset.sum_eq_single x0]
      · simp
        ring
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h
        exact absurd (mem_univ x0) h

theorem ap_sub (P : MvPolynomial σ S) : ∀ F : MvPolynomial σ S, ap P (aeval (linP L) F) = ap (aeval (linT L) P) F := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro F
    rw [aeval_C, algebraMap_eq, ap_C, ap_C, ← constantCoeff_eq, constantCoeff_aeval_linP]
  | add p q hp hq =>
    intro F
    rw [map_add, ap_add_left, ap_add_left, hp, hq]
  | mul_X p y hp =>
    intro F
    rw [ap_mul_X, pderiv_aeval_linP, ap_sum_right, map_mul, aeval_X]
    have h1 : linT L y = ∑ x, C (L x y) * X x := rfl
    rw [h1, Finset.mul_sum, ap_sum_left]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hp, ← ap_mul_X, ← ap_C_mul_left]
    congr 1
    ring

end Apolar

section Series

open MvPolynomial

variable {σ : Type} [Fintype σ] [DecidableEq σ] {S : Type} [CommRing S] {K : Type} [Field K] [Algebra K S]

theorem ap_monomial (R : MvPolynomial σ S) (m : σ →₀ ℕ) : ap R (monomial m 1) = facS S m * coeff m R := by
  unfold ap
  by_cases hm : m ∈ R.support
  · rw [Finset.sum_eq_single m]
    · rw [coeff_monomial, if_pos rfl, mul_one]
    · intro n _ hn
      rw [coeff_monomial, if_neg (Ne.symm hn), mul_zero, zero_mul]
    · intro h
      exact absurd hm h
  · rw [notMem_support_iff.1 hm, mul_zero]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [coeff_monomial, if_neg (fun h : m = n => hm (h ▸ hn)), mul_zero, zero_mul]

variable (Lk : σ → σ → K)

def linS (x : σ) : MvPowerSeries σ K := ∑ y, MvPowerSeries.C (Lk x y) * MvPowerSeries.X y

theorem linS_eq (x : σ) : linS Lk x = ((linP Lk x : MvPolynomial σ K) : MvPowerSeries σ K) := by
  unfold linS linP
  rw [← coeToMvPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_mul, coeToMvPowerSeries.ringHom_apply, coeToMvPowerSeries.ringHom_apply, coe_C, coe_X]

theorem hasSubst_linS : MvPowerSeries.HasSubst (linS Lk) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by
    unfold linS
    rw [map_sum]
    exact Finset.sum_eq_zero fun y _ => by rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

theorem map_linP (x : σ) : map (algebraMap K S) (linP Lk x) = linP (fun x y => algebraMap K S (Lk x y)) x := by
  unfold linP
  rw [map_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [map_mul, map_C, map_X]

theorem coeff_prod_linS (m n : σ →₀ ℕ) :
    algebraMap K S (MvPowerSeries.coeff n (m.prod fun s e => linS Lk s ^ e)) =
      coeff n (aeval (linP fun x y => algebraMap K S (Lk x y)) (monomial m (1 : S))) := by
  have h1 : (m.prod fun s e => linS Lk s ^ e) =
      ((m.prod fun s e => linP Lk s ^ e : MvPolynomial σ K) : MvPowerSeries σ K) := by
    rw [← coeToMvPowerSeries.ringHom_apply, Finsupp.prod, Finsupp.prod, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, coeToMvPowerSeries.ringHom_apply, linS_eq]
  rw [h1, coeff_coe, ← coeff_map, aeval_monomial, map_one, one_mul, Finsupp.prod, Finsupp.prod, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, map_linP]

def pr (Gd : (σ →₀ ℕ) → Prop) [DecidablePred Gd] (Q : MvPolynomial σ S) (f : MvPowerSeries σ K) : S :=
  ∑ n ∈ Q.support, (if Gd n then facS K n * MvPowerSeries.coeff n f else 0) • coeff n Q

theorem algebraMap_facS (n : σ →₀ ℕ) : algebraMap K S (facS K n) = facS S n := by
  unfold facS
  rw [map_prod]
  exact Finset.prod_congr rfl fun x _ => map_natCast _ _

theorem pr_sub (Gd : (σ →₀ ℕ) → Prop) [DecidablePred Gd]
    (hGd : ∀ m n, coeff n (aeval (linP fun x y => algebraMap K S (Lk x y)) (monomial m (1 : S))) ≠ 0 → (Gd n ↔ Gd m))
    (Q : MvPolynomial σ S) (f : MvPowerSeries σ K) :
    pr Gd Q (MvPowerSeries.subst (linS Lk) f) = pr Gd (aeval (linT fun x y => algebraMap K S (Lk x y)) Q) f := by
  set L : σ → σ → S := fun x y => algebraMap K S (Lk x y) with hL
  have ha := hasSubst_linS Lk
  let T : Finset (σ →₀ ℕ) :=
    (Q.support.biUnion fun n => (show (Function.support fun d => MvPowerSeries.coeff d f •
      MvPowerSeries.coeff n (d.prod fun s e => linS Lk s ^ e)).Finite from
        MvPowerSeries.coeff_subst_finite ha f n).toFinset) ∪ (aeval (linT L) Q).support
  have hc : ∀ n ∈ Q.support, MvPowerSeries.coeff n (MvPowerSeries.subst (linS Lk) f) =
      ∑ m ∈ T, MvPowerSeries.coeff m f * MvPowerSeries.coeff n (m.prod fun s e => linS Lk s ^ e) := by
    intro n hn
    rw [MvPowerSeries.coeff_subst ha]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro m hm
    refine Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨n, hn, ?_⟩))
    exact (Set.Finite.mem_toFinset _).2 hm

  have hm : ∀ m, ∑ n ∈ Q.support, (if Gd n then facS S n * coeff n (aeval (linP L) (monomial m (1 : S))) else 0) * coeff n Q =
      (if Gd m then facS S m else 0) * coeff m (aeval (linT L) Q) := by
    intro m
    have h0 := ap_sub L Q (monomial m 1)
    rw [ap_monomial] at h0
    by_cases hg : Gd m
    · rw [if_pos hg, ← h0]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hz : coeff n (aeval (linP L) (monomial m (1 : S))) = 0
      · rw [hz]; simp
      · rw [if_pos ((hGd m n hz).2 hg)]
    · rw [if_neg hg, zero_mul]
      refine Finset.sum_eq_zero fun n _ => ?_
      by_cases hz : coeff n (aeval (linP L) (monomial m (1 : S))) = 0
      · rw [hz]; simp
      · rw [if_neg (fun h => hg ((hGd m n hz).1 h)), zero_mul]
  have h2 : pr Gd (aeval (linT L) Q) f =
      ∑ m ∈ T, (if Gd m then facS K m * MvPowerSeries.coeff m f else 0) • coeff m (aeval (linT L) Q) :=
    Finset.sum_subset Finset.subset_union_right fun m _ hm' => by rw [notMem_support_iff.1 hm', smul_zero]
  rw [h2]
  unfold pr
  calc ∑ n ∈ Q.support, (if Gd n then facS K n * MvPowerSeries.coeff n (MvPowerSeries.subst (linS Lk) f) else 0) • coeff n Q
      = ∑ n ∈ Q.support, ∑ m ∈ T, algebraMap K S (MvPowerSeries.coeff m f) *
          ((if Gd n then facS S n * coeff n (aeval (linP L) (monomial m (1 : S))) else 0) * coeff n Q) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hc n hn, Algebra.smul_def]
        by_cases hg : Gd n
        · simp only [if_pos hg]
          rw [map_mul, map_sum, algebraMap_facS, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_mul, coeff_prod_linS]
          ring
        · simp only [if_neg hg]
          simp
    _ = ∑ m ∈ T, algebraMap K S (MvPowerSeries.coeff m f) *
          ((if Gd m then facS S m else 0) * coeff m (aeval (linT L) Q)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Finset.mul_sum, hm m]
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Algebra.smul_def]
        by_cases hg : Gd m
        · simp only [if_pos hg]
          rw [map_mul, algebraMap_facS]
          ring
        · simp only [if_neg hg]
          simp

end Series

section Conc

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]
  (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

def cf (v : X.Pl) (s : Fin (X.G.P.n' v)) : Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) Kc :=
  if IsOddPos s then mAt X Kc j v s ((B v)⁻¹ : GL _ _) else (mAt X Kc j v s (B v)).transpose

theorem actS_eq (z : X.ZA j) : actS X Kc j B z =
    ∑ a', MvPowerSeries.C (cf X Kc j B z.1 z.2.1 z.2.2.1 a') * MvPowerSeries.X (⟨z.1, (z.2.1, a', z.2.2.2)⟩ : X.ZA j) := by
  obtain ⟨v, s, a, b⟩ := z
  unfold actS cf
  refine Finset.sum_congr rfl fun a' _ => ?_
  by_cases h : IsOddPos s
  · simp only [if_pos h]
  · simp only [if_neg h, Matrix.transpose_apply]

def LkB (z z' : X.ZA j) : Kc :=
  ∑ a', if z' = (⟨z.1, (z.2.1, a', z.2.2.2)⟩ : X.ZA j) then cf X Kc j B z.1 z.2.1 z.2.2.1 a' else 0

theorem linS_LkB (z : X.ZA j) : linS (LkB X Kc j B) z = actS X Kc j B z := by
  rw [actS_eq]
  unfold linS LkB
  simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_eq_single (⟨z.1, (z.2.1, a', z.2.2.2)⟩ : X.ZA j)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, map_zero, zero_mul]
  · intro h
    exact absurd (mem_univ _) h

def lamF (y : X.ZA j) : DA X Kc j :=
  ∑ a, MvPolynomial.C (algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (cf X Kc j B y.1 y.2.1 a y.2.2.1)) *
    MvPolynomial.X (⟨y.1, (y.2.1, a, y.2.2.2)⟩ : X.ZA j)

theorem LkB_same (y : X.ZA j) (a : Fin (NN X.G.P.m X.t j)) :
    LkB X Kc j B ⟨y.1, (y.2.1, a, y.2.2.2)⟩ y = cf X Kc j B y.1 y.2.1 a y.2.2.1 := by
  obtain ⟨v, s, a'', b⟩ := y
  unfold LkB
  rw [Finset.sum_eq_single a'']
  · rw [if_pos rfl]
  · intro a' _ ha'
    refine if_neg fun h => ha' ?_
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and, and_true] at h
    exact h.symm
  · intro h
    exact absurd (mem_univ _) h

theorem linT_LkB (y : X.ZA j) :
    linT (fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (LkB X Kc j B x y)) y = lamF X Kc j B y := by
  unfold linT lamF
  have hinj : Function.Injective fun a : Fin (NN X.G.P.m X.t j) => (⟨y.1, (y.2.1, a, y.2.2.2)⟩ : X.ZA j) := by
    intro a a' h
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and, and_true] at h
    exact h
  rw [← Finset.sum_subset (Finset.subset_univ (univ.image fun a : Fin (NN X.G.P.m X.t j) =>
    (⟨y.1, (y.2.1, a, y.2.2.2)⟩ : X.ZA j))), Finset.sum_image fun a _ a' _ h => hinj h]
  · refine Finset.sum_congr rfl fun a _ => ?_
    beta_reduce
    rw [LkB_same]
  · intro x _ hx
    have h0 : LkB X Kc j B x y = 0 := by
      refine Finset.sum_eq_zero fun a' _ => if_neg fun h => hx ?_
      subst h
      exact Finset.mem_image.2 ⟨x.2.2.1, mem_univ _, rfl⟩
    beta_reduce
    rw [h0, map_zero, map_zero, zero_mul]

def lamB : DA X Kc j →ₐ[XspC (X.Pj (j + 1)) Kc] DA X Kc j := MvPolynomial.aeval (lamF X Kc j B)

theorem lamB_eq : MvPolynomial.aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (LkB X Kc j B x y)) = lamB X Kc j B := by
  unfold lamB
  congr 1
  exact funext (linT_LkB X Kc j B)

end Conc

section Filter

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]
  (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem sum_block {M : Type} [AddCommMonoid M] (F : X.ZA j → M) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (h0 : ∀ z : X.ZA j, (⟨z.1, z.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) ≠ ⟨v, s⟩ → F z = 0) :
    ∑ z, F z = ∑ a, ∑ b, F ⟨v, (s, a, b)⟩ := by
  have h1 : ∑ a, ∑ b, F ⟨v, (s, a, b)⟩ =
      ∑ ab : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)), F ⟨v, (s, ab)⟩ :=
    (Fintype.sum_prod_type fun ab : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)) => F ⟨v, (s, ab)⟩).symm
  have hinj : Function.Injective fun ab : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)) =>
      (⟨v, (s, ab)⟩ : X.ZA j) := by
    intro a a' h
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
    exact h
  rw [h1, ← Finset.sum_image (f := F) (s := univ) fun a _ a' _ h => hinj h]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun z _ hz => h0 z fun h => hz ?_
  obtain ⟨v', s', ab⟩ := z
  cases h
  exact Finset.mem_image.2 ⟨ab, mem_univ _, rfl⟩

def wB (v : X.Pl) (s : Fin (X.G.P.n' v)) (z : X.ZA j) : ℕ :=
  if (⟨z.1, z.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩ then 1 else 0

theorem wt_eq (v : X.Pl) (s : Fin (X.G.P.n' v)) (n : X.ZA j →₀ ℕ) :
    Finsupp.weight (wB X j v s) n = ∑ a, ∑ b, n ⟨v, (s, a, b)⟩ := by
  rw [Finsupp.weight_eq_sum, sum_block X j (fun z => n z • wB X j v s z) v s (fun z hz => by
    simp only [wB, if_neg hz, smul_zero])]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [wB]

theorem LkB_ne (x y : X.ZA j) (h : LkB X Kc j B x y ≠ 0) :
    (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨x.1, x.2.1⟩ := by
  by_contra hne
  refine h (Finset.sum_eq_zero fun a' _ => if_neg fun hy => hne ?_)
  subst hy
  rfl

theorem isWeightedHomogeneous_linP (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.ZA j) :
    MvPolynomial.IsWeightedHomogeneous (wB X j v s)
      (linP (fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (LkB X Kc j B x y)) x) (wB X j v s x) := by
  unfold linP
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun y _ => ?_
  beta_reduce
  by_cases h : LkB X Kc j B x y = 0
  · rw [h, map_zero, map_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  · have h2 : wB X j v s x = wB X j v s y := by
      unfold wB
      rw [LkB_ne X Kc j B x y h]
    rw [h2]
    exact (MvPolynomial.isWeightedHomogeneous_X _ _ y).C_mul _

theorem mono_wh (v : X.Pl) (s : Fin (X.G.P.n' v)) (m : X.ZA j →₀ ℕ) :
    MvPolynomial.IsWeightedHomogeneous (wB X j v s)
      (MvPolynomial.aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (LkB X Kc j B x y))
        (MvPolynomial.monomial m (1 : XspC (X.Pj (j + 1)) Kc))) (Finsupp.weight (wB X j v s) m) := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.weight_apply]
  exact MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun x _ => (isWeightedHomogeneous_linP X Kc j B v s x).pow _

theorem hGd_B (m n : X.ZA j →₀ ℕ)
    (h : MvPolynomial.coeff n (MvPolynomial.aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (LkB X Kc j B x y))
        (MvPolynomial.monomial m (1 : XspC (X.Pj (j + 1)) Kc))) ≠ 0) : GoodDeg X j n ↔ GoodDeg X j m := by
  have key : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), ∑ a, ∑ b, n ⟨v, (s, a, b)⟩ = ∑ a, ∑ b, m ⟨v, (s, a, b)⟩ := by
    intro v s
    rw [← wt_eq, ← wt_eq]
    by_contra hne
    exact h ((mono_wh X Kc j B v s m).coeff_eq_zero n hne)
  unfold GoodDeg
  simp only [key]

open Classical in
theorem pairD_eq_pr (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j P f = pr (GoodDeg X j) P f := rfl

theorem pairD_SA (Q : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j Q (SA X Kc j B f) = pairD X Kc j (lamB X Kc j B Q) f := by
  classical
  have h := pr_sub (LkB X Kc j B) (GoodDeg X j) (hGd_B X Kc j B) Q f
  rw [lamB_eq, (funext (linS_LkB X Kc j B) : linS (LkB X Kc j B) = actS X Kc j B)] at h
  rw [pairD_eq_pr, pairD_eq_pr]
  exact h

end Filter

section Mat

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]
  (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

def cD : Kc →+* DA X Kc j := (MvPolynomial.C).comp (algebraMap Kc (XspC (X.Pj (j + 1)) Kc))

theorem lamB_dMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (dMat X Kc j v s).map (lamB X Kc j B) = ((cf X Kc j B v s).transpose.map (cD X Kc j)) * dMat X Kc j v s := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply, Matrix.mul_apply]
  show lamB X Kc j B (MvPolynomial.X _) = _
  unfold lamB
  rw [MvPolynomial.aeval_X]
  rfl

theorem lamB_yMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (yMat X Kc j v s).map (lamB X Kc j B) = yMat X Kc j v s := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply]
  show lamB X Kc j B (MvPolynomial.C _) = _
  unfold lamB
  rw [MvPolynomial.aeval_C]
  rfl

theorem lamB_dyMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (dyMat X Kc j v s).map (lamB X Kc j B) = ((cf X Kc j B v s).transpose.map (cD X Kc j)) * dyMat X Kc j v s := by
  unfold dyMat
  rw [← Matrix.submatrix_map, Matrix.map_mul, lamB_dMat, lamB_yMat, Matrix.mul_assoc]
  refine Matrix.ext fun a t => ?_
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]

theorem lamB_YtMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (YtMat X Kc j v s).map (lamB X Kc j B) = YtMat X Kc j v s * ((cf X Kc j B v s).map (cD X Kc j)) := by
  unfold YtMat
  have h1 : ((yMat X Kc j v s).adjugate.submatrix (shiftI X j) id).map (lamB X Kc j B) =
      (yMat X Kc j v s).adjugate.submatrix (shiftI X j) id := by
    rw [← Matrix.submatrix_map]
    have := RingHom.map_adjugate (lamB X Kc j B : DA X Kc j →+* DA X Kc j) (yMat X Kc j v s)
    simp only [RingHom.mapMatrix_apply] at this
    have h2 : (yMat X Kc j v s).map ((lamB X Kc j B : DA X Kc j →+* DA X Kc j)) = yMat X Kc j v s := lamB_yMat X Kc j B v s
    rw [h2] at this
    exact congrArg (fun M => M.submatrix (shiftI X j) id) this
  rw [Matrix.map_mul, h1, Matrix.transpose_map, lamB_dMat, Matrix.transpose_mul, ← Matrix.transpose_map,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem det_mAt (v : X.Pl) (s : Fin (X.G.P.n' v))
    (A : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    (mAt X Kc j v s A).det = tw X Kc v s A.det := by
  unfold mAt
  rw [Matrix.det_submatrix_equiv_self, RingHom.map_det]
  rfl

end Mat

section Tau

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]
  (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem hM_mul_gM (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    mAt X Kc j v s ((B v)⁻¹ : GL _ _) * mAt X Kc j v s (B v) = 1 := by
  rw [mAt_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mAt_one]

theorem gM_mul_hM (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    mAt X Kc j v s (B v) * mAt X Kc j v s ((B v)⁻¹ : GL _ _) = 1 := by
  rw [mAt_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mAt_one]

theorem cf_inv (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    cf X Kc j (fun v => (B v)⁻¹) v s =
      if IsOddPos s then mAt X Kc j v s (B v) else (mAt X Kc j v s ((B v)⁻¹ : GL _ _)).transpose := by
  unfold cf
  simp only [inv_inv]

theorem cf_mul_cf_inv (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    cf X Kc j B v s * cf X Kc j (fun v => (B v)⁻¹) v s = 1 := by
  rw [cf_inv]
  unfold cf
  by_cases h : IsOddPos s
  · simp only [if_pos h]
    exact hM_mul_gM X Kc j B v s
  · simp only [if_neg h]
    rw [← Matrix.transpose_mul, hM_mul_gM, Matrix.transpose_one]

theorem lamB_cD (c : Kc) : lamB X Kc j B (cD X Kc j c) = cD X Kc j c := by
  unfold lamB cD
  rw [RingHom.comp_apply, MvPolynomial.aeval_C]
  rfl

theorem map_cD_lamB {n n' : Type} (M : Matrix n n' Kc) :
    (M.map (cD X Kc j)).map (lamB X Kc j B) = M.map (cD X Kc j) :=
  Matrix.ext fun a b => by rw [Matrix.map_apply, Matrix.map_apply, lamB_cD]

theorem lamB_comp (P : DA X Kc j) : lamB X Kc j B (lamB X Kc j (fun v => (B v)⁻¹) P) = P := by
  have h : (lamB X Kc j B).comp (lamB X Kc j fun v => (B v)⁻¹) = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun y => ?_
    obtain ⟨v, s, a, b⟩ := y
    have h1 : ((dMat X Kc j v s).map (lamB X Kc j fun v => (B v)⁻¹)).map (lamB X Kc j B) = dMat X Kc j v s := by
      rw [lamB_dMat, Matrix.map_mul, map_cD_lamB, lamB_dMat, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.transpose_mul,
        cf_mul_cf_inv, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    exact congrFun (congrFun h1 a) b
  exact congrArg (fun φ => φ P) h

def ec (v : X.Pl) (s : Fin (X.G.P.n' v)) : Kc := (cf X Kc j (fun v => (B v)⁻¹) v s).det

theorem det_map_cD {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n Kc) :
    (M.map (cD X Kc j)).det = cD X Kc j M.det := ((cD X Kc j).map_det M).symm

theorem tau_det_y (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamB X Kc j B (yMat X Kc j v s).det = (yMat X Kc j v s).det := by
  rw [AlgHom.map_det]
  show ((yMat X Kc j v s).map (lamB X Kc j B)).det = _
  rw [lamB_yMat]

theorem tau_det_Yt (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamB X Kc j (fun v => (B v)⁻¹) (YtMat X Kc j v s).det = cD X Kc j (ec X Kc j B v s) * (YtMat X Kc j v s).det := by
  rw [AlgHom.map_det]
  show ((YtMat X Kc j v s).map (lamB X Kc j fun v => (B v)⁻¹)).det = _
  rw [lamB_YtMat, Matrix.det_mul, det_map_cD, mul_comm]
  rfl

theorem tau_det_dy (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamB X Kc j (fun v => (B v)⁻¹) (dyMat X Kc j v s).det = cD X Kc j (ec X Kc j B v s) * (dyMat X Kc j v s).det := by
  rw [AlgHom.map_det]
  show ((dyMat X Kc j v s).map (lamB X Kc j fun v => (B v)⁻¹)).det = _
  rw [lamB_dyMat, Matrix.det_mul, det_map_cD, Matrix.det_transpose]
  rfl

def n1 : Kc := ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v),
  if IsOddPos s then ec X Kc j B v s ^ (exT X j v s).toNat
  else ec X Kc j B v s ^ (X.nuv v (j + 1) s (NN X.G.P.m X.t j)).toNat

def d1 : Kc := ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v),
  if IsOddPos s then ec X Kc j B v s ^ (-exT X j v s).toNat else 1

theorem tau_numD : lamB X Kc j (fun v => (B v)⁻¹) (numD X Kc j) = cD X Kc j (n1 X Kc j B) * numD X Kc j := by
  unfold numD n1
  simp only [map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases h : IsOddPos s
  · simp only [if_pos h]
    rw [map_mul, map_pow, map_pow, tau_det_y, tau_det_Yt, map_pow, mul_pow]
    ring
  · simp only [if_neg h]
    rw [map_pow, tau_det_dy, map_pow, mul_pow]

theorem tau_denD : lamB X Kc j (fun v => (B v)⁻¹) (denD X Kc j) = cD X Kc j (d1 X Kc j B) * denD X Kc j := by
  unfold denD d1
  simp only [map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases h : IsOddPos s
  · simp only [if_pos h]
    rw [map_mul, map_pow, map_pow, tau_det_y, tau_det_Yt, map_pow, mul_pow]
    ring
  · simp only [if_neg h]
    rw [map_one, map_one, one_mul]

end Tau

section Core

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]
  (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem ec_ne (v : X.Pl) (s : Fin (X.G.P.n' v)) : ec X Kc j B v s ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (cf_mul_cf_inv X Kc j B v s)
  rw [Matrix.det_mul, Matrix.det_one] at h1
  unfold ec at h
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

theorem normalizing_constant_ne_zero : n1 X Kc j B ≠ 0 := by
  unfold n1
  refine Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun s _ => ?_
  split_ifs <;> exact pow_ne_zero _ (ec_ne X Kc j B v s)

theorem pairD_cD_mul (c : Kc) (Q : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j (cD X Kc j c * Q) f = c • pairD X Kc j Q f := by
  rw [pairD_eq X Kc j (cD X Kc j c * Q) f Q.support (fun n hn => by
    rw [MvPolynomial.mem_support_iff] at hn ⊢
    intro h0
    apply hn
    show MvPolynomial.coeff n (MvPolynomial.C _ * Q) = 0
    rw [MvPolynomial.coeff_C_mul, h0, mul_zero])]
  unfold pairD
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : MvPolynomial.coeff n (cD X Kc j c * Q) = c • MvPolynomial.coeff n Q := by
    show MvPolynomial.coeff n (MvPolynomial.C _ * Q) = _
    rw [MvPolynomial.coeff_C_mul, Algebra.smul_def]
  rw [h1, smul_comm]

theorem delF_core (G G' : (X.Pj j).Xsp) (c0 : Kc)
    (hS : subD X Kc j G' = cD X Kc j c0 * lamB X Kc j (fun v => (B v)⁻¹) (subD X Kc j G))
    (hG : GoodG X Kc j G) (f : MvPowerSeries (X.ZA j) Kc) :
    GoodG X Kc j G' ∧ delF X Kc j G' (SA X Kc j B f) =
      (c0 * d1 X Kc j B * (n1 X Kc j B)⁻¹) • delF X Kc j G f := by
  obtain ⟨R, hR⟩ := hG
  have h1 := congrArg (lamB X Kc j fun v => (B v)⁻¹) hR
  rw [map_mul, map_mul, tau_numD, tau_denD] at h1
  have hn : cD X Kc j (n1 X Kc j B)⁻¹ * cD X Kc j (n1 X Kc j B) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (normalizing_constant_ne_zero X Kc j B), map_one]
  have h2 : subD X Kc j G' * numD X Kc j = denD X Kc j *
      (cD X Kc j (c0 * d1 X Kc j B * (n1 X Kc j B)⁻¹) * lamB X Kc j (fun v => (B v)⁻¹) R) := by
    rw [hS]
    calc cD X Kc j c0 * lamB X Kc j (fun v => (B v)⁻¹) (subD X Kc j G) * numD X Kc j
        = (cD X Kc j (n1 X Kc j B)⁻¹ * cD X Kc j (n1 X Kc j B)) *
            (cD X Kc j c0 * lamB X Kc j (fun v => (B v)⁻¹) (subD X Kc j G) * numD X Kc j) := by rw [hn, one_mul]
      _ = cD X Kc j (n1 X Kc j B)⁻¹ * cD X Kc j c0 *
            (lamB X Kc j (fun v => (B v)⁻¹) (subD X Kc j G) * (cD X Kc j (n1 X Kc j B) * numD X Kc j)) := by ring
      _ = _ := by
          rw [h1, map_mul, map_mul]
          ring
  refine ⟨⟨_, h2⟩, ?_⟩
  rw [delF_eq X Kc j G' _ h2, pairD_cD_mul, pairD_SA, lamB_comp, delF_eq X Kc j G R hR]

theorem ySub_tau (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    ((mAt X Kc j v s ((B v)⁻¹ : GL _ _)).map (cD X Kc j)) * ySub X Kc j v s =
      cD X Kc j (if IsOddPos s then (ec X Kc j B v s)⁻¹ else 1) •
        (ySub X Kc j v s).map (lamB X Kc j fun v => (B v)⁻¹) := by
  by_cases h : IsOddPos s
  · rw [if_pos h, ySub_odd X Kc j v s h]
    have h1 : (YtMat X Kc j v s).adjugate.map (lamB X Kc j fun v => (B v)⁻¹) =
        ((YtMat X Kc j v s).map (lamB X Kc j fun v => (B v)⁻¹)).adjugate :=
      RingHom.map_adjugate (lamB X Kc j (fun v => (B v)⁻¹) : DA X Kc j →+* DA X Kc j) (YtMat X Kc j v s)
    have hcf : cf X Kc j (fun v => (B v)⁻¹) v s = mAt X Kc j v s (B v) := by rw [cf_inv, if_pos h]
    have h2 : ((mAt X Kc j v s (B v)).map (cD X Kc j)).adjugate =
        cD X Kc j (ec X Kc j B v s) • (mAt X Kc j v s ((B v)⁻¹ : GL _ _)).map (cD X Kc j) := by
      have h3 : (mAt X Kc j v s (B v)).map (cD X Kc j) * (mAt X Kc j v s ((B v)⁻¹ : GL _ _)).map (cD X Kc j) = 1 := by
        rw [← Matrix.map_mul, gM_mul_hM, Matrix.map_one _ (map_zero _) (map_one _)]
      calc ((mAt X Kc j v s (B v)).map (cD X Kc j)).adjugate
          = ((mAt X Kc j v s (B v)).map (cD X Kc j)).adjugate * ((mAt X Kc j v s (B v)).map (cD X Kc j) *
              (mAt X Kc j v s ((B v)⁻¹ : GL _ _)).map (cD X Kc j)) := by rw [h3, Matrix.mul_one]
        _ = _ := by
            rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, det_map_cD]
            unfold ec
            rw [hcf]
    rw [h1, lamB_YtMat, hcf, Matrix.adjugate_mul_distrib, h2, Matrix.smul_mul, smul_smul, ← map_mul,
      inv_mul_cancel₀ (ec_ne X Kc j B v s), map_one, one_smul]
  · rw [if_neg h, map_one, one_smul]
    have h0 : ySub X Kc j v s = dyMat X Kc j v s := by unfold ySub; rw [if_neg h]
    rw [h0, lamB_dyMat, cf_inv, if_neg h, Matrix.transpose_transpose]

end Core

section Final

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

theorem ringHom_scale {I R T : Type} [Fintype I] [DecidableEq I] [CommRing R] [CommRing T]
    (φ ψ : MvPolynomial I R →+* T) (c : I → T) (hC : ∀ a, φ (MvPolynomial.C a) = ψ (MvPolynomial.C a))
    (hX : ∀ x, φ (MvPolynomial.X x) = c x * ψ (MvPolynomial.X x)) (s : T) (G : MvPolynomial I R)
    (hG : ∀ m ∈ G.support, ∏ x, c x ^ m x = s) : φ G = s * ψ G := by
  have hm : ∀ (m : I →₀ ℕ) (a : R), φ (MvPolynomial.monomial m a) = (∏ x, c x ^ m x) * ψ (MvPolynomial.monomial m a) := by
    intro m a
    rw [MvPolynomial.monomial_eq, map_mul, map_mul, hC, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod, map_prod]
    simp only [map_pow, hX, mul_pow]
    rw [Finset.prod_mul_distrib]
    ring
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m hm' => by rw [hm, hG m hm']

theorem alg_eq (j : ℕ) (a : X.G.Kf) : algebraMap X.G.Kf (DA X Kc j) a = cD X Kc j (algebraMap X.G.Kf Kc a) := by
  rw [MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply]
  rfl

theorem subD_C (j : ℕ) (a : X.G.Kf) : subD X Kc j (MvPolynomial.C a) = cD X Kc j (algebraMap X.G.Kf Kc a) := by
  rw [← alg_eq, ← MvPolynomial.algebraMap_eq]
  exact AlgHom.commutes _ _

theorem subD_subst_X (j : ℕ) (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v))
    (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    subD X Kc j ((X.Pj j).subst (fun v s => (X.Pj j).gPos v s ((A v)⁻¹ : GL _ _)) (MvPolynomial.X x)) =
      (((mAt X Kc j (idxJ X j x).1 (idxJ X j x).2.1 ((glAt X j A (idxJ X j x).1)⁻¹ : GL _ _)).map (cD X Kc j)) *
        ySub X Kc j (idxJ X j x).1 (idxJ X j x).2.1) (idxJ X j x).2.2.1 (idxJ X j x).2.2.2 := by
  cases j <;>
  · obtain ⟨v, s, a, t⟩ := x
    rw [Matrix.mul_apply]
    simp only [Places.subst, MvPolynomial.aeval_X, map_sum, map_mul, subD_X, subD_C]
    refine Fintype.sum_equiv (finCongr (rankJ X _)) _ _ fun b => ?_
    rfl

def blkJ (j : ℕ)
    (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    Σ v : X.Pl, Fin (X.G.P.n' v) := ⟨(idxJ X j x).1, (idxJ X j x).2.1⟩

def OddDeg (j : ℕ) (G : (X.Pj j).Xsp) : Prop :=
  ∀ m ∈ G.support, ∀ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), IsOddPos b.2 →
    ((∑ x ∈ univ.filter (fun x => blkJ X j x = b), m x : ℕ) : ℤ) =
      (NN X.G.P.m X.t j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2

def s1 (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : Kc :=
  ∏ b : (Σ v : X.Pl, Fin (X.G.P.n' v)),
    if IsOddPos b.2 then ec X Kc j B b.1 b.2 ^ (-((NN X.G.P.m X.t j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2)) else 1

def s0 (j : ℕ) (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) : X.G.Kf :=
  ∏ v, ∏ s : Fin ((X.Pj j).n' v), ((X.Pj j).gPos v s (A v : Matrix _ _ _)).det ^
    (-(lamAt ((X.Pj j).lam0 v) s (Fin.last (X.Pj j).m)))

set_option maxHeartbeats 1000000 in
theorem subD_natAct (j : ℕ) (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) (G : (X.Pj j).Xsp)
    (hO : OddDeg X j G) :
    subD X Kc j ((X.Pj j).natAct A G) = cD X Kc j (algebraMap X.G.Kf Kc (s0 X j A) * s1 X Kc j (glAt X j A)) *
      lamB X Kc j (fun v => (glAt X j A v)⁻¹) (subD X Kc j G) := by
  have h1 : (X.Pj j).natAct A G = s0 X j A • (X.Pj j).subst (fun v s => (X.Pj j).gPos v s ((A v)⁻¹ : GL _ _)) G := rfl
  rw [h1, map_smul, Algebra.smul_def, alg_eq, map_mul, mul_assoc]
  congr 1
  have hC : ∀ a : X.G.Kf, subD X Kc j ((X.Pj j).subst (fun v s => (X.Pj j).gPos v s ((A v)⁻¹ : GL _ _)) (MvPolynomial.C a)) =
      lamB X Kc j (fun v => (glAt X j A v)⁻¹) (subD X Kc j (MvPolynomial.C a)) := by
    intro a
    have h2 : (X.Pj j).subst (fun v s => (X.Pj j).gPos v s ((A v)⁻¹ : GL _ _)) (MvPolynomial.C a) = MvPolynomial.C a := by
      rw [← MvPolynomial.algebraMap_eq]
      exact AlgHom.commutes _ _
    rw [h2, subD_C, lamB_cD]
  have hX : ∀ x, subD X Kc j ((X.Pj j).subst (fun v s => (X.Pj j).gPos v s ((A v)⁻¹ : GL _ _)) (MvPolynomial.X x)) =
      cD X Kc j (if IsOddPos (blkJ X j x).2 then (ec X Kc j (glAt X j A) (blkJ X j x).1 (blkJ X j x).2)⁻¹ else 1) *
        lamB X Kc j (fun v => (glAt X j A v)⁻¹) (subD X Kc j (MvPolynomial.X x)) := by
    intro x
    rw [subD_subst_X, ySub_tau, subD_X, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rfl
  have key := ringHom_scale
    ((subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j).comp
      ((X.Pj j).subst fun v s => (X.Pj j).gPos v s ((A v)⁻¹ : GL _ _) : (X.Pj j).Xsp →+* (X.Pj j).Xsp))
    ((lamB X Kc j fun v => (glAt X j A v)⁻¹ : DA X Kc j →+* DA X Kc j).comp (subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j))
    (fun x => cD X Kc j (if IsOddPos (blkJ X j x).2 then (ec X Kc j (glAt X j A) (blkJ X j x).1 (blkJ X j x).2)⁻¹ else 1))
    (fun a => by simpa only [RingHom.comp_apply, RingHom.coe_coe] using hC a)
    (fun x => by simpa only [RingHom.comp_apply, RingHom.coe_coe] using hX x)
    (cD X Kc j (s1 X Kc j (glAt X j A))) G ?_
  · simpa only [RingHom.comp_apply, RingHom.coe_coe] using key
  · intro m hm
    simp only [← map_pow, ← map_prod]
    congr 1
    rw [← Finset.prod_fiberwise univ (blkJ X j)]
    unfold s1
    refine Finset.prod_congr rfl fun b _ => ?_
    have h2 : ∏ x ∈ univ.filter (fun x => blkJ X j x = b),
        (if IsOddPos (blkJ X j x).2 then (ec X Kc j (glAt X j A) (blkJ X j x).1 (blkJ X j x).2)⁻¹ else 1) ^ m x =
        (if IsOddPos b.2 then (ec X Kc j (glAt X j A) b.1 b.2)⁻¹ else 1) ^
          (∑ x ∈ univ.filter (fun x => blkJ X j x = b), m x) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    rw [h2]
    by_cases hb : IsOddPos b.2
    · rw [if_pos hb, if_pos hb, ← hO m hm b hb, zpow_neg, zpow_natCast, inv_pow]
    · rw [if_neg hb, if_neg hb, one_pow]

def cB (j : ℕ) (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) : Kc :=
  algebraMap X.G.Kf Kc (s0 X j A) * s1 X Kc j (glAt X j A) * d1 X Kc j (glAt X j A) * (n1 X Kc j (glAt X j A))⁻¹

theorem delF_equiv (j : ℕ) (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) (G : (X.Pj j).Xsp)
    (f : MvPowerSeries (X.ZA j) Kc) (hG : GoodG X Kc j G) (hO : OddDeg X j G) :
    GoodG X Kc j ((X.Pj j).natAct A G) ∧
      delF X Kc j ((X.Pj j).natAct A G) (SA X Kc j (glAt X j A) f) = cB X Kc j A • delF X Kc j G f :=
  delF_core X Kc j (glAt X j A) G _ _ (subD_natAct X Kc j A G hO) hG f

end Final

section Scalar

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

def eJ : (j : ℕ) → (v : X.Pl) → Fin (X.G.P.n' v) → ℤ
  | 0, v, s => lamAt (X.G.P.lam0 v) s (Fin.last _)
  | j + 1, v, s => lamAt ((X.Fl.Pj (j + 1)).lam0 v) s (Fin.last _)

theorem alg_det_tw {n : Type} [Fintype n] [DecidableEq n] (v : X.Pl) (s : Fin (X.G.P.n' v)) (M : Matrix n n (X.G.P.Qq v)) :
    algebraMap X.G.Kf Kc (M.map fun x => X.G.P.ι v ((X.G.P.σ v ^ s.val) x)).det = tw X Kc v s M.det :=
  (RingHom.map_det (algebraMap X.G.Kf Kc) _).trans (RingHom.map_det (tw X Kc v s) M).symm

theorem algebraMap_twisted_det_product (j : ℕ) (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) :
    algebraMap X.G.Kf Kc (s0 X j A) = ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v),
      (tw X Kc v s (glAt X j A v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det) ^
        (-(eJ X j v s)) := by
  cases j <;>
  · unfold s0
    simp only [map_prod, map_zpow₀]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    congr 1
    exact alg_det_tw X Kc v s _

theorem tw_det_ne (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    tw X Kc v s (B v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (hM_mul_gM X Kc j B v s)
  rw [Matrix.det_mul, Matrix.det_one, det_mAt X Kc j v s (B v), h, mul_zero] at h1
  exact zero_ne_one h1

theorem ec_eq (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    ec X Kc j B v s = if IsOddPos s
      then tw X Kc v s (B v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det
      else (tw X Kc v s (B v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det)⁻¹ := by
  unfold ec
  rw [cf_inv]
  by_cases h : IsOddPos s
  · rw [if_pos h, if_pos h, det_mAt]
  · rw [if_neg h, if_neg h, Matrix.det_transpose]
    have h1 := congrArg Matrix.det (hM_mul_gM X Kc j B v s)
    rw [Matrix.det_mul, Matrix.det_one, det_mAt X Kc j v s (B v)] at h1
    exact eq_inv_of_mul_eq_one_left h1

def NumE : Prop := ∀ (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)), ¬ IsOddPos s →
  0 ≤ X.nuv v (j + 1) s (NN X.G.P.m X.t j) ∧ X.nuv v (j + 1) s (NN X.G.P.m X.t j) = eJ X j v s + X.w v (j + 1) s

def NumO : Prop := ∀ (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)), IsOddPos s →
  cMu X j v s = X.w v (j + 1) s - eJ X j v s

theorem cB_eq (hE : NumE X) (hO : NumO X) (j : ℕ)
    (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) :
    cB X Kc j A = cA X Kc j (glAt X j A) := by
  unfold cB cA s1 d1 n1
  rw [algebraMap_twisted_det_product, Fintype.prod_sigma]
  simp only [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
  have hD := tw_det_ne X Kc j (glAt X j A) v s
  rw [ec_eq]
  by_cases h : IsOddPos s
  · simp only [if_pos h]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hD, ← zpow_add₀ hD, ← zpow_add₀ hD]
    congr 1
    have h1 := Int.toNat_sub_toNat_neg (exT X j v s)
    have h2 := hO j v s h
    have h3 : exT X j v s = cMu X j v s - (NN X.G.P.m X.t j : ℤ) * cMu X j v s + szMu X j v s := rfl
    linarith
  · simp only [if_neg h]
    obtain ⟨h0, h1⟩ := hE j v s h
    rw [mul_one, mul_one, inv_pow, inv_inv, ← zpow_natCast, Int.toNat_of_nonneg h0, ← zpow_add₀ hD]
    congr 1
    linarith

def DelEquivH : Prop :=
  ∀ (j : ℕ) (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) (G : (X.Pj j).Xsp)
    (f : MvPowerSeries (X.ZA j) Kc), GoodG X Kc j G → OddDeg X j G →
    GoodG X Kc j ((X.Pj j).natAct A G) ∧
    delF X Kc j ((X.Pj j).natAct A G) (SA X Kc j (glAt X j A) f) = cA X Kc j (glAt X j A) • delF X Kc j G f

theorem delEquivH_of (hE : NumE X) (hO : NumO X) : DelEquivH X Kc := fun j A G f hG hOd => by
  rw [← cB_eq X Kc hE hO j A]
  exact delF_equiv X Kc j A G f hG hOd

end Scalar

section Numbers

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem numO : NumO X := by
  intro j v s h
  have hne : ¬ Even s.val := by
    rw [Nat.not_even_iff]
    exact h
  have h1 : cMu X j v s = X.G.P.lam0 v s 0 + X.w v (j + 1) s := by
    unfold cMu Sys.nuv nu lamI
    rw [if_pos ⟨le_refl 1, by omega⟩, dif_pos ⟨le_refl 1, by omega⟩]
    rfl
  have h2 : eJ X j v s = -X.G.P.lam0 v s 0 := by
    cases j with
    | zero =>
      show lamAt _ s _ = _
      unfold lamAt
      rw [if_neg hne, Fin.rev_last]
    | succ j =>
      show lamAt _ s _ = _
      unfold lamAt
      rw [if_neg hne, Fin.rev_last]
      show -liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (j + 1) 0 = _
      unfold liftWt
      rw [dif_pos (by simp)]
      rfl
  rw [h1, h2]
  ring

theorem succ_mul_succ_sub_one_div_succ (j t : ℕ) : ((j + 1) * (t + 1) - 1) / (t + 1) = j :=
  Nat.div_eq_of_lt_le (by rw [Nat.succ_mul]; omega) (by
    have : 0 < (j + 1) * (t + 1) := by positivity
    omega)

theorem numE : NumE X := by
  intro j v s h
  have hev : Even s.val := Nat.even_iff.2 (by unfold IsOddPos at h; omega)
  cases j with
  | zero =>
    have h1 : X.nuv v (0 + 1) s (NN X.G.P.m X.t 0) = X.G.P.lam0 v s (Fin.last _) + X.w v (0 + 1) s := by
      have hN : NN X.G.P.m X.t 0 = X.G.P.m + 1 := by unfold NN; omega
      rw [hN]
      unfold Sys.nuv nu lamI
      rw [if_pos ⟨by omega, le_refl _⟩, dif_pos ⟨by omega, le_refl _⟩]
      rfl
    have h2 : eJ X 0 v s = X.G.P.lam0 v s (Fin.last _) := by
      show lamAt _ s _ = _
      unfold lamAt
      rw [if_pos hev]
    have h3 := X.Fl.w_ge v s
    have h4 : -(X.G.P.lam0 v s (Fin.last X.G.P.m)) ≤ X.Fl.w v 1 s := le_trans (le_max_right _ _) h3
    rw [h1, h2]
    refine ⟨?_, rfl⟩
    show 0 ≤ X.G.P.lam0 v s (Fin.last _) + X.Fl.w v 1 s
    linarith
  | succ j =>
    have hpos : 0 < (j + 1) * (X.t + 1) := by positivity
    have hN : NN X.G.P.m X.t (j + 1) = X.G.P.m + 1 + (j + 1) * (X.t + 1) := rfl
    have h1 : X.nuv v (j + 1 + 1) s (NN X.G.P.m X.t (j + 1)) = -X.w v (j + 1) s + X.w v (j + 1 + 1) s := by
      unfold Sys.nuv nu
      rw [if_neg (by intro hh; have := hh.2; rw [hN] at this; omega),
        if_pos ⟨by rw [hN]; omega, NN_le X (j + 1)⟩]
      rw [hN, show X.G.P.m + 1 + (j + 1) * (X.t + 1) - (X.G.P.m + 2) = (j + 1) * (X.t + 1) - 1 by omega, succ_mul_succ_sub_one_div_succ]
    have h2 : eJ X (j + 1) v s = -X.w v (j + 1) s := by
      have hpos' : 0 < (j + 1) * (X.Fl.t + 1) := by positivity
      show lamAt _ s _ = _
      unfold lamAt
      rw [if_pos hev]
      show liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (j + 1) (Fin.last _) = _
      unfold liftWt
      rw [dif_neg (by simp only [Fin.val_last]; omega)]
      simp only [Fin.val_last]
      rw [show X.G.P.m + (j + 1) * (X.Fl.t + 1) - (X.G.P.m + 1) = (j + 1) * (X.Fl.t + 1) - 1 by omega, succ_mul_succ_sub_one_div_succ]
    have h3 : X.Fl.w v (j + 1) s ≤ X.Fl.w v (j + 1 + 1) s := X.Fl.w_mono v s (j + 1) (by omega)
    rw [h1, h2]
    refine ⟨?_, rfl⟩
    show 0 ≤ -X.Fl.w v (j + 1) s + X.Fl.w v (j + 1 + 1) s
    linarith

variable (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

theorem delEquivH : DelEquivH X Kc := delEquivH_of X Kc (numE X) (numO X)

end Numbers

end Formalism.L2.G.Pend
