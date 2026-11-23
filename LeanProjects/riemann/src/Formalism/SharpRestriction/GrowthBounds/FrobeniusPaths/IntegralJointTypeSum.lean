import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSumOfParts

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Ops

variable {F : Type*} [Field F] {N m k : ℕ} (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k)

lemma glOps_eq_E (a b : Fin m) : glOps F m LL S a b = glOpsE F LL S (id : Fin m → Fin m) a b := rfl

lemma glOpsE_mul (a b : Fin m) (f g : MvPolynomial (Fin N × Fin k) F) :
    glOpsE F LL S e a b (f * g) = f * glOpsE F LL S e a b g + g * glOpsE F LL S e a b f := by
  simp only [glOpsE, LinearMap.sum_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp [Derivation.leibniz] <;> ring

lemma glOpsE_C (a b : Fin m) (c : F) : glOpsE F LL S e a b (C c) = 0 := by
  simp only [glOpsE, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro l _
  split_ifs <;> simp

open Classical in
lemma glOpsE_X (a b : Fin m) (v : Fin N × Fin k) :
    glOpsE F LL S e a b (X v) =
      if v.1 ∈ S then (if LL.vec v.1 then (if v.2 = e b then X (v.1, e a) else 0)
        else (if v.2 = e a then -X (v.1, e b) else 0)) else 0 := by
  simp only [glOpsE, LinearMap.sum_apply]
  rw [Finset.sum_eq_single v.1]
  · obtain ⟨l, c⟩ := v
    simp only
    split_ifs <;> simp_all [pderiv_X]
  · intro l _ hl
    obtain ⟨l', c⟩ := v
    simp only at hl
    split_ifs <;> simp [pderiv_X, Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ _) h

end Ops

section Inter

variable {n : ℕ} {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

lemma inter_umon (E : GLOps n K V) (E' : GLOps n K W) (T : V →ₗ[K] W) (hT : ∀ a b x, T (E a b x) = E' a b (T x))
    (u : Module.End K V) (hu : u ∈ Umon E) : ∃ u' ∈ Umon E', ∀ x, T (u x) = u' (T x) := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    obtain ⟨ab, rfl⟩ := hu
    exact ⟨E' ab.1 ab.2, Submonoid.subset_closure ⟨ab, rfl⟩, hT _ _⟩
  | one => exact ⟨1, Submonoid.one_mem _, fun x => rfl⟩
  | mul u1 u2 _ _ h1 h2 =>
    obtain ⟨v1, hv1, e1⟩ := h1
    obtain ⟨v2, hv2, e2⟩ := h2
    exact ⟨v1 * v2, Submonoid.mul_mem _ hv1 hv2, fun x => by
      rw [Module.End.mul_apply, e1, e2, Module.End.mul_apply]⟩

lemma inter_iso (E : GLOps n K V) (E' : GLOps n K W) (T : V →ₗ[K] W) (hT : ∀ a b x, T (E a b x) = E' a b (T x))
    (lam : Fin n → ℤ) (x : V) (hx : x ∈ isoSub E lam) : T x ∈ isoSub E' lam := by
  unfold isoSub at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', e1⟩ := inter_umon E E' T hT u hu
    rw [e1]
    by_cases h0 : T v = 0
    · rw [h0, map_zero]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨u', hu', T v, ⟨h0, ?_, ?_⟩, rfl⟩
      · have h2 := hv.2.1
        simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply] at h2 ⊢
        intro a
        rw [← hT, ← map_smul, ← map_sub, h2 a, map_zero]
      · intro a b hab
        rw [← hT, hv.2.2 a b hab, map_zero]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [map_smul]; exact Submodule.smul_mem _ _ h

end Inter

section Deg

variable {F : Type*} [Field F] {N m k : ℕ} (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k)

lemma coeff_XD {σ : Type*} (i j : σ) (f : MvPolynomial σ F) (mm : σ →₀ ℕ) :
    coeff mm (X i * pderiv j f) =
      if mm i = 0 then 0 else
        coeff (mm - Finsupp.single i 1 + Finsupp.single j 1) f * (((mm - Finsupp.single i 1 : σ →₀ ℕ) j : ℕ) + 1 : F) := by
  classical
  rw [coeff_X_mul']
  by_cases h : mm i = 0
  · rw [if_neg (by simpa using h), if_pos h]
  · rw [if_pos (by simpa using h), if_neg h, coeff_pderiv]

lemma coeff_XDii {σ : Type*} (i : σ) (f : MvPolynomial σ F) (mm : σ →₀ ℕ) :
    coeff mm (X i * pderiv i f) = (mm i : F) * coeff mm f := by
  rw [coeff_XD]
  by_cases h : mm i = 0
  · rw [if_pos h, h]; simp
  · rw [if_neg h]
    have h1 : Finsupp.single i 1 ≤ mm := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    rw [tsub_add_cancel_of_le h1]
    have h2 : ((mm - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) + 1 = mm i := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      omega
    have h3 : (((mm - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) + 1 : F) = (mm i : F) := by
      rw [← h2, Nat.cast_add, Nat.cast_one]
    rw [h3, mul_comm]

open Classical in

def wtA (mm : Fin N × Fin k →₀ ℕ) (a : Fin m) : ℤ :=
  ∑ l : Fin N, if l ∈ S then (if LL.vec l then (mm (l, e a) : ℤ) else -(mm (l, e a) : ℤ)) else 0

def tot (mm : Fin N × Fin k →₀ ℕ) : ℤ := ∑ a, wtA LL S e mm a

lemma coeff_Eaa (a : Fin m) (f : MvPolynomial (Fin N × Fin k) F) (mm : Fin N × Fin k →₀ ℕ) :
    coeff mm (glOpsE F LL S e a a f) = (wtA LL S e mm a : F) * coeff mm f := by
  simp only [glOpsE, LinearMap.sum_apply, coeff_sum, wtA]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs
  · simp [coeff_XDii]
  · simp [coeff_XDii]
  · simp

lemma tot_add (m1 m2 : Fin N × Fin k →₀ ℕ) : tot LL S e (m1 + m2) = tot LL S e m1 + tot LL S e m2 := by
  simp only [tot, wtA]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp <;> ring

open Classical in
lemma tot_single (he : Function.Injective e) (l : Fin N) (c : Fin m) :
    tot LL S e (Finsupp.single (l, e c) 1) = if l ∈ S then (if LL.vec l then 1 else -1) else 0 := by
  simp only [tot, wtA]
  rw [Finset.sum_eq_single c, Finset.sum_eq_single l]
  · simp
  · intro l' _ hl'
    have : (Finsupp.single (l, e c) 1 : Fin N × Fin k →₀ ℕ) (l', e c) = 0 := by
      rw [Finsupp.single_apply, if_neg]; intro h; exact hl' (congrArg Prod.fst h).symm
    rw [this]; simp
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro l' _
    have : (Finsupp.single (l, e c) 1 : Fin N × Fin k →₀ ℕ) (l', e a) = 0 := by
      rw [Finsupp.single_apply, if_neg]; intro h; exact ha (he (congrArg Prod.snd h)).symm
    rw [this]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

def TotSub (F : Type*) [Field F] {N m k : ℕ} (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k) (s : ℤ) :
    Submodule F (MvPolynomial (Fin N × Fin k) F) :=
  MvPolynomial.restrictSupport F {mm | tot LL S e mm = s}

lemma XD_mem (he : Function.Injective e) (s : ℤ) (l : Fin N) (c d : Fin m) (f : MvPolynomial (Fin N × Fin k) F)
    (hf : f ∈ TotSub F LL S e s) : X (l, e c) * pderiv (l, e d) f ∈ TotSub F LL S e s := by
  unfold TotSub at hf ⊢
  rw [MvPolynomial.mem_restrictSupport_iff] at hf ⊢
  intro mm hmm
  rw [Finset.mem_coe, mem_support_iff, coeff_XD] at hmm
  by_cases h : mm (l, e c) = 0
  · rw [if_pos h] at hmm; exact absurd rfl hmm
  · rw [if_neg h] at hmm
    have h0 : coeff (mm - Finsupp.single (l, e c) 1 + Finsupp.single (l, e d) 1) f ≠ 0 := left_ne_zero_of_mul hmm
    have h1 := hf (Finset.mem_coe.2 (mem_support_iff.2 h0))
    have h2 : Finsupp.single (l, e c) 1 ≤ mm := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    simp only [Set.mem_ofPred_eq] at h1 ⊢
    rw [tot_add, tot_single LL S e he] at h1
    rw [← tsub_add_cancel_of_le h2, tot_add, tot_single LL S e he]
    exact h1

lemma E_mem (he : Function.Injective e) (s : ℤ) (c d : Fin m) (f : MvPolynomial (Fin N × Fin k) F)
    (hf : f ∈ TotSub F LL S e s) : glOpsE F LL S e c d f ∈ TotSub F LL S e s := by
  simp only [glOpsE, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro l _
  split_ifs
  · exact XD_mem LL S e he s l c d f hf
  · simp only [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (XD_mem LL S e he s l d c f hf)
  · exact Submodule.zero_mem _

lemma U_mem (he : Function.Injective e) (s : ℤ) (u : Module.End F (MvPolynomial (Fin N × Fin k) F))
    (hu : u ∈ Umon (glOpsE F LL S e)) (f : MvPolynomial (Fin N × Fin k) F)
    (hf : f ∈ TotSub F LL S e s) : u f ∈ TotSub F LL S e s := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction generalizing f with
  | mem u hu =>
    obtain ⟨ab, rfl⟩ := hu
    exact E_mem LL S e he s _ _ f hf
  | one => exact hf
  | mul u1 u2 _ _ h1 h2 => exact h1 _ (h2 _ hf)

lemma hwv_mem [CharZero F] (lam : Fin m → ℤ) (v : MvPolynomial (Fin N × Fin k) F)
    (hv : v ∈ weightSp (glOpsE F LL S e) lam) : v ∈ TotSub F LL S e (∑ a, lam a) := by
  unfold TotSub
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm
  rw [Finset.mem_coe, mem_support_iff] at hmm
  simp only [Set.mem_ofPred_eq, tot]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] at hv
  have h1 := congrArg (coeff mm) (hv a)
  rw [coeff_sub, coeff_Eaa, coeff_smul, coeff_zero, smul_eq_mul, ← sub_mul] at h1
  rcases mul_eq_zero.1 h1 with h | h
  · exact_mod_cast sub_eq_zero.1 h
  · exact absurd h hmm

lemma iso_le_tot [CharZero F] (he : Function.Injective e) (lam : Fin m → ℤ) :
    isoSub (glOpsE F LL S e) lam ≤ TotSub F LL S e (∑ a, lam a) := by
  unfold isoSub
  rw [Submodule.span_le]
  rintro x ⟨u, hu, v, hv, rfl⟩
  exact U_mem LL S e he _ u hu v (hwv_mem LL S e lam v hv.2.1)

lemma sum_lt_succ (g : Fin N → ℤ) (l : Fin N) [DecidablePred (· ∈ {j : Fin N | j.val < l.succ.val})]
    [DecidablePred (· ∈ {j : Fin N | j.val < l.castSucc.val})] :
    (∑ j : Fin N, if j ∈ {j : Fin N | j.val < l.succ.val} then g j else 0) =
      (∑ j : Fin N, if j ∈ {j : Fin N | j.val < l.castSucc.val} then g j else 0) + g l := by
  have h : ∀ j : Fin N, (if j ∈ {j : Fin N | j.val < l.succ.val} then g j else 0) =
      (if j ∈ {j : Fin N | j.val < l.castSucc.val} then g j else 0) + (if j = l then g j else 0) := by
    intro j
    simp only [Set.mem_ofPred_eq, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, Finset.sum_ite_eq' univ l g]
  simp

lemma deg_of_iso [CharZero F] (he : Function.Injective e) (lam : Fin (N + 1) → Fin m → ℤ)
    (x : MvPolynomial (Fin N × Fin k) F)
    (hx : ∀ i : Fin (N + 1), x ∈ isoSub (glOpsE F LL {j | j.val < i.val} e) (lam i))
    (mm : Fin N × Fin k →₀ ℕ) (hmm : mm ∈ x.support) (l : Fin N) :
    (∑ a, (if LL.vec l then (mm (l, e a) : ℤ) else -(mm (l, e a) : ℤ))) =
      ∑ a, lam l.succ a - ∑ a, lam l.castSucc a := by
  have h : ∀ i : Fin (N + 1), tot LL {j | j.val < i.val} e mm = ∑ a, lam i a := by
    intro i
    have := iso_le_tot LL {j | j.val < i.val} e he (lam i) (hx i)
    unfold TotSub at this
    rw [MvPolynomial.mem_restrictSupport_iff] at this
    exact this (Finset.mem_coe.2 hmm)
  rw [← h l.succ, ← h l.castSucc]
  simp only [tot, wtA]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have h5 := @sum_lt_succ N (fun j => if LL.vec j then (mm (j, e a) : ℤ) else -(mm (j, e a) : ℤ)) l
    (fun _ => Classical.propDecidable _) (fun _ => Classical.propDecidable _)
  exact eq_sub_of_add_eq ((add_comm _ _).trans h5.symm)

lemma deg_of_iso_path [CharZero F] (he : Function.Injective e) (b : Fin N → ℕ) (P : PPath m N LL b)
    (x : MvPolynomial (Fin N × Fin k) F)
    (hx : ∀ i : Fin (N + 1), x ∈ isoSub (glOpsE F LL {j | j.val < i.val} e) (P.mu i))
    (mm : Fin N × Fin k →₀ ℕ) (hmm : mm ∈ x.support) (l : Fin N) : ∑ a, mm (l, e a) = b l := by
  have h1 := deg_of_iso LL e he P.mu x hx mm hmm l
  have h2 := size_of_path P l
  have h3 : ((∑ a, mm (l, e a) : ℕ) : ℤ) = (b l : ℤ) := by
    push_cast
    by_cases hv : LL.vec l
    · simp only [hv, if_true] at h1 h2
      rw [h1, h2]
    · simp only [hv, if_false, Bool.false_eq_true, Finset.sum_neg_distrib] at h1 h2
      rw [h2]; linarith
  exact_mod_cast h3

end Deg

theorem hjb_pf (D : Formalism.BasicNotions.D7) : HJb D := by
  intro F _ _ N r K _ _ LL B nu ka hP x hx
  obtain ⟨b', b'', hb, ⟨P1, rfl⟩, ⟨P2, rfl⟩⟩ := hP
  simp only [jointType, Submodule.mem_iInf, Submodule.mem_inf] at hx
  unfold Pol
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm l
  have h1 := deg_of_iso_path LL (Fin.castAdd K) (Fin.castAdd_injective r K) b' P1 x (fun i => (hx i).1) mm hmm l
  have h2 := deg_of_iso_path LL (Fin.natAdd r) (Fin.natAdd_injective K r) b'' P2 x (fun i => (hx i).2) mm hmm l
  unfold multideg
  rw [Fin.sum_univ_add, h1, h2, hb]

section Ev

variable {F : Type*} [Field F] {N m k : ℕ} (LL : Letters (Fin N)) (e : Fin m → Fin k) (dcd : Fin k → Option (Fin m))

def Tev (y : Fin N × Fin k → F) : MvPolynomial (Fin N × Fin k) F →ₐ[F] MvPolynomial (Fin N × Fin m) F :=
  aeval fun v => (dcd v.2).elim (C (y v)) (fun a => X (v.1, a))

lemma Tev_X (y : Fin N × Fin k → F) (v : Fin N × Fin k) :
    Tev dcd y (X v) = (dcd v.2).elim (C (y v)) (fun a => X (v.1, a)) := by
  unfold Tev; rw [aeval_X]

lemma Tev_C (y : Fin N × Fin k → F) (c : F) : Tev dcd y (C c) = C c := by
  unfold Tev; rw [aeval_C]; rfl

lemma Tev_gen (hd1 : ∀ a, dcd (e a) = some a) (hd2 : ∀ c a, dcd c = some a → c = e a) (S : Set (Fin N))
    (y : Fin N × Fin k → F) (a b : Fin m) (v : Fin N × Fin k) :
    Tev dcd y (glOpsE F LL S e a b (X v)) = glOpsE F LL S (id : Fin m → Fin m) a b (Tev dcd y (X v)) := by
  classical
  have he : Function.Injective e := fun a b h => by
    have := hd1 a; rw [h, hd1] at this; exact (Option.some.inj this).symm
  obtain ⟨l, c⟩ := v
  rw [Tev_X, glOpsE_X]
  dsimp only
  cases h : dcd c with
  | none =>
    have h1 : ∀ a', c ≠ e a' := fun a' hc => by rw [hc, hd1] at h; exact absurd h (by simp)
    simp [h1 a, h1 b, glOpsE_C]
  | some c' =>
    have hc : c = e c' := hd2 _ _ h
    subst hc
    simp only [Option.elim]
    rw [glOpsE_X]
    simp only [he.eq_iff, id]
    split_ifs <;> simp [Tev_X, hd1]

lemma Tev_inter (hd1 : ∀ a, dcd (e a) = some a) (hd2 : ∀ c a, dcd c = some a → c = e a) (S : Set (Fin N))
    (y : Fin N × Fin k → F) (a b : Fin m) (f : MvPolynomial (Fin N × Fin k) F) :
    Tev dcd y (glOpsE F LL S e a b f) = glOpsE F LL S (id : Fin m → Fin m) a b (Tev dcd y f) := by
  induction f using MvPolynomial.induction_on with
  | C c => rw [glOpsE_C, map_zero, Tev_C, glOpsE_C]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p v ih =>
    rw [glOpsE_mul, map_add, map_mul, map_mul, map_mul, glOpsE_mul, ih, Tev_gen LL e dcd hd1 hd2]

lemma eval_Tev (hd2 : ∀ c a, dcd c = some a → c = e a) (z : Fin N × Fin k → F)
    (f : MvPolynomial (Fin N × Fin k) F) :
    eval (fun v' : Fin N × Fin m => z (v'.1, e v'.2)) (Tev dcd z f) = eval z f := by
  induction f using MvPolynomial.induction_on with
  | C c => rw [Tev_C, eval_C, eval_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v ih =>
    rw [map_mul, map_mul, map_mul, ih, Tev_X, eval_X]
    congr 1
    obtain ⟨l, c⟩ := v
    dsimp only
    cases h : dcd c with
    | none => simp only [Option.elim, eval_C]
    | some a => simp only [Option.elim, eval_X]; rw [← hd2 c a h]

lemma exists_Tev_ne [Infinite F] (hd2 : ∀ c a, dcd c = some a → c = e a) (x : MvPolynomial (Fin N × Fin k) F)
    (hx : x ≠ 0) : ∃ y, Tev dcd y x ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hx
  apply MvPolynomial.funext
  intro z
  rw [← eval_Tev e dcd hd2 z x, hcon z, map_zero, map_zero]

end Ev

def dOf {N m : ℕ} (LL : Letters (Fin N)) (lam : Fin (N + 1) → Fin m → ℤ) : Fin N → ℕ := fun l =>
  (if LL.vec l then ∑ a, lam l.succ a - ∑ a, lam l.castSucc a else ∑ a, lam l.castSucc a - ∑ a, lam l.succ a).toNat

theorem path_of_iso (D : Formalism.BasicNotions.D7) (h14 : JointComponentsPaths D) {F : Type} [Field F] [CharZero F] {N m k : ℕ}
    (LL : Letters (Fin N)) (e : Fin m → Fin k) (dcd : Fin k → Option (Fin m))
    (hd1 : ∀ a, dcd (e a) = some a) (hd2 : ∀ c a, dcd c = some a → c = e a)
    (lam : Fin (N + 1) → Fin m → ℤ) (x : MvPolynomial (Fin N × Fin k) F) (hx0 : x ≠ 0)
    (hx : ∀ i : Fin (N + 1), x ∈ isoSub (glOpsE F LL {j | j.val < i.val} e) (lam i)) :
    ∃ d : Fin N → ℕ, ∃ P : PPath m N LL d, P.mu = lam := by
  obtain ⟨y, hy⟩ := exists_Tev_ne e dcd hd2 x hx0
  have h1 : ∀ i : Fin (N + 1),
      Tev dcd y x ∈ isoSub (glOpsE F LL {j | j.val < i.val} (id : Fin m → Fin m)) (lam i) := fun i =>
    inter_iso _ _ (Tev dcd y).toLinearMap (fun a b f => Tev_inter LL e dcd hd1 hd2 _ y a b f) (lam i) x (hx i)
  refine ⟨dOf LL lam, ?_⟩
  by_contra hno
  have h2 := (h14 F N m LL (dOf LL lam) lam).2 hno
  have h3 : Tev dcd y x ∈ Pol F m (dOf LL lam) ⊓
      ⨅ i : Fin (N + 1), isoSub (glOps F m LL {l | l.val < i.val}) (lam i) := by
    refine ⟨?_, ?_⟩
    · unfold Pol
      rw [SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
      intro mm hmm l
      have h5 := deg_of_iso LL (id : Fin m → Fin m) Function.injective_id lam _ h1 mm hmm l
      have h4 : ((multideg mm l : ℕ) : ℤ) = (if LL.vec l then ∑ a, lam l.succ a - ∑ a, lam l.castSucc a
          else ∑ a, lam l.castSucc a - ∑ a, lam l.succ a) := by
        unfold multideg
        push_cast
        by_cases hv : LL.vec l
        · simp only [hv, if_true, id] at h5 ⊢
          exact h5
        · simp only [hv, Bool.false_eq_true, if_false, Finset.sum_neg_distrib, id] at h5 ⊢
          linarith
      unfold dOf
      rw [← h4, Int.toNat_natCast]
    · rw [SetLike.mem_coe, Submodule.mem_iInf]
      exact h1
  rw [h2] at h3
  exact hy ((Submodule.mem_bot F).1 h3)

def dcdPl (r K : ℕ) : Fin (r + K) → Option (Fin r) := fun c => if h : c.val < r then some ⟨c.val, h⟩ else none

def dcdTan (r K : ℕ) : Fin (r + K) → Option (Fin K) := fun c =>
  if h : r ≤ c.val then some ⟨c.val - r, by have := c.isLt; omega⟩ else none

lemma dcdPl_1 (r K : ℕ) (a : Fin r) : dcdPl r K (Fin.castAdd K a) = some a := by
  unfold dcdPl
  rw [dif_pos (show (Fin.castAdd K a).val < r from a.2)]
  rfl

lemma dcdPl_2 (r K : ℕ) (c : Fin (r + K)) (a : Fin r) (h : dcdPl r K c = some a) : c = Fin.castAdd K a := by
  unfold dcdPl at h
  by_cases hc : c.val < r
  · rw [dif_pos hc] at h
    rw [← Option.some.inj h]
    ext; rfl
  · rw [dif_neg hc] at h
    exact absurd h (by simp)

lemma dcdTan_1 (r K : ℕ) (a : Fin K) : dcdTan r K (Fin.natAdd r a) = some a := by
  unfold dcdTan
  rw [dif_pos (show r ≤ (Fin.natAdd r a).val by simp)]
  congr 1
  ext; simp

lemma dcdTan_2 (r K : ℕ) (c : Fin (r + K)) (a : Fin K) (h : dcdTan r K c = some a) : c = Fin.natAdd r a := by
  unfold dcdTan at h
  by_cases hc : r ≤ c.val
  · rw [dif_pos hc] at h
    rw [← Option.some.inj h]
    ext; simp; omega
  · rw [dif_neg hc] at h
    exact absurd h (by simp)

theorem hjc_pf (D : Formalism.BasicNotions.D7) (h14 : JointComponentsPaths D) : HJc D := by
  intro F _ _ N r K _ _ LL nu ka hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  simp only [jointType, Submodule.mem_iInf, Submodule.mem_inf] at hx
  obtain ⟨b', hb'⟩ := path_of_iso D h14 LL (Fin.castAdd K) (dcdPl r K) (dcdPl_1 r K) (dcdPl_2 r K) nu x hx0
    (fun i => (hx i).1)
  obtain ⟨b'', hb''⟩ := path_of_iso D h14 LL (Fin.natAdd r) (dcdTan r K) (dcdTan_1 r K) (dcdTan_2 r K) ka x hx0
    (fun i => (hx i).2)
  exact ⟨b', b'', hb', hb''⟩

theorem integral_joint_type_sum (D : Formalism.BasicNotions.D7) (h14 : JointComponentsPaths D) (h16 : PairedPathIndependence D) : IntegralJointTypeSum D :=
  integral_joint_type_sum_of_parts D h16 (hjb_pf D) (hjc_pf D h14)

end Formalism.MainNotions.LemmaBAlt
