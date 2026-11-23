import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.LzExist

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

def IsDecomp (S : Finset A) : Prop :=
  (∀ e ∈ S, e * e = e) ∧ (∀ e ∈ S, ∀ z : A, e * z = z * e) ∧ (∀ e ∈ S, e ≠ 0) ∧
    (∀ e ∈ S, ∀ f ∈ S, e ≠ f → e * f = 0) ∧ ∑ e ∈ S, e = 1

def IsPrim (S : Finset A) : Prop :=
  ∀ t ∈ S, ∀ x : A, x * x = x → (∀ z, x * z = z * x) → x * t = x → x = 0 ∨ x = t

theorem linInd {S : Finset A} (h : IsDecomp S) : LinearIndependent ℂ (fun x : S => (x : A)) := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h1 : (∑ j ∈ s, c j • (j : A)) * (i : A) = c i • (i : A) := by
    rw [Finset.sum_mul, Finset.sum_eq_single i]
    · rw [smul_mul_assoc, h.1 _ i.2]
    · intro j _ hji
      rw [smul_mul_assoc, h.2.2.2.1 _ j.2 _ i.2 (fun e => hji (Subtype.ext e)), smul_zero]
    · intro h'; exact absurd hi h'
  rw [hs, zero_mul] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right (h.2.2.1 _ i.2)

theorem card_le [Module.Finite ℂ A] {S : Finset A} (h : IsDecomp S) : S.card ≤ Module.finrank ℂ A := by
  have := (linInd h).fintype_card_le_finrank
  simpa using this

theorem refine_decomp [DecidableEq A] {S : Finset A} (h : IsDecomp S) {t : A} (ht : t ∈ S) {x : A}
    (hx : x * x = x) (hc : ∀ z, x * z = z * x) (hxt : x * t = x) (h0 : x ≠ 0) (ht' : x ≠ t) :
    IsDecomp (insert x (insert (t - x) (S.erase t))) ∧
      (insert x (insert (t - x) (S.erase t))).card = S.card + 1 := by
  obtain ⟨hI, hC, hN, hO, hS⟩ := h
  have htx : t * x = x := by rw [← hc t, hxt]
  have hxs : ∀ s ∈ S.erase t, x * s = 0 := by
    intro s hs
    obtain ⟨hst, hs⟩ := Finset.mem_erase.1 hs
    rw [← hxt, mul_assoc, hO t ht s hs (Ne.symm hst), mul_zero]
  have hsx : ∀ s ∈ S.erase t, s * x = 0 := fun s hs => by rw [← hc s]; exact hxs s hs
  have hts : ∀ s ∈ S.erase t, (t - x) * s = 0 := by
    intro s hs
    obtain ⟨hst, hs'⟩ := Finset.mem_erase.1 hs
    rw [sub_mul, hO t ht s hs' (Ne.symm hst), hxs s hs, sub_zero]
  have hst' : ∀ s ∈ S.erase t, s * (t - x) = 0 := by
    intro s hs
    obtain ⟨hst, hs'⟩ := Finset.mem_erase.1 hs
    rw [mul_sub, hO s hs' t ht hst, hsx s hs, sub_zero]
  have hxtx : x * (t - x) = 0 := by rw [mul_sub, hxt, hx, sub_self]
  have htxx : (t - x) * x = 0 := by rw [sub_mul, htx, hx, sub_self]
  have htt : (t - x) * (t - x) = t - x := by
    rw [mul_sub, htxx, sub_zero, sub_mul, hI t ht, hxt]
  have htx0 : t - x ≠ 0 := fun h => ht' (sub_eq_zero.1 h).symm
  have hnot : ∀ y, y * y = y → y ≠ 0 → (∀ s ∈ S.erase t, y * s = 0) → y ∉ S.erase t := by
    intro y hy hy0 hys hmem
    exact hy0 (by rw [← hy]; exact hys y hmem)
  have hm1 : t - x ∉ S.erase t := hnot _ htt htx0 hts
  have hm2 : x ∉ insert (t - x) (S.erase t) := by
    rw [Finset.mem_insert, not_or]
    refine ⟨fun e => h0 ?_, hnot _ hx h0 hxs⟩
    rw [← hx]; nth_rewrite 2 [e]; exact hxtx
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact hx
    · exact htt
    · exact hI e (Finset.mem_of_mem_erase he)
  · intro e he z
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact hc z
    · rw [sub_mul, mul_sub, hC t ht z, hc z]
    · exact hC e (Finset.mem_of_mem_erase he) z
  · intro e he
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact h0
    · exact htx0
    · exact hN e (Finset.mem_of_mem_erase he)
  · intro e he f hf hef
    rw [Finset.mem_insert, Finset.mem_insert] at he hf
    rcases he with rfl | rfl | he <;> rcases hf with rfl | rfl | hf
    · exact absurd rfl hef
    · exact hxtx
    · exact hxs f hf
    · exact htxx
    · exact absurd rfl hef
    · exact hts f hf
    · exact hsx e he
    · exact hst' e he
    · exact hO e (Finset.mem_of_mem_erase he) f (Finset.mem_of_mem_erase hf) hef
  · rw [Finset.sum_insert hm2, Finset.sum_insert hm1, ← add_assoc, add_sub_cancel,
      Finset.add_sum_erase S (fun e => e) ht, hS]
  · rw [Finset.card_insert_of_notMem hm2, Finset.card_insert_of_notMem hm1,
      Finset.card_erase_of_mem ht]
    have := Finset.card_pos.2 ⟨t, ht⟩
    omega

theorem exists_prim [Module.Finite ℂ A] [Nontrivial A] : ∃ S : Finset A, IsDecomp S ∧ IsPrim S := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Finset A, IsDecomp S ∧ S.card = n
  have h1 : P 1 := ⟨{1}, ⟨by simp, by simp, by simp, by simp, by simp⟩, by simp⟩
  have hb : ∀ n, P n → n ≤ Module.finrank ℂ A := by
    rintro n ⟨S, hS, rfl⟩; exact card_le hS
  obtain ⟨S, hS, hc⟩ := Nat.findGreatest_spec (P := P) (m := 1) (n := Module.finrank ℂ A) (hb 1 h1) h1
  refine ⟨S, hS, ?_⟩
  intro t ht x hx hc' hxt
  by_contra hne
  rw [not_or] at hne
  obtain ⟨h2, h3⟩ := refine_decomp hS ht hx hc' hxt hne.1 hne.2
  have := Nat.le_findGreatest (P := P) (hb _ ⟨_, h2, rfl⟩) ⟨_, h2, rfl⟩
  omega

theorem lab_unique {ι : Type} {S : Finset A} (hS : IsDecomp S) (hP : IsPrim S) (e : ι → A)
    (he_idem : ∀ i, e i * e i = e i) (he_c : ∀ i z, e i * z = z * e i)
    (he_o : ∀ i j, i ≠ j → e i * e j = 0) (T : Finset ι) (hT : ∑ i ∈ T, e i = 1) {t : A} (ht : t ∈ S) :
    ∃ i ∈ T, e i * t = t ∧ ∀ j, j ≠ i → e j * t = 0 := by
  have key : ∀ j, e j * t = 0 ∨ e j * t = t := by
    intro j
    refine hP t ht _ ?_ ?_ ?_
    · rw [mul_assoc, ← mul_assoc t, hS.2.1 t ht (e j), mul_assoc, hS.1 t ht, ← mul_assoc, he_idem]
    · intro z
      rw [mul_assoc, hS.2.1 t ht z, ← mul_assoc, he_c j z, mul_assoc]
    · rw [mul_assoc, hS.1 t ht]
  have hsum : ∑ j ∈ T, e j * t = t := by rw [← Finset.sum_mul, hT, one_mul]
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ hS.2.2.1 t ht)
  have hit : e i * t = t := (key i).resolve_left hne
  refine ⟨i, hi, hit, fun j hji => (key j).resolve_right fun hjt => hS.2.2.1 t ht ?_⟩
  have h0 : (e j * t) * (e i * t) = 0 := by
    rw [mul_assoc, ← mul_assoc t, hS.2.1 t ht (e i), mul_assoc, ← mul_assoc (e j), he_o j i hji,
      zero_mul]
  rw [hjt, hit, hS.1 t ht] at h0
  exact h0

end Alg

section Lz

variable (g r : ℕ) [Fact g.Prime] (e : (ZMod g)[X] → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)))

abbrev GA (a : ℕ) : Type := MonoidAlgebra ℂ (GL (Fin a) (ZMod g))

def decS (a : ℕ) : Finset (GA g a) := (exists_prim (A := GA g a)).choose

theorem decS_spec (a : ℕ) : IsDecomp (decS g a) ∧ IsPrim (decS g a) :=
  (exists_prim (A := GA g a)).choose_spec

def LabQ (a : ℕ) (x : GA g a) (f : (ZMod g)[X]) : Prop :=
  (f.Monic ∧ f.natDegree = a ∧ f.coeff 0 ≠ 0) ∧
    ∀ h : a = r, e f * cast (congrArg (GA g) h) x = cast (congrArg (GA g) h) x

open Classical in

def labF (a : ℕ) (x : GA g a) : (ZMod g)[X] :=
  if h : ∃ f, LabQ g r e a x f then h.choose else (X - C 1) ^ a

theorem labF_spec (a : ℕ) (x : GA g a) :
    (labF g r e a x).Monic ∧ (labF g r e a x).natDegree = a ∧ (labF g r e a x).coeff 0 ≠ 0 := by
  unfold labF
  split_ifs with h
  · exact h.choose_spec.1
  · refine ⟨(monic_X_sub_C 1).pow a, ?_, ?_⟩
    · rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    · rw [coeff_zero_eq_eval_zero]; simp

def lzE : PairedCharacterCondition.LzData g where
  Irr a := ↥(decS g a)
  finIrr a := inferInstance
  idem τ := τ.1
  idem_idem τ := (decS_spec g _).1.1 _ τ.2
  idem_central τ z := (decS_spec g _).1.2.1 _ τ.2 z
  idem_ne τ := (decS_spec g _).1.2.2.1 _ τ.2
  idem_orth τ σ h := (decS_spec g _).1.2.2.2.1 _ τ.2 _ σ.2 (fun e => h (Subtype.ext e))
  idem_sum a := by
    rw [Finset.sum_coe_sort (decS g a) (fun x => x)]; exact (decS_spec g a).1.2.2.2.2
  idem_prim τ x hx hc hxt := (decS_spec g _).2 _ τ.2 x hx hc hxt
  lab τ := labF g r e _ τ.1
  lab_spec τ := labF_spec g r e _ τ.1
  Rep a := Set ↥(decS g a)
  ofIrr τ := {τ}
  cons R τ := τ ∈ R
  cons_ofIrr _ _ := Set.mem_singleton_iff
  hc _ _ := ∅

open Classical in
theorem lzE_ser (hidem : ∀ f, e f * e f = e f) (hcen : ∀ f a, e f * a = a * e f)
    (horth : ∀ f f', f ≠ f' → e f * e f' = 0)
    (hsum : ∃ S : Finset (ZMod g)[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0) ∧
      ∑ f ∈ S, e f = 1) (f : (ZMod g)[X]) :
    e f = ∑ τ : (lzE g r e).Irr r, if (lzE g r e).lab τ = f then (lzE g r e).idem τ else 0 := by
  obtain ⟨T, hTm, hT⟩ := hsum
  have hmain : ∀ t ∈ decS g r, ∀ f, e f * t = if labF g r e r t = f then t else 0 := by
    intro t ht f
    obtain ⟨i, hi, hit, hj⟩ :=
      lab_unique (decS_spec g r).1 (decS_spec g r).2 e hidem hcen horth T hT ht
    have hlab : labF g r e r t = i := by
      have hex : ∃ f, LabQ g r e r t f := ⟨i, (hTm i).1 hi, fun h => by simp only [cast_eq]; exact hit⟩
      have hs := hex.choose_spec.2 rfl
      simp only [cast_eq] at hs
      unfold labF
      rw [dif_pos hex]
      by_contra hne
      exact (decS_spec g r).1.2.2.1 t ht (hs.symm.trans (hj _ hne))
    rw [hlab]
    split_ifs with hif
    · subst hif; exact hit
    · exact hj f (Ne.symm hif)
  show e f = ∑ τ : ↥(decS g r), if labF g r e r τ.1 = f then τ.1 else 0
  calc e f = e f * ∑ τ : ↥(decS g r), τ.1 := by
        rw [Finset.sum_coe_sort (decS g r) (fun x => x), (decS_spec g r).1.2.2.2.2, mul_one]
    _ = ∑ τ : ↥(decS g r), e f * τ.1 := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun τ _ => hmain τ.1 τ.2 f

end Lz

theorem exists_lz_serEq : ∀ D : D7, ∃ lz : ∀ k : Fin 2, PairedCharacterCondition.LzData (D.host.g k), SerEq D lz := by
  intro D
  refine ⟨fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩;
    lzE (D.host.g k) D.R.r (D.ntypes.eSer k), ?_⟩
  intro k f
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  exact lzE_ser _ _ _ (D.ntypes.eSer_idem k) (D.ntypes.eSer_central k) (D.ntypes.eSer_orth k)
    (D.ntypes.eSer_sum k) f

end GlobalTheory.LzExist
