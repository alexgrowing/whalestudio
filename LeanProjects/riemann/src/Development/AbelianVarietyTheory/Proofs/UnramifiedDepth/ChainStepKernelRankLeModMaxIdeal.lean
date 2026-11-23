import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.ChainStep

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) :
    V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [V.v.map_mul]
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right (by simpa using hb))

theorem int_mul_mm {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM
  rw [V.v_l]
  exact zero_lt_one

def intRing (V : VF C) : Subring C where
  carrier := {a | V.Ge 0 a}
  mul_mem' ha hb := VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' ha hb := VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' ha := VF.Ge.neg ha

theorem add_pow_congr {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (n : ℕ) :
    V.MM ((a + b) ^ (V.l ^ n) - (a ^ (V.l ^ n) + b ^ (V.l ^ n))) := by
  have h : ∃ r : intRing V, ((⟨a, ha⟩ : intRing V) + ⟨b, hb⟩) ^ (V.l ^ n) =
      (⟨a, ha⟩ : intRing V) ^ (V.l ^ n) + (⟨b, hb⟩ : intRing V) ^ (V.l ^ n) + (V.l : intRing V) * r := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨a, ha⟩ : intRing V) ⟨b, hb⟩ n
    first
      | exact ⟨r, hr⟩
      | exact ⟨_, by rw [hr, mul_assoc, mul_assoc]⟩
  obtain ⟨r, hr⟩ := h
  have h2 := congrArg (fun z : intRing V => (z : C)) hr
  push_cast at h2
  rw [h2, add_sub_cancel_left]
  exact mm_mul_int mm_l r.2

theorem sum_pow_congr {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) (n : ℕ) :
    V.MM ((∑ i ∈ s, f i) ^ (V.l ^ n) - ∑ i ∈ s, f i ^ (V.l ^ n)) := by
  induction s using Finset.induction_on with
  | empty => simpa [V.l_prime.ne_zero] using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h' := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h1 := add_pow_congr (h a (Finset.mem_insert_self a s)) (VF.Ge.sum h') n
    have h2 := mm_add h1 (ih h')
    convert h2 using 1
    ring

theorem even_val_add {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (s : ℕ) :
    Even (a + ((2 * s : ℕ) : ZMod d)).val ↔ Even a.val := by
  have h2 : 2 ∣ d := hd.two_dvd
  rw [ZMod.val_add, ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2,
    Nat.add_mod, Nat.mod_mod_of_dvd _ h2]
  simp

theorem big_add {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (h : X.big g a) (s : ℕ) :
    X.big g (a + ((2 * s : ℕ) : ZMod d)) := by
  fin_cases g
  · exact (hA.2 _).2 ((even_val_add hA.1 a s).2 ((hA.2 _).1 h))
  · have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
    refine (h1 _).2 fun h2 => (h1 _).1 h ?_
    exact (hA.2 _).2 ((even_val_add hA.1 a s).1 ((hA.2 _).1 h2))

theorem mm_of_tan {d : ℕ} {I J : Type} [Fintype I] [Fintype J] {G : Cart V d I J} (S : Sys G)
    (z : I → C) (h : ∀ k, V.MM (∑ c, z c * S.tan c k)) (c : I) : V.MM (z c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have h2 : z c = ∑ k, (∑ b, z b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, z b * S.tan b k * S.U⁻¹ k c = z b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp [Sys.U, mul_assoc]
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [h2]
  exact mm_sum fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)

theorem rank_le : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → ∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν e, D.lev e = s + 1 → V.MM (∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2))) → N ≤ X.j' := by
  intro C _ V d _ I J _ _ X hA g a hbig i S Z D hD s hs m y hy hyi N x hx hxi hker
  set F : Finset (I g) := Finset.univ.filter (fun c => D.lev c = s) with hF
  have hFm : ∀ c, c ∈ F ↔ D.lev c = s := fun c => by simp [hF]
  have hDi : D.i = i := hD.2.2.1
  have hDl : D.l = V.l := hD.2.1
  have hDv : D.v = V.v := hD.1
  have hgood : ∀ c ∈ F, D.good c := fun c hc =>
    D.pure_good c (by rw [(hFm c).1 hc, hDi]; omega)
  let w : Fin N → I g → C := fun ν c => ∑ δ, x ν δ * y δ c
  have hw : ∀ ν c, V.Ge 0 (w ν c) := fun ν c => VF.Ge.sum fun δ _ => (hx ν δ).mul_int (hy δ c)
  have hG : ∀ c ∈ F, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 := hD.good (hgood c hc)
    rwa [hD.2.2.2.2 c (by rw [(hFm c).1 hc]; omega), (hFm c).1 hc] at h1
  have hal : ∀ c ∈ F, ∀ e, V.Ge 0 ((V.l : C) * D.al c 2 e) := fun c hc e =>
    hDl ▸ hD.l_mul_al_two_int (hgood c hc) e
  have key := X.R1 hA g _ (big_add X hA g a hbig s) N
    (fun ν => ∑ c ∈ F, w ν c • S.tan c) (fun ν => ∑ c ∈ F, teich V.l (w ν c) (S.cur c))
    (fun ν => Cart.Good.comb F (fun c _ => hw ν c) hG) ?_ ?_
  · omega
  · intro ν k
    rw [Cart.scaledSecond_sum]
    have e1 : ∑ c ∈ F, w ν c ^ (V.l ^ 2) * (X.G g).V2 (S.cur c) k =
        ∑ e, (∑ c ∈ F, w ν c ^ (V.l ^ 2) * ((V.l : C) * D.al c 2 e)) * S.tan e k := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 := hD.2.2.2.1 c 2 k (by norm_num)
      simp only [Sys.al, Sys.cur_zero_inl] at h1
      simp only [Cart.V2, h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [e1]
    refine mm_sum fun e _ => mm_mul_int ?_ (tan_int S e k)
    by_cases he : D.lev e = s + 1
    · have h1 := hker ν e he
      have h2 : V.MM (∑ c ∈ F, (w ν c ^ (V.l ^ 2) - ∑ δ, (x ν δ * y δ c) ^ (V.l ^ 2)) *
          ((V.l : C) * D.al c 2 e)) :=
        mm_sum fun c hc => mm_mul_int
          (sum_pow_congr (fun δ _ => (hx ν δ).mul_int (hy δ c)) 2) (hal c hc e)
      have e2 : ∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ F, (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2) =
          ∑ c ∈ F, (∑ δ, (x ν δ * y δ c) ^ (V.l ^ 2)) * ((V.l : C) * D.al c 2 e) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun δ _ => by
          rw [mul_pow]; ring
      convert mm_add h1 h2 using 1
      rw [e2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    · refine mm_sum fun c hc => int_mul_mm ((hw ν c).pow _) ?_
      have hc' := (hFm c).1 hc
      rw [D.al_two c (by rw [hc', hDi]; omega) e,
        D.g_supp c (by rw [hc', hDi]; omega) e (by rw [hc']; exact he), hDl, zero_add,
        mul_inv_cancel_left₀ VF.l_ne_zero]
      refine mm_mul_int mm_l ?_
      have := D.lam_int c e
      rw [hDv] at this
      simpa [VF.Ge] using this
  · intro co hco hmm
    refine hxi co hco (hyi (fun δ => ∑ ν, co ν * x ν δ)
      (fun δ => VF.Ge.sum fun ν _ => (hco ν).mul_int (hx ν δ)) ?_)
    refine mm_of_tan S _ fun k => ?_
    convert hmm k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hF, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : D.lev c = s
    · simp only [hc, if_true, w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun δ _ => by ring
    · simp [hc]

end GlobalTheory.ChainStep
