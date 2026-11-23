import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionOfDecompGlob

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions NumberField

section Gen

variable (O : Subring ℂ)

def bwE_Int {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) : Prop := ∀ a b, M a b ∈ O

def bwE_Loc : Prop :=
  ∀ (r : ℕ) (s : Finset (Fin r)) (c m : Fin r → ℂ), (∀ i, c i ∈ O) → (∀ i, m i ∈ O) → ∑ i ∈ s, c i * m i = 1 →
    ∃ i ∈ s, ∃ y ∈ O, m i * y = 1

variable {O} {r : ℕ}

theorem bwE_Int_one : bwE_Int O (1 : Matrix (Fin r) (Fin r) ℂ) := fun a b => by
  rw [Matrix.one_apply]; split_ifs
  · exact O.one_mem
  · exact O.zero_mem

theorem bwE_Int_add {A B : Matrix (Fin r) (Fin r) ℂ} (hA : bwE_Int O A) (hB : bwE_Int O B) : bwE_Int O (A + B) :=
  fun a b => O.add_mem (hA a b) (hB a b)

theorem bwE_Int_sub {A B : Matrix (Fin r) (Fin r) ℂ} (hA : bwE_Int O A) (hB : bwE_Int O B) : bwE_Int O (A - B) :=
  fun a b => O.sub_mem (hA a b) (hB a b)

theorem bwE_Int_mul {A B : Matrix (Fin r) (Fin r) ℂ} (hA : bwE_Int O A) (hB : bwE_Int O B) : bwE_Int O (A * B) :=
  fun a b => by
    rw [Matrix.mul_apply]; exact O.sum_mem (fun k _ => O.mul_mem (hA a k) (hB k b))

theorem bwE_Int_single (p q : Fin r) {x : ℂ} (hx : x ∈ O) : bwE_Int O (Matrix.single p q x) := fun a b => by
  rw [Matrix.single_apply]; split_ifs
  · exact hx
  · exact O.zero_mem

theorem bwE_Int_sum {ι : Type} (s : Finset ι) (X : ι → Matrix (Fin r) (Fin r) ℂ) (h : ∀ i ∈ s, bwE_Int O (X i)) :
    bwE_Int O (∑ i ∈ s, X i) := fun a b => by
  rw [Matrix.sum_apply]; exact O.sum_mem (fun i hi => h i hi a b)

theorem bwE_det_mem {M : Matrix (Fin r) (Fin r) ℂ} (h : bwE_Int O M) : M.det ∈ O := by
  have e : M = (Matrix.of fun a b => (⟨M a b, h a b⟩ : O)).map O.subtype := by ext a b; rfl
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Subtype.property _

theorem bwE_gen_mem (p q : Fin r) {x : ℂ} (hx : x ∈ O) : (1 + Matrix.single p q x) ∈ bwA_EO O r :=
  Submonoid.subset_closure ⟨q, p, x, hx, rfl⟩

theorem bwE_prod_eq {ι : Type} [DecidableEq ι] (s : Finset ι) (X : ι → Matrix (Fin r) (Fin r) ℂ) (a : ι) (ha : a ∉ s)
    (h0 : ∀ i ∈ insert a s, ∀ i' ∈ insert a s, X i * X i' = 0) :
    1 + ∑ i ∈ insert a s, X i = (1 + X a) * (1 + ∑ i ∈ s, X i) := by
  rw [Finset.sum_insert ha, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, Finset.mul_sum,
    Finset.sum_eq_zero (fun i hi => h0 a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)), add_zero]
  abel

theorem bwE_sum_mem {ι : Type} [DecidableEq ι] (s : Finset ι) (X : ι → Matrix (Fin r) (Fin r) ℂ)
    (h1 : ∀ i ∈ s, 1 + X i ∈ bwA_EO O r) (h0 : ∀ i ∈ s, ∀ i' ∈ s, X i * X i' = 0) :
    1 + ∑ i ∈ s, X i ∈ bwA_EO O r := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, add_zero]; exact (bwA_EO O r).one_mem
  | @insert a s ha ih =>
    rw [bwE_prod_eq s X a ha h0]
    exact (bwA_EO O r).mul_mem (h1 a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
        (fun i hi i' hi' => h0 i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi')))

theorem bwE_single_mul_apply (p q : Fin r) (x : ℂ) (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (Matrix.single p q x * M) a b = if a = p then x * M q b else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : a = p
  · subst h; simp [Matrix.single_apply]
  · simp [Ne.symm h, h]

theorem bwE_elim (hL : bwE_Loc O) (M : Matrix (Fin r) (Fin r) ℂ) (hM : bwE_Int O M)
    (hinv : ∃ M', bwE_Int O M' ∧ M' * M = 1) : M ∈ bwA_EO O r := by
  suffices H : ∀ d k, k + d = r → ∀ M : Matrix (Fin r) (Fin r) ℂ, bwE_Int O M →
      (∃ M', bwE_Int O M' ∧ M' * M = 1) →
      (∀ c : Fin r, c.val < k → ∀ a, M a c = if a = c then 1 else 0) → M ∈ bwA_EO O r from
    H r 0 (by omega) M hM hinv (fun c hc => absurd hc (Nat.not_lt_zero _))
  intro d
  induction d with
  | zero =>
    intro k hk M _ _ hc
    have e : M = 1 := by
      ext a c; rw [hc c (by omega) a, Matrix.one_apply]
    rw [e]; exact (bwA_EO O r).one_mem
  | succ d ih =>
    intro k hk M hM hinv hc
    obtain ⟨M', hM', hM'M⟩ := hinv
    have hkr : k < r := by omega
    set kk : Fin r := ⟨k, hkr⟩ with hkk
    have hne : ∀ c : Fin r, c.val < k → kk ≠ c := fun c hcl h => by
      rw [← h] at hcl; exact lt_irrefl _ hcl
    have hrow : ∀ c : Fin r, c.val < k → M' kk c = 0 := by
      intro c hcl
      have h1 := congrFun (congrFun hM'M kk) c
      rw [Matrix.mul_apply, Matrix.one_apply, if_neg (hne c hcl)] at h1
      rw [← h1, Finset.sum_eq_single c]
      · rw [hc c hcl c, if_pos rfl, mul_one]
      · intro b _ hb; rw [hc c hcl b, if_neg hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ c) h
    have hsum : ∑ i ∈ Finset.univ.filter (fun i : Fin r => k ≤ i.val), M' kk i * M i kk = 1 := by
      have h1 := congrFun (congrFun hM'M kk) kk
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
      rw [Finset.sum_filter, ← h1]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs with h
      · rfl
      · rw [hrow i (by omega), zero_mul]
    obtain ⟨i₀, hi₀s, y, hyO, hy⟩ := hL r _ (fun i => M' kk i) (fun i => M i kk) (fun i => hM' kk i)
      (fun i => hM i kk) hsum
    have hi₀ : k ≤ i₀.val := (Finset.mem_filter.1 hi₀s).2
    have hMkc : ∀ c : Fin r, c.val < k → M kk c = 0 := fun c hcl => by rw [hc c hcl kk, if_neg (hne c hcl)]
    have hMi₀c : ∀ c : Fin r, c.val < k → M i₀ c = 0 := fun c hcl => by
      rw [hc c hcl i₀, if_neg]; intro h; rw [h] at hi₀; omega
    obtain ⟨G, G', hGI, hG', hG'I, hG'G, hA1, hAc⟩ : ∃ G G' : Matrix (Fin r) (Fin r) ℂ, bwE_Int O G ∧
        G' ∈ bwA_EO O r ∧ bwE_Int O G' ∧ G' * G = 1 ∧ (G * M) kk kk = 1 ∧
        ∀ c : Fin r, c.val < k → ∀ a, (G * M) a c = M a c := by
      by_cases h : i₀ = kk
      · rw [h] at hy
        refine ⟨1 + Matrix.single kk kk (y - 1), 1 + Matrix.single kk kk (M kk kk - 1),
          bwE_Int_add bwE_Int_one (bwE_Int_single _ _ (O.sub_mem hyO O.one_mem)),
          bwE_gen_mem _ _ (O.sub_mem (hM kk kk) O.one_mem),
          bwE_Int_add bwE_Int_one (bwE_Int_single _ _ (O.sub_mem (hM kk kk) O.one_mem)), ?_, ?_, ?_⟩
        · rw [add_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_same, add_assoc,
            ← Matrix.single_add, ← Matrix.single_add]
          have e : y - 1 + (M kk kk - 1 + (M kk kk - 1) * (y - 1)) = 0 := by linear_combination hy
          rw [e, Matrix.single_zero, add_zero]
        · rw [add_mul, one_mul, Matrix.add_apply, bwE_single_mul_apply, if_pos rfl]
          linear_combination hy
        · intro c hcl a
          rw [add_mul, one_mul, Matrix.add_apply, bwE_single_mul_apply, hMkc c hcl, mul_zero]
          split_ifs <;> simp
      · refine ⟨1 + Matrix.single kk i₀ ((1 - M kk kk) * y), 1 + Matrix.single kk i₀ (-((1 - M kk kk) * y)),
          bwE_Int_add bwE_Int_one (bwE_Int_single _ _ (O.mul_mem (O.sub_mem O.one_mem (hM kk kk)) hyO)),
          bwE_gen_mem _ _ (O.neg_mem (O.mul_mem (O.sub_mem O.one_mem (hM kk kk)) hyO)),
          bwE_Int_add bwE_Int_one (bwE_Int_single _ _ (O.neg_mem (O.mul_mem (O.sub_mem O.one_mem (hM kk kk)) hyO))),
          ?_, ?_, ?_⟩
        · rw [add_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne _ _ _ _ h, add_zero, add_assoc,
            ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero]
        · rw [add_mul, one_mul, Matrix.add_apply, bwE_single_mul_apply, if_pos rfl]
          linear_combination (1 - M kk kk) * hy
        · intro c hcl a
          rw [add_mul, one_mul, Matrix.add_apply, bwE_single_mul_apply, hMi₀c c hcl, mul_zero]
          split_ifs <;> simp
    set A := G * M with hAdef
    have hAI : bwE_Int O A := bwE_Int_mul hGI hM
    set X : Matrix (Fin r) (Fin r) ℂ := ∑ i ∈ Finset.univ.erase kk, Matrix.single i kk (A i kk) with hX
    have hXX0 : ∀ i ∈ Finset.univ.erase kk, ∀ i' ∈ Finset.univ.erase kk,
        Matrix.single i kk (A i kk) * Matrix.single i' kk (A i' kk) = 0 := fun i _ i' hi' =>
      Matrix.single_mul_single_of_ne _ _ _ _ (Finset.ne_of_mem_erase hi').symm _
    have hXX : X * X = 0 := by
      rw [hX, Finset.sum_mul_sum]
      exact Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun i' hi' => hXX0 i hi i' hi'))
    have hXI : bwE_Int O X := bwE_Int_sum _ _ (fun i _ => bwE_Int_single _ _ (hAI i kk))
    have hXE : 1 + X ∈ bwA_EO O r := bwE_sum_mem _ _ (fun i _ => bwE_gen_mem _ _ (hAI i kk)) hXX0
    have hXmul : ∀ a b, (X * A) a b = if a ∈ Finset.univ.erase kk then A a kk * A kk b else 0 := by
      intro a b
      rw [hX, Finset.sum_mul, Matrix.sum_apply]
      simp_rw [bwE_single_mul_apply]
      rw [Finset.sum_ite_eq]
    have h1X : (1 + X) * (1 - X) = 1 := by
      rw [mul_sub, mul_one, add_mul, one_mul, hXX]; abel
    set C := (1 - X) * A with hCdef
    have hCe : ∀ a b, C a b = A a b - if a ∈ Finset.univ.erase kk then A a kk * A kk b else 0 := by
      intro a b; rw [hCdef, sub_mul, one_mul, Matrix.sub_apply, hXmul]
    have hCI : bwE_Int O C := bwE_Int_mul (bwE_Int_sub bwE_Int_one hXI) hAI
    have hCinv : ∃ M'', bwE_Int O M'' ∧ M'' * C = 1 := by
      refine ⟨M' * G' * (1 + X), bwE_Int_mul (bwE_Int_mul hM' hG'I) (bwE_Int_add bwE_Int_one hXI), ?_⟩
      calc M' * G' * (1 + X) * C = M' * (G' * (((1 + X) * (1 - X)) * (G * M))) := by
            rw [hCdef, hAdef]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1X, Matrix.one_mul, ← Matrix.mul_assoc G', hG'G, Matrix.one_mul, hM'M]
    have hAkc : ∀ c : Fin r, c.val < k → A kk c = 0 := fun c hcl => by rw [hAc c hcl, hMkc c hcl]
    have hCc : ∀ c : Fin r, c.val < k + 1 → ∀ a, C a c = if a = c then 1 else 0 := by
      intro c hcl a
      rw [hCe]
      by_cases hck : c.val < k
      · rw [hAkc c hck, mul_zero, ite_self, sub_zero, hAc c hck, hc c hck]
      · have e : c = kk := Fin.ext (by rw [hkk]; simp only; omega)
        subst e
        by_cases ha : a = kk
        · subst ha; simp [hA1]
        · have : a ∈ Finset.univ.erase kk := Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩
          rw [if_pos this, hA1, mul_one, sub_self, if_neg ha]
    have hCE := ih (k + 1) (by omega) C hCI hCinv hCc
    have eM : M = G' * ((1 + X) * C) := by
      rw [hCdef, ← Matrix.mul_assoc (1 + X), h1X, Matrix.one_mul, hAdef, ← Matrix.mul_assoc, hG'G, Matrix.one_mul]
    rw [eM]
    exact (bwA_EO O r).mul_mem hG' ((bwA_EO O r).mul_mem hXE hCE)

end Gen

section Spec

open Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms
open scoped Matrix

variable (D : D7) (u : D.what₂.Word)

theorem bwE_loc_Ow (w : D.what₂.places.Pl) : bwE_Loc (bwA_Ow D w) := by
  intro r s c m hc hm hsum
  by_contra hno
  push Not at hno
  choose γ hγ hγe using fun i => Subring.mem_map.1 (hc i)
  choose μ hμ hμe using fun i => Subring.mem_map.1 (hm i)
  have hpos : ∀ i ∈ s, (0 : WithTop ℤ) < D.what₂.places.val w (γ i * μ i) := by
    intro i hi
    have h0 : (0 : WithTop ℤ) ≤ D.what₂.places.val w (μ i) := hμ i
    have hne : D.what₂.places.val w (μ i) ≠ 0 := by
      intro h
      have hμ0 : μ i ≠ 0 := by
        intro h'; rw [h', AddValuation.map_zero] at h; simp at h
      refine hno i hi (D.what₂.embLL (μ i)⁻¹) (Subring.mem_map.2 ⟨(μ i)⁻¹, ?_, rfl⟩) ?_
      · show (0 : WithTop ℤ) ≤ D.what₂.places.val w (μ i)⁻¹
        rw [AddValuation.map_inv, h, neg_zero]
      · rw [← hμe i, ← map_mul, mul_inv_cancel₀ hμ0, map_one]
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le (lt_of_le_of_ne h0 (Ne.symm hne)) (le_add_of_nonneg_left (hγ i))
  have h1 : ∑ i ∈ s, γ i * μ i = 1 := by
    apply D.what₂.embLL.injective
    rw [map_sum, map_one, ← hsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, hγe, hμe])
  have h2 : (0 : WithTop ℤ) < D.what₂.places.val w (∑ i ∈ s, γ i * μ i) :=
    AddValuation.map_lt_sum _ (by simp) hpos
  rw [h1, AddValuation.map_one] at h2
  exact lt_irrefl _ h2

theorem bwE_mem_Ow (w : D.what₂.places.Pl) (hw : OverT D u w) (τ : D.what₂.Tau) (y : D.host.E) (s : ℕ)
    (hs : ¬ (D.mem u).A.T ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    embT D τ y ∈ bwA_Ow D w := by
  rw [bwA_embT_eq]
  exact Subring.mem_map.2 ⟨_, bwA_val_locInt D w ((D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) y s
    (by rw [hw]; exact hs) hy, rfl⟩

theorem bwE_mulVec_col {n : ℕ} (A B : Matrix (Fin n) (Fin n) D.host.E) (a k : Fin n) :
    (A *ᵥ fun r => B r k) a = (A * B) a k := rfl

theorem bwE_locBasis_int (w : D.what₂.places.Pl) (hw : OverT D u w) (τ : D.what₂.Tau) {n : ℕ}
    {L : Set (Fin n → D.host.E)} {B : GL (Fin n) D.host.E} (hB : IsLocBasis (D.mem u).A.T L B)
    (x : Fin n → D.host.E) (s : ℕ) (hs : ¬ (D.mem u).A.T ∣ s) (hx : (s : D.host.E) • x ∈ L) (a : Fin n) :
    embT D τ ((((B⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x) a) ∈ bwA_Ow D w := by
  obtain ⟨s', hs', h⟩ := (hB x).1 ⟨s, hs, hx⟩
  exact bwE_mem_Ow D u w hw τ _ s' hs' (h a)

theorem bwE_col_loc (w : D.what₂.places.Pl) (hw : OverT D u w) {n : ℕ} {L : Set (Fin n → D.host.E)}
    {B : GL (Fin n) D.host.E} (hB : IsLocBasis (D.mem u).A.T L B) (k : Fin n) :
    ∃ s : ℕ, ¬ (D.mem u).A.T ∣ s ∧ (s : D.host.E) • (fun r => (B : Matrix (Fin n) (Fin n) D.host.E) r k) ∈ L := by
  refine (hB _).2 ⟨1, ?_, fun a => ?_⟩
  · rw [← hw]; exact (D.what₂.places.resChar_prime w).not_dvd_one
  · rw [Nat.cast_one, one_mul, bwE_mulVec_col, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩

end Spec

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
