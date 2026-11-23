import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionOfDecompGlob

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions NumberField

section Gen

variable (O : Subring ℂ)

def bwD_Int {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) : Prop := ∀ a b, M a b ∈ O

def bwD_Loc : Prop :=
  ∀ (r : ℕ) (s : Finset (Fin r)) (c m : Fin r → ℂ), (∀ i, c i ∈ O) → (∀ i, m i ∈ O) → ∑ i ∈ s, c i * m i = 1 →
    ∃ i ∈ s, ∃ y ∈ O, m i * y = 1

variable {O} {r : ℕ}

theorem bwD_Int_one : bwD_Int O (1 : Matrix (Fin r) (Fin r) ℂ) := by
  intro a b
  by_cases h : a = b
  · subst h; simp only [Matrix.one_apply_eq]; exact O.one_mem
  · rw [Matrix.one_apply_ne h]; exact O.zero_mem

theorem bwD_Int_add {A B : Matrix (Fin r) (Fin r) ℂ} (hA : bwD_Int O A) (hB : bwD_Int O B) : bwD_Int O (A + B) := fun a b => by
  rw [Matrix.add_apply]; exact O.add_mem (hA a b) (hB a b)

theorem bwD_Int_sub {A B : Matrix (Fin r) (Fin r) ℂ} (hA : bwD_Int O A) (hB : bwD_Int O B) : bwD_Int O (A - B) := fun a b => by
  rw [Matrix.sub_apply]; exact O.sub_mem (hA a b) (hB a b)

theorem bwD_Int_mul {A B : Matrix (Fin r) (Fin r) ℂ} (hA : bwD_Int O A) (hB : bwD_Int O B) : bwD_Int O (A * B) := fun a b => by
  rw [Matrix.mul_apply]; exact O.sum_mem fun k _ => O.mul_mem (hA a k) (hB k b)

theorem bwD_Int_single (p q : Fin r) {x : ℂ} (hx : x ∈ O) : bwD_Int O (Matrix.single p q x) := fun a b => by
  rw [Matrix.single_apply]; split_ifs
  · exact hx
  · exact O.zero_mem

theorem bwD_Int_sum {ι : Type} (s : Finset ι) (X : ι → Matrix (Fin r) (Fin r) ℂ) (h : ∀ i ∈ s, bwD_Int O (X i)) :
    bwD_Int O (∑ i ∈ s, X i) := fun a b => by
  rw [Matrix.sum_apply]; exact O.sum_mem fun i hi => h i hi a b

theorem bwD_det_mem {M : Matrix (Fin r) (Fin r) ℂ} (h : bwD_Int O M) : M.det ∈ O := by
  have hM : M = O.subtype.mapMatrix (Matrix.of fun a b => (⟨M a b, h a b⟩ : O)) := by
    ext a b; rfl
  rw [hM, ← RingHom.map_det]
  exact Subtype.mem _

theorem bwD_Int_adj {M : Matrix (Fin r) (Fin r) ℂ} (h : bwD_Int O M) : bwD_Int O M.adjugate := by
  have hM : M = O.subtype.mapMatrix (Matrix.of fun a b => (⟨M a b, h a b⟩ : O)) := by
    ext a b; rfl
  intro a b
  rw [hM, ← RingHom.map_adjugate]
  exact Subtype.mem _

theorem bwD_gen_mem (p q : Fin r) {x : ℂ} (hx : x ∈ O) : (1 + Matrix.single p q x) ∈ bwA_EO O r := by
  unfold bwA_EO
  exact Submonoid.subset_closure ⟨q, p, x, hx, rfl⟩

theorem bwD_prod_eq {ι : Type} [DecidableEq ι] (s : Finset ι) (X : ι → Matrix (Fin r) (Fin r) ℂ) (a : ι) (ha : a ∉ s)
    (h0 : ∀ i ∈ insert a s, ∀ i' ∈ insert a s, X i * X i' = 0) :
    1 + ∑ i ∈ insert a s, X i = (1 + X a) * (1 + ∑ i ∈ s, X i) := by
  have hz : ∑ i ∈ s, X a * X i = 0 :=
    Finset.sum_eq_zero fun i hi => h0 a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
  rw [Finset.sum_insert ha, add_mul, one_mul, mul_add, mul_one, Finset.mul_sum, hz, add_zero]
  abel

theorem bwD_sum_mem {ι : Type} [DecidableEq ι] (s : Finset ι) (X : ι → Matrix (Fin r) (Fin r) ℂ)
    (h1 : ∀ i ∈ s, 1 + X i ∈ bwA_EO O r) (h0 : ∀ i ∈ s, ∀ i' ∈ s, X i * X i' = 0) :
    1 + ∑ i ∈ s, X i ∈ bwA_EO O r := by
  revert h1 h0
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    rw [Finset.sum_empty, add_zero]
    exact one_mem _
  · intro a s ha ih h1 h0
    rw [bwD_prod_eq s X a ha h0]
    exact mul_mem (h1 a (Finset.mem_insert_self a s))
      (ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
        (fun i hi i' hi' => h0 i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi')))

theorem bwD_sum_det {ι : Type} [DecidableEq ι] (s : Finset ι) (X : ι → Matrix (Fin r) (Fin r) ℂ)
    (h1 : ∀ i ∈ s, (1 + X i).det = 1) (h0 : ∀ i ∈ s, ∀ i' ∈ s, X i * X i' = 0) :
    (1 + ∑ i ∈ s, X i).det = 1 := by
  revert h1 h0
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    rw [Finset.sum_empty, add_zero, Matrix.det_one]
  · intro a s ha ih h1 h0
    rw [bwD_prod_eq s X a ha h0, Matrix.det_mul, h1 a (Finset.mem_insert_self a s),
      ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
        (fun i hi i' hi' => h0 i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi')), one_mul]

theorem bwD_single_mul_apply (p q : Fin r) (x : ℂ) (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (Matrix.single p q x * M) a b = if a = p then x * M q b else 0 := by
  by_cases h : a = p
  · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
  · simp [Matrix.mul_apply, Matrix.single_apply, h, Ne.symm h]

theorem bwD_mul_single_apply (p q : Fin r) (x : ℂ) (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (M * Matrix.single p q x) a b = if b = q then M a p * x else 0 := by
  by_cases h : b = q
  · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
  · simp [Matrix.mul_apply, Matrix.single_apply, h, Ne.symm h]

private lemma one_add_single_mul_one_add_single_eq_one {r : ℕ} (p q : Fin r) (c d : ℂ)
    (h : d + c + (if q = p then d * c else 0) = 0) :
    (1 + Matrix.single p q d) * (1 + Matrix.single p q c) = 1 := by
  have hdc : Matrix.single p q d * Matrix.single p q c =
      Matrix.single p q (if q = p then d * c else 0) := by
    ext x z
    rw [bwD_single_mul_apply]
    by_cases hx : x = p
    · by_cases hz : z = q
      · by_cases hqp : q = p
        · simp [Matrix.single_apply, hx, hz, hqp]
        · simp [Matrix.single_apply, hx, hz, hqp, Ne.symm hqp]
      · simp [Matrix.single_apply, hx, hz, Ne.symm hz]
    · simp [Matrix.single_apply, hx, Ne.symm hx]
  rw [add_mul, one_mul, mul_add, mul_one, hdc]
  generalize (if q = p then d * c else 0) = e at h ⊢
  ext x z
  simp only [Matrix.add_apply, Matrix.single_apply]
  split_ifs
  · linear_combination h
  · simp

theorem bwD_elim (hL : bwD_Loc O) (M : Matrix (Fin r) (Fin r) ℂ) (hM : bwD_Int O M)
    (hinv : ∃ M', bwD_Int O M' ∧ M' * M = 1) : M ∈ bwA_EO O r := by
  suffices key : ∀ n k, k + n = r → ∀ M : Matrix (Fin r) (Fin r) ℂ, bwD_Int O M →
      (∃ M', bwD_Int O M' ∧ M' * M = 1) →
      (∀ b c : Fin r, c.val < k → M b c = if b = c then 1 else 0) → M ∈ bwA_EO O r by
    exact key r 0 (zero_add r) M hM hinv (fun b c hc => absurd hc (Nat.not_lt_zero _))
  intro n
  induction n with
  | zero =>
    intro k hk M _ _ hstd
    have h1 : M = 1 := by
      ext b c
      rw [Matrix.one_apply]
      exact hstd b c (by have := c.isLt; omega)
    rw [h1]
    exact one_mem _
  | succ n ih =>
    intro k hk M hMI hinvM hstd
    obtain ⟨M', hM'I, hM'M⟩ := hinvM
    obtain ⟨j, hjk⟩ : ∃ j : Fin r, j.val = k := ⟨⟨k, by omega⟩, rfl⟩

    have hM'j : ∀ c : Fin r, c.val < k → M' j c = 0 := by
      intro c hc
      have h1 := congrFun (congrFun hM'M j) c
      have hcol : ∀ x, M x c = if x = c then 1 else 0 := fun x => hstd x c hc
      simp only [Matrix.mul_apply, hcol, mul_ite, mul_one, mul_zero] at h1
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h1
      rw [h1, Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega))]
    have hsum : ∑ a ∈ Finset.univ.filter (fun a : Fin r => k ≤ a.val), M' j a * M a j = 1 := by
      have h1 := congrFun (congrFun hM'M j) j
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
      rw [Finset.sum_filter]
      refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h1
      split_ifs with ha
      · rfl
      · rw [hM'j a (by omega), zero_mul]
    obtain ⟨a, ha, y, hyO, hay⟩ := hL r _ (fun a => M' j a) (fun a => M a j)
      (fun a => hM'I j a) (fun a => hMI a j) hsum
    have hay' : M a j * y = 1 := hay
    have hka : k ≤ a.val := (Finset.mem_filter.mp ha).2

    obtain ⟨c₁, hc₁⟩ : ∃ c : ℂ, c = (1 - M j j) * y := ⟨_, rfl⟩
    have hc₁O : c₁ ∈ O := by rw [hc₁]; exact O.mul_mem (O.sub_mem O.one_mem (hMI j j)) hyO
    obtain ⟨d₁, hd₁⟩ : ∃ d : ℂ, d = if a = j then M j j - 1 else -c₁ := ⟨_, rfl⟩
    have hd₁O : d₁ ∈ O := by
      rw [hd₁]; split_ifs
      · exact O.sub_mem (hMI j j) O.one_mem
      · exact O.neg_mem hc₁O
    have hG₁ : (1 + Matrix.single j a d₁) * (1 + Matrix.single j a c₁) = 1 := by
      apply one_add_single_mul_one_add_single_eq_one
      rw [hd₁]
      split_ifs with haj
      · rw [haj] at hay'
        rw [hc₁]
        linear_combination (1 - M j j) * hay'
      · ring
    have hR₁I : bwD_Int O (1 + Matrix.single j a c₁) := bwD_Int_add bwD_Int_one (bwD_Int_single j a hc₁O)
    have hG₁I : bwD_Int O (1 + Matrix.single j a d₁) := bwD_Int_add bwD_Int_one (bwD_Int_single j a hd₁O)
    have hG₁E : 1 + Matrix.single j a d₁ ∈ bwA_EO O r := bwD_gen_mem j a hd₁O
    obtain ⟨M₁, hM₁⟩ : ∃ M₁ : Matrix (Fin r) (Fin r) ℂ, M₁ = (1 + Matrix.single j a c₁) * M := ⟨_, rfl⟩
    have hM₁e : ∀ x z, M₁ x z = M x z + if x = j then c₁ * M a z else 0 := by
      intro x z
      rw [hM₁, add_mul, one_mul, Matrix.add_apply, bwD_single_mul_apply]
    have hM₁I : bwD_Int O M₁ := by rw [hM₁]; exact bwD_Int_mul hR₁I hMI
    have hM₁jj : M₁ j j = 1 := by
      rw [hM₁e, if_pos rfl, hc₁]
      linear_combination (1 - M j j) * hay'
    have hMa : ∀ c : Fin r, c.val < k → M a c = 0 := by
      intro c hc
      rw [hstd a c hc, if_neg (Fin.ne_of_val_ne (by omega))]
    have hM₁c : ∀ x (c : Fin r), c.val < k → M₁ x c = if x = c then 1 else 0 := by
      intro x c hc
      rw [hM₁e, hMa c hc, mul_zero, ite_self, add_zero, hstd x c hc]

    obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin r) (Fin r) ℂ,
        S = ∑ b ∈ Finset.univ.erase j, Matrix.single b j (M₁ b j) := ⟨_, rfl⟩
    have hX0 : ∀ b ∈ Finset.univ.erase j, ∀ b' ∈ Finset.univ.erase j,
        Matrix.single b j (M₁ b j) * Matrix.single b' j (M₁ b' j) = 0 := by
      intro b _ b' hb'
      have hb'j : b' ≠ j := Finset.ne_of_mem_erase hb'
      ext x z
      rw [bwD_single_mul_apply, Matrix.zero_apply]
      simp [Matrix.single_apply, hb'j]
    have hSS : S * S = 0 := by
      rw [hS, Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun b' hb' => hX0 b hb b' hb'
    have hG₂E : 1 + S ∈ bwA_EO O r := by
      rw [hS]
      exact bwD_sum_mem _ (fun b => Matrix.single b j (M₁ b j)) (fun b _ => bwD_gen_mem b j (hM₁I b j)) hX0
    have hSI : bwD_Int O S := by
      rw [hS]; exact bwD_Int_sum _ _ fun b _ => bwD_Int_single b j (hM₁I b j)
    have hG₂ : (1 + S) * (1 - S) = 1 := by
      rw [add_mul, one_mul, mul_sub, mul_one, hSS, sub_zero, sub_add_cancel]
    obtain ⟨M₂, hM₂⟩ : ∃ M₂ : Matrix (Fin r) (Fin r) ℂ, M₂ = (1 - S) * M₁ := ⟨_, rfl⟩
    have hM₂e : ∀ x z, M₂ x z = M₁ x z - if x ∈ Finset.univ.erase j then M₁ x j * M₁ j z else 0 := by
      intro x z
      rw [hM₂, sub_mul, one_mul, Matrix.sub_apply, hS, Finset.sum_mul, Matrix.sum_apply]
      simp only [bwD_single_mul_apply]
      rw [Finset.sum_ite_eq]
    have hM₂I : bwD_Int O M₂ := by
      rw [hM₂]; exact bwD_Int_mul (bwD_Int_sub bwD_Int_one hSI) hM₁I
    have hstd₂ : ∀ x c : Fin r, c.val < k + 1 → M₂ x c = if x = c then 1 else 0 := by
      intro x c hc
      rw [hM₂e]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | hc
      · rw [hM₁c j c hc, if_neg (Fin.ne_of_val_ne (by omega)), mul_zero, ite_self, sub_zero,
          hM₁c x c hc]
      · have hcj : c = j := Fin.ext (by omega)
        rw [hcj, hM₁jj, mul_one]
        by_cases hx : x = j
        · rw [hx]; simp [hM₁jj]
        · rw [if_pos (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩), sub_self, if_neg hx]
    have hM₂inv : ∃ M'', bwD_Int O M'' ∧ M'' * M₂ = 1 := by
      refine ⟨M' * (1 + Matrix.single j a d₁) * (1 + S),
        bwD_Int_mul (bwD_Int_mul hM'I hG₁I) (bwD_Int_add bwD_Int_one hSI), ?_⟩
      rw [hM₂, hM₁]
      calc M' * (1 + Matrix.single j a d₁) * (1 + S) * ((1 - S) * ((1 + Matrix.single j a c₁) * M))
          = M' * ((1 + Matrix.single j a d₁) * (((1 + S) * (1 - S)) * ((1 + Matrix.single j a c₁) * M))) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [hG₂, Matrix.one_mul, ← Matrix.mul_assoc (1 + Matrix.single j a d₁), hG₁, Matrix.one_mul, hM'M]
    have hM₂E := ih (k + 1) (by omega) M₂ hM₂I hM₂inv hstd₂
    have hMeq : M = (1 + Matrix.single j a d₁) * ((1 + S) * M₂) := by
      rw [hM₂, ← Matrix.mul_assoc (1 + S), hG₂, Matrix.one_mul, hM₁, ← Matrix.mul_assoc, hG₁, Matrix.one_mul]
    rw [hMeq]
    exact mul_mem hG₁E (mul_mem hG₂E hM₂E)

theorem bwD_decomp (hL : bwD_Loc O) (N M : Matrix (Fin r) (Fin r) ℂ) (t : ℂ)
    (hM : bwD_Int O M) (hNM : N * M = 1) (htN : ∀ a b, t * N a b ∈ O)
    (j : Fin r) (av : Fin r → ℂ) (hav : ∀ k, av k ∈ O)
    (hcol : ∀ k, k ≠ j → ∀ a, N a k - N a j * av k ∈ O) :
    ∃ K₁ K₂ : Matrix (Fin r) (Fin r) ℂ, K₁ ∈ bwA_EO O r ∧ K₂ ∈ bwA_EO O r ∧ M.det ∈ O ∧ M.det ≠ 0 ∧
      N.det * M.det = 1 ∧ t * N.det ∈ O ∧
      N = K₁ * Matrix.diagonal (Function.update 1 j (M.det)⁻¹) * K₂ := by
  have hpN : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
  have hp0 : M.det ≠ 0 := fun h => by rw [h, mul_zero] at hpN; exact zero_ne_one hpN
  have hadj : M.det • N = M.adjugate := by
    calc M.det • N = N * (M.det • (1 : Matrix (Fin r) (Fin r) ℂ)) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = N * (M * M.adjugate) := by rw [Matrix.mul_adjugate]
      _ = M.adjugate := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]

  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin r) (Fin r) ℂ,
      S = ∑ k ∈ Finset.univ.erase j, Matrix.single j k (av k) := ⟨_, rfl⟩
  have hX0 : ∀ k ∈ Finset.univ.erase j, ∀ k' ∈ Finset.univ.erase j,
      Matrix.single j k (av k) * Matrix.single j k' (av k') = 0 := by
    intro k hk k' _
    have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
    ext a b
    rw [bwD_single_mul_apply, Matrix.zero_apply]
    simp [Matrix.single_apply, hjk]
  have hSS : S * S = 0 := by
    rw [hS, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun b' hb' => hX0 b hb b' hb'
  have hCE : 1 + S ∈ bwA_EO O r := by
    rw [hS]
    exact bwD_sum_mem _ (fun k => Matrix.single j k (av k)) (fun k _ => bwD_gen_mem j k (hav k)) hX0
  have hdetC : (1 + S).det = 1 := by
    rw [hS]
    exact bwD_sum_det _ (fun k => Matrix.single j k (av k))
      (fun k hk => Matrix.det_transvection_of_ne j k (Finset.ne_of_mem_erase hk).symm (av k)) hX0
  have hCinv : (1 - S) * (1 + S) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hSS, add_zero, add_sub_cancel_right]
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : Matrix (Fin r) (Fin r) ℂ, N₀ = N * (1 - S) := ⟨_, rfl⟩
  have hN₀C : N₀ * (1 + S) = N := by rw [hN₀, Matrix.mul_assoc, hCinv, Matrix.mul_one]
  have hdetN₀ : N₀.det = N.det := by
    have h := congrArg Matrix.det hN₀C
    rw [Matrix.det_mul, hdetC, mul_one] at h
    exact h
  have hN₀e : ∀ a b, N₀ a b = N a b - if b ∈ Finset.univ.erase j then N a j * av b else 0 := by
    intro a b
    rw [hN₀, mul_sub, mul_one, Matrix.sub_apply, hS, Finset.mul_sum, Matrix.sum_apply]
    simp only [bwD_mul_single_apply]
    rw [Finset.sum_ite_eq]

  have hint : ∀ s : ℂ, (∀ a, N a j * s ∈ O) →
      bwD_Int O (N₀ * Matrix.diagonal (Function.update (1 : Fin r → ℂ) j s)) := by
    intro s hs a b
    rw [Matrix.mul_diagonal, hN₀e]
    by_cases hb : b = j
    · rw [hb]; simpa using hs a
    · have h1 : Function.update (1 : Fin r → ℂ) j s b = 1 := by simp [hb]
      rw [h1, mul_one, if_pos (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩)]
      exact hcol b hb a
  have hdet : ∀ s : ℂ, (N₀ * Matrix.diagonal (Function.update (1 : Fin r → ℂ) j s)).det = N.det * s := by
    intro s
    rw [Matrix.det_mul, Matrix.det_diagonal, hdetN₀, Finset.prod_update_of_mem (Finset.mem_univ j)]
    simp
  have hpj : ∀ a, N a j * M.det ∈ O := by
    intro a
    have h := bwD_Int_adj hM a j
    rw [← hadj, Matrix.smul_apply, smul_eq_mul, mul_comm] at h
    exact h
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : Matrix (Fin r) (Fin r) ℂ,
      N₁ = N₀ * Matrix.diagonal (Function.update (1 : Fin r → ℂ) j M.det) := ⟨_, rfl⟩
  have hN₁I : bwD_Int O N₁ := by rw [hN₁]; exact hint _ hpj
  have hdetN₁ : N₁.det = 1 := by rw [hN₁, hdet, hpN]
  have hN₁E : N₁ ∈ bwA_EO O r :=
    bwD_elim hL N₁ hN₁I ⟨N₁.adjugate, bwD_Int_adj hN₁I, by rw [Matrix.adjugate_mul, hdetN₁, one_smul]⟩
  have hdd : Matrix.diagonal (Function.update (1 : Fin r → ℂ) j M.det) *
      Matrix.diagonal (Function.update (1 : Fin r → ℂ) j (M.det)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i = j
    · rw [h]; simp [hp0]
    · simp [h]
  have htd : t * N.det ∈ O := by
    have h := bwD_det_mem (hint t fun a => by rw [mul_comm]; exact htN a j)
    rw [hdet, mul_comm] at h
    exact h
  refine ⟨N₁, 1 + S, hN₁E, hCE, bwD_det_mem hM, hp0, hpN, htd, ?_⟩
  rw [hN₁, Matrix.mul_assoc N₀, hdd, Matrix.mul_one, hN₀C]

end Gen

section Spec

open Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms
open scoped Matrix

variable (D : D7) (u : D.what₂.Word)

theorem bwD_loc_Ow (w : D.what₂.places.Pl) : bwD_Loc (bwA_Ow D w) := by
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

theorem bwD_mem_Ow (w : D.what₂.places.Pl) (hw : OverT D u w) (τ : D.what₂.Tau) (y : D.host.E) (s : ℕ)
    (hs : ¬ (D.mem u).A.T ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    embT D τ y ∈ bwA_Ow D w := by
  rw [bwA_embT_eq]
  exact Subring.mem_map.2 ⟨_, bwA_val_locInt D w ((D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) y s
    (by rw [hw]; exact hs) hy, rfl⟩

theorem bwD_mulVec_col {n : ℕ} (A B : Matrix (Fin n) (Fin n) D.host.E) (a k : Fin n) :
    (A *ᵥ fun r => B r k) a = (A * B) a k := rfl

theorem bwD_locBasis_int (w : D.what₂.places.Pl) (hw : OverT D u w) (τ : D.what₂.Tau) {n : ℕ}
    {L : Set (Fin n → D.host.E)} {B : GL (Fin n) D.host.E} (hB : IsLocBasis (D.mem u).A.T L B)
    (x : Fin n → D.host.E) (s : ℕ) (hs : ¬ (D.mem u).A.T ∣ s) (hx : (s : D.host.E) • x ∈ L) (a : Fin n) :
    embT D τ ((((B⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x) a) ∈ bwA_Ow D w := by
  obtain ⟨s', hs', h⟩ := (hB x).1 ⟨s, hs, hx⟩
  exact bwD_mem_Ow D u w hw τ _ s' hs' (h a)

theorem bwD_col_loc (w : D.what₂.places.Pl) (hw : OverT D u w) {n : ℕ} {L : Set (Fin n → D.host.E)}
    {B : GL (Fin n) D.host.E} (hB : IsLocBasis (D.mem u).A.T L B) (k : Fin n) :
    ∃ s : ℕ, ¬ (D.mem u).A.T ∣ s ∧ (s : D.host.E) • (fun r => (B : Matrix (Fin n) (Fin n) D.host.E) r k) ∈ L := by
  refine (hB _).2 ⟨1, ?_, fun a => ?_⟩
  · rw [← hw]; exact (D.what₂.places.resChar_prime w).not_dvd_one
  · rw [Nat.cast_one, one_mul, bwD_mulVec_col, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩

def BwLcInt : Prop :=
  ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i), clsCrd D u i hi c ≤ Ld D u i hi c

end Spec

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
