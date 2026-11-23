import Mathlib

namespace GlobalTheory.IwaFlag

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}

def Princ (ε : R) (O : AddSubgroup R) : Prop :=
  ∀ J : AddSubgroup R, (∀ a ∈ J, ε * a = a) → (∀ o ∈ O, ∀ a ∈ J, o * a ∈ J) → (∃ m : ℕ, 0 < m ∧ (m : R) * ε ∈ J) →
    (∃ N : ℕ, 0 < N ∧ ∀ a ∈ J, (N : R) * a ∈ O) → ∃ α ∈ J, ∃ α', ε * α' = α' ∧ α * α' = ε ∧ ∀ a ∈ J, α' * a ∈ O

theorem smul_mem_of_sd (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hM₁ : ∀ y ∈ M, ε • y = y)
    (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O)) {o : R} (ho : o ∈ O) {y : V} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM₂ _ (by rw [smul_comm, hM₁ y hy])).2 fun x hx => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact hmul _ ho _ ((hM₂ y (hM₁ y hy)).1 hy x hx)

theorem exists_triangular (hεc : c ε = ε) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M) (i : Fin ρ) :
    ∃ (b : Fin ρ → R) (α' : R), (∀ l, i < l → b l = 0) ∧ X b ∈ M ∧ ε * α' = α' ∧ b i * α' = ε ∧
      ∀ t : Fin ρ → R, (∀ l, i < l → t l = 0) → X t ∈ M → α' * t i ∈ O := by
  have hfix : ∀ t, X t ∈ M → ∀ k, ε * t k = t k := fun t ht k => by
    have := congrArg (fun z => h z (f k)) (hM₁ _ ht)
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hXf] using this
  let J : AddSubgroup R :=
    { carrier := {a | ∃ t : Fin ρ → R, (∀ l, i < l → t l = 0) ∧ X t ∈ M ∧ t i = a}
      zero_mem' := ⟨0, fun _ _ => rfl, by rw [map_zero]; exact M.zero_mem, rfl⟩
      add_mem' := by
        rintro _ _ ⟨t, h1, h2, rfl⟩ ⟨s, g1, g2, rfl⟩
        exact ⟨t + s, fun l hl => by simp [h1 l hl, g1 l hl], by rw [map_add]; exact M.add_mem h2 g2, rfl⟩
      neg_mem' := by
        rintro _ ⟨t, h1, h2, rfl⟩
        exact ⟨-t, fun l hl => by simp [h1 l hl], by rw [map_neg]; exact M.neg_mem h2, rfl⟩ }
  obtain ⟨α, ⟨b, hb1, hb2, rfl⟩, α', h1, h2, h3⟩ := hP J
    (by rintro _ ⟨t, -, h2, rfl⟩; exact hfix t h2 i)
    (by
      rintro o ho _ ⟨t, h1, h2, rfl⟩
      exact ⟨o • t, fun l hl => by simp [h1 l hl], by rw [map_smul]; exact smul_mem_of_sd hmul hM₁ hM₂ ho h2, rfl⟩)
    ⟨N, hN, Pi.single i ((N : R) * ε), fun l hl => Pi.single_eq_of_ne hl.ne' _, he i, Pi.single_eq_same _ _⟩
    ⟨N, hN, by
      rintro _ ⟨t, -, h2, rfl⟩
      have := (hM₂ _ (hM₁ _ h2)).1 h2 _ (hf i)
      rwa [map_smulₛₗ, hXf, map_mul, map_natCast, hεc, smul_eq_mul, mul_assoc, hfix t h2 i] at this⟩
  exact ⟨b, α', hb1, hb2, h1, h2, fun t ht1 ht2 => h3 _ ⟨t, ht1, ht2, rfl⟩⟩

theorem exists_step (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O) (hOε : ∀ a ∈ O, ε * a = a)
    (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M)
    (b : Fin ρ → Fin ρ → R) (hb₁ : ∀ i l, i < l → b i l = 0) (hb₂ : ∀ i, X (b i) ∈ M) (j : Fin ρ) (α' : R)
    (hα : b j j * α' = ε) (hJ : ∀ t : Fin ρ → R, (∀ l, j < l → t l = 0) → X t ∈ M → α' * t j ∈ O)
    (ih : ∀ z : Fin ρ → R, (∀ i, z i ∈ O) → ∃ y ∈ M, ∀ i, i < j → h (X (b i)) y = z i) :
    ∃ w ∈ M, (∀ i, i < j → h (X (b i)) w = 0) ∧ h (X (b j)) w = ε := by
  classical
  have hint : ∀ i, ∀ y ∈ M, h (X (b i)) y ∈ O := fun i => (hM₂ _ (hM₁ _ (hb₂ i))).1 (hb₂ i)
  have hsm : ∀ {o : R}, o ∈ O → ∀ {y : V}, y ∈ M → o • y ∈ M := fun ho _ hy => smul_mem_of_sd hmul hM₁ hM₂ ho hy
  let K : AddSubgroup R :=
    { carrier := {a | ∃ y ∈ M, (∀ i, i < j → h (X (b i)) y = 0) ∧ h (X (b j)) y = a}
      zero_mem' := ⟨0, M.zero_mem, fun _ _ => map_zero _, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨t, h1, h2, rfl⟩ ⟨s, g1, g2, rfl⟩
        exact ⟨t + s, M.add_mem h1 g1, fun l hl => by rw [map_add, h2 l hl, g2 l hl, add_zero], map_add _ _ _⟩
      neg_mem' := by
        rintro _ ⟨t, h1, h2, rfl⟩
        exact ⟨-t, M.neg_mem h1, fun l hl => by rw [map_neg, h2 l hl, neg_zero], map_neg _ _⟩ }
  have hKO : ∀ o ∈ O, ∀ a ∈ K, o * a ∈ K := by
    rintro o ho _ ⟨t, h1, h2, rfl⟩
    exact ⟨c o • t, hsm (hcO o ho) h1, fun l hl => by rw [map_smulₛₗ, h2 l hl, smul_zero],
      by rw [map_smulₛₗ, hcc, smul_eq_mul]⟩
  have hαN : α' * ((N : R) * ε) ∈ O := by
    have := hJ (Pi.single j ((N : R) * ε)) (fun l hl => Pi.single_eq_of_ne hl.ne' _) (he j)
    rwa [Pi.single_eq_same] at this
  have hNK : (N : R) * ε * b j j ∈ K :=
    ⟨_, hf j, fun i hi => by rw [map_smulₛₗ, hXf, hb₁ i j hi, smul_zero],
      by rw [map_smulₛₗ, hXf, map_mul, map_natCast, hεc, smul_eq_mul]⟩
  obtain ⟨β, hβ, β', h1, h2, h3⟩ := hP K
    (by rintro _ ⟨t, h1, -, rfl⟩; exact hOε _ (hint j t h1)) hKO
    ⟨N * N, Nat.mul_pos hN hN, by
      have e : ((N * N : ℕ) : R) * ε = α' * ((N : R) * ε) * ((N : R) * ε * b j j) := by
        push_cast
        linear_combination (-(N : R) * N * ε * ε) * hα - ((N : R) * N * (ε + 1)) * hεε
      rw [e]; exact hKO _ hαN _ hNK⟩
    ⟨1, one_pos, by rintro _ ⟨t, h1, -, rfl⟩; rw [Nat.cast_one, one_mul]; exact hint j t h1⟩
  choose g hg hg' using fun i : Fin ρ => ih (Pi.single i ε) fun l => by
    by_cases hl : l = i
    · rw [hl, Pi.single_eq_same]; exact hεO
    · rw [Pi.single_eq_of_ne hl]; exact O.zero_mem
  let s := Finset.univ.filter (· < j)
  let t : Fin ρ → R := β' • b j - ∑ i ∈ s, (β' * h (X (b j)) (g i)) • b i
  have hXt : X t = β' • X (b j) - ∑ i ∈ s, (β' * h (X (b j)) (g i)) • X (b i) := by
    simp only [t, map_sub, map_sum, map_smul]
  have htM : X t ∈ M := by
    refine (hM₂ _ ?_).2 fun y hy => ?_
    · rw [hXt, smul_sub, Finset.smul_sum, smul_smul, h1]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, ← mul_assoc, h1]
    · have hy' : y - ∑ i ∈ s, c (h (X (b i)) y) • g i ∈ M :=
        M.sub_mem hy (M.sum_mem fun i _ => hsm (hcO _ (hint i y hy)) (hg i))
      have hK : h (X (b j)) (y - ∑ i ∈ s, c (h (X (b i)) y) • g i) ∈ K := by
        refine ⟨_, hy', fun l hl => ?_, rfl⟩
        rw [map_sub, map_sum, Finset.sum_eq_single l]
        · rw [map_smulₛₗ, hcc, hg' l l hl, Pi.single_eq_same, smul_eq_mul, mul_comm, hOε _ (hint l y hy), sub_self]
        · intro i _ hi
          rw [map_smulₛₗ, hg' i l hl, Pi.single_eq_of_ne hi.symm, smul_zero]
        · intro hl'; exact absurd (by simpa [s] using hl) hl'
      have := h3 _ hK
      convert this using 1
      rw [hXt]
      simp only [map_sub, map_sum, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, hcc, mul_sub, Finset.mul_sum, RingHom.id_apply]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
  have hz : ∀ l, j ≤ l → (∑ i ∈ s, (β' * h (X (b j)) (g i)) • b i) l = 0 := fun l hl => by
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i hi => by
      rw [Pi.smul_apply, hb₁ i l (lt_of_lt_of_le (Finset.mem_filter.1 hi).2 hl), smul_zero]
  have hβ' : β' ∈ O := by
    have := hJ t (fun l hl => by
      simp only [t]
      rw [Pi.sub_apply, hz l hl.le, Pi.smul_apply, hb₁ j l hl, smul_zero, sub_zero]) htM
    simp only [t] at this
    rw [Pi.sub_apply, hz j le_rfl, Pi.smul_apply, sub_zero, smul_eq_mul] at this
    have e : α' * (β' * b j j) = β' := by linear_combination β' * hα + h1
    rwa [e] at this
  have := hKO _ hβ' _ hβ
  rw [mul_comm, h2] at this
  exact this

theorem exists_flag_dual (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O)
    (hOε : ∀ a ∈ O, ε * a = a) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M) :
    ∃ b : Fin ρ → Fin ρ → R, (∀ i l, i < l → b i l = 0) ∧ (∀ i l, ε * b i l = b i l) ∧ (∀ i, X (b i) ∈ M) ∧
      ∃ y : Fin ρ → V, (∀ j, y j ∈ M) ∧ ∀ i j, h (X (b i)) (y j) = if i = j then ε else 0 := by
  classical
  choose b α' hb₁ hb₂ _ hα hJ using exists_triangular hεc hmul hP hM₁ hM₂ X f hXf N hN he hf
  have hint : ∀ i, ∀ y ∈ M, h (X (b i)) y ∈ O := fun i => (hM₂ _ (hM₁ _ (hb₂ i))).1 (hb₂ i)
  have key : ∀ n : ℕ, n ≤ ρ → ∀ z : Fin ρ → R, (∀ i, z i ∈ O) → ∃ y ∈ M, ∀ i : Fin ρ, i.1 < n → h (X (b i)) y = z i := by
    intro n
    induction n with
    | zero => exact fun _ z _ => ⟨0, M.zero_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn z hz
      let j : Fin ρ := ⟨n, hn⟩
      obtain ⟨w, hw, hw₁, hw₂⟩ := exists_step hcc hεε hεc hεO hOε hmul hcO hP hM₁ hM₂ X f hXf N hN he hf b hb₁ hb₂ j
        (α' j) (hα j) (hJ j) (ih (Nat.le_of_succ_le hn))
      obtain ⟨y, hy, hy'⟩ := ih (Nat.le_of_succ_le hn) z hz
      have ho : z j - h (X (b j)) y ∈ O := O.sub_mem (hz j) (hint j y hy)
      refine ⟨y + c (z j - h (X (b j)) y) • w, M.add_mem hy (smul_mem_of_sd hmul hM₁ hM₂ (hcO _ ho) hw), fun i hi => ?_⟩
      rw [map_add, map_smulₛₗ, hcc, smul_eq_mul]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · rw [hw₁ i hi, hy' i hi, mul_zero, add_zero]
      · have : i = j := Fin.ext hi
        rw [this, hw₂, mul_comm, hOε _ ho, add_sub_cancel]
  choose y hy hy' using fun j : Fin ρ => key ρ le_rfl (Pi.single j ε) fun l => by
    by_cases hl : l = j
    · rw [hl, Pi.single_eq_same]; exact hεO
    · rw [Pi.single_eq_of_ne hl]; exact O.zero_mem
  refine ⟨b, hb₁, fun i k => ?_, hb₂, y, hy, fun i j => ?_⟩
  · have := congrArg (fun z => h z (f k)) (hM₁ _ (hb₂ i))
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hXf] using this
  · rw [hy' j i i.2, Pi.single_apply]

open Matrix in

def sesq (c : R →+* R) {n : ℕ} (G : Matrix (Fin n) (Fin n) R) : (Fin n → R) →ₗ[R] (Fin n → R) →ₛₗ[c] R :=
  LinearMap.mk₂'ₛₗ (RingHom.id R) c (fun x y => ∑ i, ∑ j, c (y i) * G i j * x j)
    (fun x x' y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

open Matrix in
theorem sesq_col {n p q : ℕ} (G : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin p) R) (B : Matrix (Fin n) (Fin q) R)
    (i : Fin p) (j : Fin q) : sesq c G (fun k => A k i) (fun k => B k j) = ((B.map c)ᵀ * (G * A)) j i := by
  simp only [sesq, LinearMap.mk₂'ₛₗ_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc]

open Matrix in

theorem exists_flag_dual_matrix {n : ℕ} {M : AddSubgroup (Fin n → R)} (G : Matrix (Fin n) (Fin n) R)
    (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O)
    (hOε : ∀ a ∈ O, ε * a = a) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ∀ i, ε * y i = y i)
    (hM₂ : ∀ y : Fin n → R, (∀ i, ε * y i = y i) → (y ∈ M ↔ ∀ x ∈ M, ∑ i, ∑ j, c (x i) * G i j * y j ∈ O))
    (E F : Matrix (Fin n) (Fin ρ) R) (hEF : (F.map c)ᵀ * (G * E) = 1) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, (fun l => (N : R) * ε * E l k) ∈ M) (hf : ∀ k, (fun l => (N : R) * ε * F l k) ∈ M) :
    ∃ b : Matrix (Fin ρ) (Fin ρ) R, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, ε * b i j = b i j) ∧
      (∀ i, (fun k => (E * b) k i) ∈ M) ∧ ∃ c' : Matrix (Fin n) (Fin ρ) R, (∀ i, (fun k => c' k i) ∈ M) ∧
        (c'.map c)ᵀ * (G * (E * b)) = ε • (1 : Matrix (Fin ρ) (Fin ρ) R) := by
  classical
  obtain ⟨b, h1, h2, h3, y, h4, h5⟩ := exists_flag_dual (h := sesq c G) (M := M) hcc hεε hεc hεO hOε hmul hcO hP
    (fun y hy => funext (hM₁ y hy)) (fun y hy => hM₂ y (congrFun hy)) E.mulVecLin (fun k l => F l k)
    (fun t k => by
      have := sesq_col (c := c) G (E * Matrix.of fun l (_ : Fin 1) => t l) F 0 k
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ G, hEF, Matrix.one_mul] at this
      exact this) N hN
    (fun k => by
      convert he k using 1
      ext l
      simp [mul_comm]) hf
  refine ⟨Matrix.of fun i j => b j i, fun i j hij => h1 j i hij, fun i j => h2 j i, h3, Matrix.of fun k j => y j k, h4, ?_⟩
  ext j i
  rw [← sesq_col]
  refine (h5 i j).trans ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Matrix.one_apply_ne (Ne.symm hij)]

end GlobalTheory.IwaFlag
