import Mathlib

namespace GlobalTheory.InvariantLift

variable {G : Type} [Group G] {A : Type} [CommRing A] {r : ℕ}

theorem average_step (σ : G → A →+* A) (hσ : ∀ g h a, σ (g * h) a = σ g (σ h a))
    (M : G →* Matrix (Fin r) (Fin r) A) (hM : ∀ g h i j, σ g (M h i j) = M h i j)
    (N : Subgroup G) [hN : N.Normal] [Finite (G ⧸ N)] (τ : A) (hτ : ∀ g ∈ N, σ g τ = τ)
    (hτ1 : ∑ᶠ x : G ⧸ N, σ x.out τ = 1) (c d : A) (hd : ∀ g ∈ N, ∀ i j, d ∣ (M g - 1) i j)
    (W : Matrix (Fin r) (Fin r) A) (hW : ∀ g ∈ N, W.map (σ g) = W)
    (hc : ∀ g i j, c ∣ (M g * W.map (σ g) - W) i j) :
    ∃ W' : Matrix (Fin r) (Fin r) A, (∀ i j, c ∣ (W - W') i j) ∧ (∀ g ∈ N, W'.map (σ g) = W') ∧
      ∀ g i j, d ∣ (M g * W'.map (σ g) - W') i j := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _

  have dl : ∀ (e : A) (X : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ X i j) →
      ∀ (Y : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e X hX Y i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hX i k).mul_right _
  have dr : ∀ (e : A) (Y : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ Y i j) →
      ∀ (X : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e Y hY X i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hY k j).mul_left _

  have hfix : ∀ a : A, (∀ m ∈ N, σ m a = a) → ∀ g, ∀ n ∈ N, σ n (σ g a) = σ g a := by
    intro a ha g n hn
    have hm : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
    rw [← hσ, show n * g = g * (g⁻¹ * n * g) by group, hσ, ha _ hm]
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin r) (Fin r) A, U = τ • W := ⟨_, rfl⟩
  have hUfix : ∀ m ∈ N, ∀ k l, σ m (U k l) = U k l := by
    intro m hm k l
    have hWe : σ m (W k l) = W k l := congrFun (congrFun (hW m hm) k) l
    rw [hU, Matrix.smul_apply, smul_eq_mul, map_mul, hτ m hm, hWe]
  have hUl : ∀ g, ∀ n ∈ N, U.map (σ (n * g)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ]
    exact hfix _ (fun m hm => hUfix m hm k l) g n hn
  have hUr : ∀ g, ∀ n ∈ N, U.map (σ (g * n)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ, hUfix n hn]
  have hMfix : ∀ g h, (M h).map (σ g) = M h := by
    intro g h
    ext i j
    exact hM g h i j
  have hUmap : ∀ g h, (U.map (σ h)).map (σ g) = U.map (σ (g * h)) := by
    intro g h
    ext i j
    simp [hσ]
  have hsum : ∀ (f : A →+* A) (X : G ⧸ N → Matrix (Fin r) (Fin r) A),
      (∑ x, X x).map f = ∑ x, (X x).map f := by
    intro f X
    ext i j
    simp [Matrix.sum_apply, map_sum]

  refine ⟨∑ x : G ⧸ N, M x.out * U.map (σ x.out), ?_, ?_, ?_⟩
  · intro i j
    have h1 : ∑ x : G ⧸ N, σ x.out τ = 1 := by
      rw [← finsum_eq_sum_of_fintype]
      exact hτ1
    have hent : ∀ x : G ⧸ N, (M x.out * U.map (σ x.out)) i j =
        σ x.out τ * (M x.out * W.map (σ x.out)) i j := by
      intro x
      simp only [hU, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hsplit : (W - ∑ x : G ⧸ N, M x.out * U.map (σ x.out)) i j =
        ∑ x : G ⧸ N, σ x.out τ * (W i j - (M x.out * W.map (σ x.out)) i j) := by
      rw [Matrix.sub_apply, Matrix.sum_apply, Finset.sum_congr rfl (fun x _ => hent x)]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    rw [hsplit]
    refine Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right ?_ _
    exact dvd_sub_comm.mp (by simpa only [Matrix.sub_apply] using hc x.out i j)
  · intro n hn
    rw [hsum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.map_mul, hMfix, hUmap, hUl _ n hn]
  · intro g i j
    have hmul : M g * (∑ x : G ⧸ N, M x.out * U.map (σ x.out)).map (σ g) =
        ∑ x : G ⧸ N, M (g * x.out) * U.map (σ (g * x.out)) := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.map_mul, hMfix, hUmap, map_mul, mul_assoc]
    have hre : ∑ x : G ⧸ N, M x.out * U.map (σ x.out) =
        ∑ x : G ⧸ N, M (g • x).out * U.map (σ (g • x).out) :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun y : G ⧸ N => M y.out * U.map (σ y.out))).symm
    rw [hmul, hre, ← Finset.sum_sub_distrib, Matrix.sum_apply]
    refine Finset.dvd_sum fun x _ => ?_
    obtain ⟨n, hn, hgx⟩ : ∃ n ∈ N, g * x.out = (g • x).out * n := by
      refine ⟨((g • x).out)⁻¹ * (g * x.out), ?_, (mul_inv_cancel_left _ _).symm⟩
      rw [← QuotientGroup.eq]
      simp only [QuotientGroup.out_eq']
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      simp only [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.mk_mul, QuotientGroup.out_eq',
        Quotient.out_eq]
    rw [hgx, map_mul, hUr _ n hn]
    have hfac : M (g • x).out * M n * U.map (σ (g • x).out) - M (g • x).out * U.map (σ (g • x).out)
        = M (g • x).out * ((M n - 1) * U.map (σ (g • x).out)) := by
      noncomm_ring
    rw [hfac]
    exact dr d _ (dl d _ (fun i' j' => by simpa [Matrix.sub_apply] using hd n hn i' j') _) _ i j

theorem exists_invariant_lift : ∀ (G : Type) [Group G] (A : Type) [CommRing A] (π : A), IsAdicComplete (Ideal.span {π}) A → ∀ (σ : G → A →+* A), (∀ g h a, σ (g * h) a = σ g (σ h a)) → (∀ g, σ g π = π) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) A), (∀ g h i j, σ g (M h i j) = M h i j) → ∀ (S : Set (Subgroup G)), (∀ N ∈ S, N.Normal ∧ Finite (G ⧸ N) ∧ ∃ τ : A, (∀ g ∈ N, σ g τ = τ) ∧ ∑ᶠ x : G ⧸ N, σ x.out τ = 1) → (∀ N ∈ S, ∀ k : ℕ, ∃ N' ∈ S, N' ≤ N ∧ ∀ g ∈ N', ∀ i j, π ^ k ∣ (M g - 1) i j) → ∀ (W₀ : Matrix (Fin r) (Fin r) A), (∃ N ∈ S, ∀ g ∈ N, W₀.map (σ g) = W₀) → (∀ g i j, π ∣ (M g * W₀.map (σ g) - W₀) i j) → ∃ W : Matrix (Fin r) (Fin r) A, (∀ i j, π ∣ (W - W₀) i j) ∧ ∀ g, M g * W.map (σ g) = W := by
  intro G _ A _ π hA σ hσ hσπ r M hM S hS hSk W₀ hW₀ hW₀c
  classical

  have hstep : ∀ (k : ℕ) (N : Subgroup G) (W : Matrix (Fin r) (Fin r) A), N ∈ S →
      (∀ g ∈ N, W.map (σ g) = W) → (∀ g i j, π ^ (k + 1) ∣ (M g * W.map (σ g) - W) i j) →
      ∃ (N' : Subgroup G) (W' : Matrix (Fin r) (Fin r) A), N' ∈ S ∧ (∀ g ∈ N', W'.map (σ g) = W') ∧
        (∀ g i j, π ^ (k + 1 + 1) ∣ (M g * W'.map (σ g) - W') i j) ∧
        ∀ i j, π ^ (k + 1) ∣ (W - W') i j := by
    intro k N W hNS hWN hWc
    obtain ⟨N', hN'S, hN'N, hN'd⟩ := hSk N hNS (k + 1 + 1)
    obtain ⟨hN'n, hN'f, τ, hτ, hτ1⟩ := hS N' hN'S
    haveI := hN'n
    haveI := hN'f
    obtain ⟨W', h1, h2, h3⟩ := GlobalTheory.InvariantLift.average_step σ hσ M hM N' τ hτ hτ1
      (π ^ (k + 1)) (π ^ (k + 1 + 1)) hN'd W (fun g hg => hWN g (hN'N hg)) hWc
    exact ⟨N', W', hN'S, h2, h3, h1⟩
  choose! Nf Wf hNf hWf hcf hdf using hstep
  obtain ⟨N₀, hN₀S, hN₀W⟩ := hW₀
  obtain ⟨seq, hseq0, hseqs⟩ : ∃ seq : ℕ → Subgroup G × Matrix (Fin r) (Fin r) A,
      seq 0 = (N₀, W₀) ∧ ∀ k, seq (k + 1) = (Nf k (seq k).1 (seq k).2, Wf k (seq k).1 (seq k).2) :=
    ⟨fun k => Nat.rec (N₀, W₀) (fun k q => (Nf k q.1 q.2, Wf k q.1 q.2)) k, rfl, fun _ => rfl⟩
  have hP : ∀ k, (seq k).1 ∈ S ∧ (∀ g ∈ (seq k).1, (seq k).2.map (σ g) = (seq k).2) ∧
      ∀ g i j, π ^ (k + 1) ∣ (M g * (seq k).2.map (σ g) - (seq k).2) i j := by
    intro k
    induction k with
    | zero => exact ⟨by simp [hseq0, hN₀S], by simpa [hseq0] using hN₀W,
        by simpa [hseq0] using hW₀c⟩
    | succ k ih =>
      rw [hseqs]
      exact ⟨hNf k _ _ ih.1 ih.2.1 ih.2.2, hWf k _ _ ih.1 ih.2.1 ih.2.2, hcf k _ _ ih.1 ih.2.1 ih.2.2⟩
  have hd : ∀ k i j, π ^ (k + 1) ∣ (seq k).2 i j - (seq (k + 1)).2 i j := by
    intro k i j
    have := hdf k _ _ (hP k).1 (hP k).2.1 (hP k).2.2 i j
    rw [hseqs]
    simpa [Matrix.sub_apply] using this
  have hcauchy : ∀ m n, m ≤ n → ∀ i j, π ^ m ∣ (seq m).2 i j - (seq n).2 i j := by
    intro m n hmn i j
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : (seq m).2 i j - (seq (n + 1)).2 i j =
          ((seq m).2 i j - (seq n).2 i j) + ((seq n).2 i j - (seq (n + 1)).2 i j) := by ring
      rw [e]
      exact dvd_add ih ((pow_dvd_pow π (by omega)).trans (hd n i j))

  have hmod : ∀ (n : ℕ) (x y : A),
      x ≡ y [SMOD ((Ideal.span {π}) ^ n • (⊤ : Submodule A A))] ↔ π ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hlim : ∀ i j, ∃ L : A, ∀ n, π ^ n ∣ (seq n).2 i j - L := by
    intro i j
    obtain ⟨L, hL⟩ := hA.toIsPrecomplete.prec (f := fun n => (seq n).2 i j)
      (fun {m n} hmn => (hmod m _ _).mpr (hcauchy m n hmn i j))
    exact ⟨L, fun n => (hmod n _ _).mp (hL n)⟩
  choose L hL using hlim
  refine ⟨Matrix.of L, ?_, ?_⟩
  · intro i j
    have a := hd 0 i j
    have b := hL i j 1
    rw [hseq0] at a
    simp only [zero_add, pow_one] at a b
    have c : π ∣ W₀ i j - L i j := by
      have e : W₀ i j - L i j = (W₀ i j - (seq 1).2 i j) + ((seq 1).2 i j - L i j) := by ring
      rw [e]
      exact dvd_add a b
    simpa [Matrix.sub_apply] using dvd_sub_comm.mp c
  · intro g
    ext i j
    apply sub_eq_zero.mp
    rw [← Matrix.sub_apply]
    apply hA.toIsHausdorff.haus
    intro n
    rw [hmod, sub_zero]
    have key : (M g * (Matrix.of L).map (σ g) - Matrix.of L) i j =
        (∑ k, M g i k * σ g (L k j - (seq n).2 k j)) +
          (M g * (seq n).2.map (σ g) - (seq n).2) i j + ((seq n).2 i j - L i j) := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, map_sub,
        mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
    refine dvd_add (dvd_add (Finset.dvd_sum fun k _ => ?_) ?_) (hL i j n)
    · obtain ⟨e, he⟩ := dvd_sub_comm.mp (hL k j n)
      refine dvd_mul_of_dvd_right ⟨σ g e, ?_⟩ _
      rw [he, map_mul, map_pow, hσπ]
    · exact (pow_dvd_pow π (Nat.le_succ n)).trans ((hP n).2.2 g i j)

end GlobalTheory.InvariantLift
