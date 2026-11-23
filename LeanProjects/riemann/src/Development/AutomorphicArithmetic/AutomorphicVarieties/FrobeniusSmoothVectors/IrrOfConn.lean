import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ArtinRees
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AddMulSelfEqOfOrthogonalIdempotents

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem irr_coord {G K : Type} [Group G] [Field K] {n : ℕ} {a : G → Matrix (Fin n) (Fin n) K}
    (h : MatIrr ⊤ a) (p q : Fin n) (hpq : q ≠ p) : ¬ ∀ g i, i ≠ p → a g i p = 0 := by
  intro hz
  rcases h (Submodule.span K {Pi.single p 1}) (fun g _ v hv => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    refine Submodule.mem_span_singleton.2 ⟨c * a g p p, ?_⟩
    ext i
    by_cases hi : i = p
    · subst hi; simp [Matrix.mulVec_smul]
    · simp [Matrix.mulVec_smul, hi, hz g i hi]) with h | h
  · have := Submodule.span_singleton_eq_bot.1 h
    simpa using congrFun this p
  · have : (Pi.single q 1 : Fin n → K) ∈ Submodule.span K {(Pi.single p 1 : Fin n → K)} := h ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    simpa [hpq] using congrFun hc q

private theorem irr_of_conn {G K : Type} [Group G] [Field K] {n : ℕ} {a : G → Matrix (Fin n) (Fin n) K}
    (hE : ∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, a g *ᵥ v ∈ W) → ∀ i, ∀ v ∈ W, single i i (1 : K) *ᵥ v ∈ W)
    (hc : ∀ P : Fin n → Prop, (∀ i j, (¬ ∀ g, a g i j = 0) → P j → P i) → ∀ i j, P j → P i) : MatIrr ⊤ a := by
  intro W hW
  have hW' : ∀ g, ∀ v ∈ W, a g *ᵥ v ∈ W := fun g => hW g (Subgroup.mem_top g)
  have h1 : ∀ v ∈ W, ∀ i, v i ≠ 0 → (Pi.single i 1 : Fin n → K) ∈ W := fun v hv i h => by
    convert W.smul_mem (v i)⁻¹ (hE W hW' i v hv) using 1
    ext k
    by_cases hk : k = i
    · subst hk; simp [Matrix.single_mulVec, h]
    · simp [Matrix.single_mulVec, hk]
  have h2 := hc (fun i => (Pi.single i 1 : Fin n → K) ∈ W) fun i j hn hj => by
    obtain ⟨g, hg⟩ := not_forall.1 hn
    exact h1 _ (hW' g _ hj) i (by simpa using hg)
  rw [or_iff_not_imp_left]
  intro h0
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 h0
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine W.sum_mem fun i _ => ?_
  convert W.smul_mem (x i) (h2 i j (h1 v hv j hj)) using 1
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

private theorem jtj {K : Type} [CommRing K] {n : ℕ} (m : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat K n * mᵀ * Jmat K n) i j = m j.rev i.rev := by
  have h : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => propext ⟨fun e => by simp [e], fun e => by simp [e]⟩
  simp [Matrix.mul_apply, Jmat, h]

private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

private theorem conn2 (Z : Fin 2 → Fin 2 → Prop) (hP : ¬ ∀ i j, j < i → Z i j) (hM : ¬ ∀ i j, i < j → Z i j)
    (P : Fin 2 → Prop) (h : ∀ i j, ¬ Z i j → P j → P i) : ∀ i j, P j → P i := by
  have h10 := h 1 0
  have h01 := h 0 1
  simp only [Fin.forall_fin_two] at hP hM ⊢
  simp at hP hM
  tauto

private theorem conn3 (Z : Fin 3 → Fin 3 → Prop) (hs : ∀ i j, Z i j → Z j.rev i.rev)
    (hP : ¬ ∀ i j, j < i → Z i j) (hM : ¬ ∀ i j, i < j → Z i j) (hE : ¬ ∀ i j, Odd (w 3 i - w 3 j) → Z i j)
    (P : Fin 3 → Prop) (h : ∀ i j, ¬ Z i j → P j → P i) : ∀ i j, P j → P i := by
  have s1 : Z 1 0 → Z 2 1 := hs 1 0
  have s2 : Z 2 1 → Z 1 0 := hs 2 1
  have s3 : Z 0 1 → Z 1 2 := hs 0 1
  have s4 : Z 1 2 → Z 0 1 := hs 1 2
  have hP' : ¬ (Z 1 0 ∧ Z 2 0) := fun ⟨x, y⟩ => hP fun i j hij => by
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact x | exact y | exact s1 x
  have hM' : ¬ (Z 0 1 ∧ Z 0 2) := fun ⟨x, y⟩ => hM fun i j hij => by
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact x | exact y | exact s3 x
  have hE' : ¬ (Z 0 1 ∧ Z 1 0) := fun ⟨x, y⟩ => hE fun i j hij => by
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | exact x | exact y | exact s3 x | exact s1 y
  have h10 := h 1 0
  have h01 := h 0 1
  have h20 := h 2 0
  have h02 := h 0 2
  have h12 := h 1 2
  have h21 := h 2 1
  have key : (P 0 → P 1) ∧ (P 1 → P 2) ∧ (P 2 → P 0) := by
    by_cases a : Z 1 0 <;> by_cases b : Z 0 1
    · exact absurd ⟨b, a⟩ hE'
    · have x := h20 fun y => hP' ⟨a, y⟩
      have y := h12 (mt s4 b)
      have z := h01 b
      exact ⟨y ∘ x, x ∘ z, z ∘ y⟩
    · exact ⟨h10 a, h21 (mt s2 a), h02 fun y => hM' ⟨b, y⟩⟩
    · exact ⟨h10 a, h21 (mt s2 a), h01 b ∘ h12 (mt s4 b)⟩
  obtain ⟨k1, k2, k3⟩ := key
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
  exact ⟨⟨id, k3 ∘ k2, k3⟩, ⟨k1, id, k1 ∘ k3⟩, k2 ∘ k1, k2, id⟩

theorem UpperTheory.V.Fr.types :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (K : Type) [Field K] (f : S.A →+* K), (MatIrr ⊤ (S.u.map f).r ↔ S.u.TI (RingHom.ker f)) ∧ (S.mB ≤ S.π (RingHom.ker f) → S.u.triP ≤ RingHom.ker f ∨ S.u.triM ≤ RingHom.ker f) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S K _ f
  obtain ⟨hco, hm⟩ := co_B hF hn S
  obtain ⟨hcone, hint⟩ := cone_u hF hn S
  have hle : ∀ Q : Fin n → Fin n → Prop,
      Ideal.span {x | ∃ g i j, Q i j ∧ x = S.u.r g i j} ≤ RingHom.ker f ↔
        ∀ i j, Q i j → ∀ g, (S.u.map f).r g i j = 0 := fun Q =>
    ⟨fun h i j hq g => h (Ideal.subset_span ⟨g, i, j, hq, rfl⟩), fun h => Ideal.span_le.2 (by
      rintro x ⟨g, i, j, hq, rfl⟩
      exact h i j hq g)⟩
  have hP := hle fun i j => j < i
  have hM := hle fun i j => i < j
  have hE := hle fun i j => Odd (w n i - w n j)
  refine ⟨⟨fun h => ⟨⟨fun h' => ?_, fun h' => ?_⟩, fun h3 h' => ?_⟩, fun h => ?_⟩, fun h => ?_⟩
  · have h2 : 1 < n := by omega
    refine irr_coord h ⟨0, by omega⟩ ⟨1, h2⟩ (by simp) fun g i hi => hP.1 h' _ _ ?_ g
    have : (i : ℕ) ≠ 0 := fun e => hi (Fin.ext e)
    exact Fin.lt_def.2 (by show 0 < (i : ℕ); omega)
  · have h2 : 1 < n := by omega
    refine irr_coord h ⟨n - 1, by omega⟩ ⟨0, by omega⟩ (by simp; omega) fun g i hi => hM.1 h' _ _ ?_ g
    have : (i : ℕ) ≠ n - 1 := fun e => hi (Fin.ext e)
    have := i.2
    exact Fin.lt_def.2 (by show (i : ℕ) < n - 1; omega)
  · subst h3
    refine irr_coord h 1 0 (by decide) fun g i hi => hE.1 h' _ _ ?_ g
    revert i
    decide
  · refine irr_of_conn (fun W hW i => ?_) ?_
    · have hspan : ∀ M ∈ Submodule.span S.B (Set.range S.u.r), ∀ v ∈ W, M.map f *ᵥ v ∈ W := by
        intro M hM
        induction hM using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨g, rfl⟩ := hx
          exact hW g
        | zero =>
          intro v _
          rw [Matrix.map_zero _ (map_zero f)]
          simp
        | add x y _ _ hx hy =>
          intro v hv
          convert W.add_mem (hx v hv) (hy v hv) using 1
          rw [← Matrix.add_mulVec]
          congr 1
          ext i j
          exact map_add f _ _
        | smul c x _ hx =>
          intro v hv
          convert W.smul_mem (f (algebraMap S.B S.A c)) (hx v hv) using 1
          rw [← Matrix.smul_mulVec]
          congr 1
          ext i j
          exact map_mul f (algebraMap S.B S.A c) _
      intro v hv
      convert hspan _ (idem hF hn S.B S.A S.u hint i) v hv using 2
      ext a b
      simp only [Matrix.single, Matrix.map_apply, Matrix.of_apply]
      split_ifs <;> simp
    · obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rcases hn with rfl | rfl
      · exact conn2 (fun i j => ∀ g, (S.u.map f).r g i j = 0) (mt hP.2 h1) (mt hM.2 h2)
      · refine conn3 (fun i j => ∀ g, (S.u.map f).r g i j = 0) (fun i j hz g => ?_) (mt hP.2 h1) (mt hM.2 h2)
          (mt hE.2 (h3 rfl))
        have := hz (F.star g)
        rwa [(S.u.map f).pol, jtj] at this
  · by_contra hc
    obtain ⟨h1, h2⟩ := not_or.1 hc
    have h1' := mt hP.2 h1
    have h2' := mt hM.2 h2
    push Not at h1' h2'
    obtain ⟨i, j, hij, g, hg⟩ := h1'
    obtain ⟨i', j', hij', g', hg'⟩ := h2'
    obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (sub_pos.2 (w_lt hij)).le
    obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (sub_pos.2 (w_lt hij')).le
    have hq0 : q ≠ 0 := by
      have := w_lt hij'
      omega
    obtain ⟨c, hc1, hc2⟩ := hcone.cyc (List.replicate q (g, i, j) ++ List.replicate p (g', i', j'))
      (by
        simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate, nsmul_eq_mul]
        rw [hq, ← neg_sub, hp]
        ring)
      ⟨(g, i, j), List.mem_append_left _ (List.mem_replicate.2 ⟨hq0, rfl⟩), hij.ne'⟩
    rw [hm] at hc1
    have h0 : f (algebraMap S.B S.A c) = 0 := h hc1
    rw [hc2] at h0
    simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, map_mul, map_pow] at h0
    exact mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hg') h0
