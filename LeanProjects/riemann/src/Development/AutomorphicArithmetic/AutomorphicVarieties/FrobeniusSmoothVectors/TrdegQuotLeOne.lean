import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem alg_of_rel {R D : Type} [CommRing R] [CommRing D] [IsDomain D] [Algebra R D]
    (T : Subalgebra R D) {x c d : D} {p : ℕ} (hp : 0 < p) (hc : c ∈ T) (hd : d ∈ T) (h0 : c ≠ 0)
    (h : x ^ p * c = d) : IsAlgebraic T x := by
  refine IsAlgebraic.of_pow hp ?_
  have hc' : (⟨c, hc⟩ : T) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  refine IsAlgebraic.of_smul (y := (⟨c, hc⟩ : T)) (mem_nonZeroDivisors_of_ne_zero hc') ?_
  have : (⟨c, hc⟩ : T) • x ^ p = algebraMap T D ⟨d, hd⟩ := by
    rw [Algebra.smul_def, mul_comm]; exact h
  rw [this]
  exact isAlgebraic_algebraMap _

private theorem trdeg_le_one {R D ι : Type} [CommRing R] [CommRing D] [IsDomain D] [Algebra R D]
    [FaithfulSMul R D] (x : ι → D) (wt : ι → ℤ) (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (h0 : ∀ (i j : ι) (p q : ℕ), p * wt i + q * wt j = 0 → x i ^ p * x j ^ q ∈ Set.range (algebraMap R D))
    {a b : ι} (ha : 0 < wt a) (hb : wt b < 0) (ha0 : x a ≠ 0) (hb0 : x b ≠ 0) : Algebra.trdeg R D ≤ 1 := by
  set T : Subalgebra R D := Algebra.adjoin R {x a} with hT
  have haT : x a ∈ T := Algebra.subset_adjoin rfl
  have hR : ∀ {y}, y ∈ Set.range (algebraMap R D) → y ∈ T := by
    rintro _ ⟨r, rfl⟩; exact T.algebraMap_mem r
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hb.le)
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hq' : wt b = -q := by omega
  have key : ∀ i, IsAlgebraic T (x i) := by
    intro i
    rcases le_total (wt i) 0 with h | h
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h)
      have hm' : wt i = -m := by omega
      exact alg_of_rel T hp0 (pow_mem haT m) (hR (h0 i a p m (by rw [hm', hp]; ring))) (pow_ne_zero _ ha0) rfl
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h
      have h1 := hR (h0 i b q m (by rw [hm, hq']; ring))
      have h2 := hR (h0 b a p q (by rw [hp, hq']; ring))
      refine alg_of_rel T (mul_pos hq0 hp0) (pow_mem h2 m) (mul_mem (pow_mem h1 p) (pow_mem haT (q * m)))
        (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ ha0))) (by ring)
  have hall : Algebra.IsAlgebraic T D := ⟨fun y => by
    have hy : y ∈ Algebra.adjoin R (Set.range x) := hgen ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact key i
    | algebraMap r => exact isAlgebraic_algebraMap (⟨_, T.algebraMap_mem r⟩ : T)
    | add y z _ _ h1 h2 => exact h1.add h2
    | mul y z _ _ h1 h2 => exact h1.mul h2⟩
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk R ({x a} : Set D)

private theorem trdeg_quot_le_one {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (η : Ideal A) (hη : η.IsPrime) (x : ι → A) (wt : ι → ℤ) (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (h0 : ∀ (i j : ι) (p q : ℕ), p * wt i + q * wt j = 0 → x i ^ p * x j ^ q ∈ Set.range (algebraMap R A))
    {a b : ι} (ha : 0 < wt a) (hb : wt b < 0) (ha0 : x a ∉ η) (hb0 : x b ∉ η) :
    Algebra.trdeg (R ⧸ η.comap (algebraMap R A)) (A ⧸ η) ≤ 1 := by
  refine trdeg_le_one (fun s => Ideal.Quotient.mk η (x s)) wt ?_ ?_ ha hb
    (fun e => ha0 (Ideal.Quotient.eq_zero_iff_mem.1 e)) (fun e => hb0 (Ideal.Quotient.eq_zero_iff_mem.1 e))
  · rw [eq_top_iff]
    intro y hy
    clear hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hy : y ∈ Algebra.adjoin R (Set.range x) := hgen ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (Ideal.Quotient.mk (η.comap (algebraMap R A)) r)
    | add y z _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | mul y z _ _ h1 h2 => rw [map_mul]; exact mul_mem h1 h2
  · intro i j p q h
    obtain ⟨r, hr⟩ := h0 i j p q h
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [← map_pow, ← map_pow, ← map_mul, ← hr]
    rfl

private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

theorem UpperTheory.V.Fr.fibre :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η : Ideal S.A, η.IsPrime → S.u.OffTri η → S.td η ≤ 1 := by
  intro l _ O _ _ _ _ F C₀ n _ _ S η hη hoff
  obtain ⟨h1, h2⟩ := hoff
  have hb : ∃ g i j, j < i ∧ S.u.r g i j ∉ η := by
    by_contra h
    push Not at h
    exact h1 (Ideal.span_le.2 (by rintro _ ⟨g, i, j, hij, rfl⟩; exact h g i j hij))
  have ha : ∃ g i j, i < j ∧ S.u.r g i j ∉ η := by
    by_contra h
    push Not at h
    exact h2 (Ideal.span_le.2 (by rintro _ ⟨g, i, j, hij, rfl⟩; exact h g i j hij))
  obtain ⟨g, i, j, hij, hg⟩ := ha
  obtain ⟨g', i', j', hij', hg'⟩ := hb
  refine trdeg_quot_le_one (ι := F.G0 × Fin n × Fin n) η hη (fun s => S.u.r s.1 s.2.1 s.2.2)
    (fun s => w n s.2.1 - w n s.2.2) ?_ ?_ (a := (g, i, j)) (b := (g', i', j'))
    (sub_pos.2 (w_lt hij)) (sub_neg.2 (w_lt hij')) hg hg'
  · rw [eq_top_iff]
    rintro ⟨y, hy⟩ hy'
    clear hy'
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · exact Subalgebra.algebraMap_mem _ (⟨y, hy⟩ : S.B)
      · exact Algebra.subset_adjoin ⟨(g, i, j), rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (algebraMap O S.B r)
    | add y z hy hz h1 h2 => exact add_mem h1 h2
    | mul y z hy hz h1 h2 => exact mul_mem h1 h2
  · intro s t p q h
    have hm : S.ρ.r s.1 s.2.1 s.2.2 ^ p * S.ρ.r t.1 t.2.1 t.2.2 ^ q ∈ S.ρ.mon 0 :=
      ⟨List.replicate p s ++ List.replicate q t, by simpa using h, by simp⟩
    exact ⟨⟨_, S.mon_mem hm⟩, rfl⟩
