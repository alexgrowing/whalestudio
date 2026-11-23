import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensityNumericalFacts

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

structure ColumnSpanNumericalFacts (K : Cst) (X : Dat) : Prop where
  arnn : 0 ≤ X.ar
  uann : 0 ≤ X.ar + X.ar / (X.k * X.Y)
  blnn : 0 ≤ X.bl
  bunn : 0 ≤ X.bu
  Y1 : 1 ≤ X.Y
  N1 : 1 ≤ X.N₁
  Npos : 1 ≤ X.N
  wpos : 0 < (X.Wa 0).card ∧ 0 < (X.Wb 0).card
  below : ((X.Wa 0).card : ℝ) ^ X.N * ((X.Wb 0).card : ℝ) ^ X.N -
      ((Finset.Icc (X.a + X.ccl) X.ua).card : ℝ) ^ X.N * ((Finset.Icc (X.lb + X.ccl) X.ub).card : ℝ) ^ X.N ≤
    1 / X.Y * (((X.Wa 0).card : ℝ) ^ X.N * ((X.Wb 0).card : ℝ) ^ X.N)
  eps : 12 * (X.N : ℝ) * X.k * X.ccl / X.b' ≤ 1 / X.Y

theorem sum_pi_cast {ι : Type} [Fintype ι] [DecidableEq ι] (lo hi : ℕ) (g : (ι → ℤ) → ℝ) :
    ∑ aa ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (lo : ℤ) (hi : ℤ)), g aa =
      ∑ A ∈ Fintype.piFinset (fun _ : ι => Finset.Icc lo hi), g (fun s => (A s : ℤ)) := by
  refine Finset.sum_nbij' (fun aa s => (aa s).toNat) (fun A s => (A s : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro aa haa
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc] at haa ⊢
    intro s
    have := haa s
    omega
  · intro A hA
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc] at hA ⊢
    intro s
    have := hA s
    omega
  · intro aa haa
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc] at haa
    funext s
    have := haa s
    show ((aa s).toNat : ℤ) = aa s
    omega
  · intro A _
    funext s
    show ((A s : ℤ)).toNat = A s
    omega
  · intro aa haa
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc] at haa
    congr 1
    funext s
    have := haa s
    show aa s = ((aa s).toNat : ℤ)
    omega

theorem card_Icc_cast (lo hi : ℕ) : (Finset.Icc (lo : ℤ) (hi : ℤ)).card = (Finset.Icc lo hi).card := by
  rw [Int.card_Icc, Nat.card_Icc]
  omega

theorem ceil_cast {x : ℝ} (hx : 0 ≤ x) : ((⌈x⌉₊ : ℕ) : ℤ) = ⌈x⌉ := by
  rw [← Int.ceil_toNat, Int.toNat_of_nonneg (Int.ceil_nonneg hx)]

theorem floor_cast {x : ℝ} (hx : 0 ≤ x) : ((⌊x⌋₊ : ℕ) : ℤ) = ⌊x⌋ := by
  rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx)]

open Classical in

theorem kText_cast (K : Cst) (X : Dat) (R : RS X.p X.n') (hbl : 0 ≤ X.bl) (A B : X.TT → ℕ) :
    X.kText K R (fun s => (A s : ℤ)) (fun s => (B s : ℤ)) =
      (if (∀ s, X.a + X.ccl ≤ A s ∧ X.lb + X.ccl ≤ B s) then
        X.kF K R (fun s => A s - X.ccl) (fun s => B s - X.ccl) else 1) +
      2 * X.kF K R (fun s => A s + X.ccl) (fun s => B s + X.ccl) + 12 * X.N * X.k * X.ccl / X.b' := by
  have hIn : X.Inside (fun s => (A s : ℤ)) (fun s => (B s : ℤ)) ↔
      ∀ s, X.a + X.ccl ≤ A s ∧ X.lb + X.ccl ≤ B s := by
    unfold Dat.Inside Dat.lb
    refine forall_congr' fun s => and_congr ?_ ?_
    · dsimp only
      omega
    · dsimp only
      rw [← Int.ceil_le, ← ceil_cast hbl]
      omega
  have h1 : (fun s => ((A s : ℤ) - (X.ccl : ℤ)).toNat) = (fun s => A s - X.ccl) := by
    funext s; omega
  have h2 : (fun s => ((B s : ℤ) - (X.ccl : ℤ)).toNat) = (fun s => B s - X.ccl) := by
    funext s; omega
  have h3 : (fun s => ((A s : ℤ) + (X.ccl : ℤ)).toNat) = (fun s => A s + X.ccl) := by
    funext s; omega
  have h4 : (fun s => ((B s : ℤ) + (X.ccl : ℤ)).toNat) = (fun s => B s + X.ccl) := by
    funext s; omega
  simp only [Dat.kText]
  by_cases hc : ∀ s, X.a + X.ccl ≤ A s ∧ X.lb + X.ccl ≤ B s
  · rw [if_pos (hIn.mpr hc), if_pos hc, h1, h2, h3, h4]
  · rw [if_neg (mt hIn.mp hc), if_neg hc, h3, h4]

theorem sum_of_meanN {ι : Type} [Fintype ι] [DecidableEq ι] (Sa Sb : Finset ℕ) (f : (ι → ℕ) → (ι → ℕ) → ℝ) (M : ℝ)
    (ha : 0 < Sa.card) (hb : 0 < Sb.card) (h : meanN Sa Sb f ≤ M) :
    ∑ A ∈ Fintype.piFinset (fun _ : ι => Sa), ∑ B ∈ Fintype.piFinset (fun _ : ι => Sb), f A B ≤
      M * ((Sa.card : ℝ) ^ Fintype.card ι * (Sb.card : ℝ) ^ Fintype.card ι) := by
  have hD : (0 : ℝ) < (Sa.card : ℝ) ^ Fintype.card ι * (Sb.card : ℝ) ^ Fintype.card ι :=
    mul_pos (pow_pos (by exact_mod_cast ha) _) (pow_pos (by exact_mod_cast hb) _)
  unfold meanN at h
  rwa [div_le_iff₀ hD] at h

open Classical in

theorem sum_first {ι : Type} [Fintype ι] [DecidableEq ι] (a ua lb ub c : ℕ) (kf : (ι → ℕ) → (ι → ℕ) → ℝ)
    (hkf : ∀ A B, 0 ≤ kf A B) :
    ∑ A ∈ Fintype.piFinset (fun _ : ι => Finset.Icc a ua), ∑ B ∈ Fintype.piFinset (fun _ : ι => Finset.Icc lb ub),
        (if (∀ s, a + c ≤ A s ∧ lb + c ≤ B s) then kf (fun s => A s - c) (fun s => B s - c) else 1) ≤
      (∑ A ∈ Fintype.piFinset (fun _ : ι => Finset.Icc a ua),
        ∑ B ∈ Fintype.piFinset (fun _ : ι => Finset.Icc lb ub), kf A B) +
      (((Finset.Icc a ua).card : ℝ) ^ Fintype.card ι * ((Finset.Icc lb ub).card : ℝ) ^ Fintype.card ι -
        ((Finset.Icc (a + c) ua).card : ℝ) ^ Fintype.card ι * ((Finset.Icc (lb + c) ub).card : ℝ) ^ Fintype.card ι) := by
  have sub_le : ∀ (lo hi : ℕ) (g : (ι → ℕ) → ℝ), (∀ A, 0 ≤ g A) →
      ∑ A ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (lo + c) hi), g (fun s => A s - c) ≤
        ∑ A ∈ Fintype.piFinset (fun _ : ι => Finset.Icc lo hi), g A := by
    intro lo hi g hg
    have hinj : ∀ x ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (lo + c) hi),
        ∀ y ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (lo + c) hi),
          (fun s => x s - c) = (fun s => y s - c) → x = y := by
      intro x hx y hy hxy
      rw [Fintype.mem_piFinset] at hx hy
      funext s
      have h1 : x s - c = y s - c := congrFun hxy s
      have h2 := Finset.mem_Icc.mp (hx s)
      have h3 := Finset.mem_Icc.mp (hy s)
      omega
    rw [← Finset.sum_image hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro B hB
      rw [Finset.mem_image] at hB
      obtain ⟨A, hA, rfl⟩ := hB
      rw [Fintype.mem_piFinset] at hA ⊢
      intro s
      have := Finset.mem_Icc.mp (hA s)
      show A s - c ∈ Finset.Icc lo hi
      rw [Finset.mem_Icc]
      omega
    · intro A _ _
      exact hg A
  set pa := Fintype.piFinset (fun _ : ι => Finset.Icc a ua) with hpa
  set pb := Fintype.piFinset (fun _ : ι => Finset.Icc lb ub) with hpb
  set qa := Fintype.piFinset (fun _ : ι => Finset.Icc (a + c) ua) with hqa
  set qb := Fintype.piFinset (fun _ : ι => Finset.Icc (lb + c) ub) with hqb
  rw [← Finset.sum_product' (f := fun (A B : ι → ℕ) =>
    (if (∀ s, a + c ≤ A s ∧ lb + c ≤ B s) then kf (fun s => A s - c) (fun s => B s - c) else (1 : ℝ)))]
  rw [Finset.sum_ite]
  have hF : (pa ×ˢ pb).filter (fun x : (ι → ℕ) × (ι → ℕ) => ∀ s, a + c ≤ x.1 s ∧ lb + c ≤ x.2 s) = qa ×ˢ qb := by
    ext ⟨A, B⟩
    simp only [hpa, hpb, hqa, hqb, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hA, hB⟩, hP⟩
      exact ⟨fun s => ⟨(hP s).1, (hA s).2⟩, fun s => ⟨(hP s).2, (hB s).2⟩⟩
    · rintro ⟨hA, hB⟩
      refine ⟨⟨fun s => ⟨?_, (hA s).2⟩, fun s => ⟨?_, (hB s).2⟩⟩, fun s => ⟨(hA s).1, (hB s).1⟩⟩
      · have := hA s; omega
      · have := hB s; omega
  have hcard : ((pa ×ˢ pb).filter (fun x : (ι → ℕ) × (ι → ℕ) => ∀ s, a + c ≤ x.1 s ∧ lb + c ≤ x.2 s)).card +
      ((pa ×ˢ pb).filter (fun x : (ι → ℕ) × (ι → ℕ) => ¬ ∀ s, a + c ≤ x.1 s ∧ lb + c ≤ x.2 s)).card =
        (pa ×ˢ pb).card := by
    first
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | exact Finset.card_filter_add_card_filter_not _
    | (rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
        Finset.filter_union_filter_neg_eq])
    | (rw [← Finset.card_disjoint_union (Finset.disjoint_filter_filter_neg _ _ _),
        Finset.filter_union_filter_neg_eq])
  rw [hF] at hcard ⊢
  have hcS : (pa ×ˢ pb).card = (Finset.Icc a ua).card ^ Fintype.card ι * (Finset.Icc lb ub).card ^ Fintype.card ι := by
    rw [Finset.card_product, hpa, hpb, Fintype.card_piFinset, Fintype.card_piFinset, Finset.prod_const,
      Finset.prod_const, Finset.card_univ]
  have hcQ : (qa ×ˢ qb).card = (Finset.Icc (a + c) ua).card ^ Fintype.card ι * (Finset.Icc (lb + c) ub).card ^ Fintype.card ι := by
    rw [Finset.card_product, hqa, hqb, Fintype.card_piFinset, Fintype.card_piFinset, Finset.prod_const,
      Finset.prod_const, Finset.card_univ]
  have hneg : ((((pa ×ˢ pb).filter (fun x : (ι → ℕ) × (ι → ℕ) => ¬ ∀ s, a + c ≤ x.1 s ∧ lb + c ≤ x.2 s)).card : ℕ) : ℝ) =
      ((Finset.Icc a ua).card : ℝ) ^ Fintype.card ι * ((Finset.Icc lb ub).card : ℝ) ^ Fintype.card ι -
        ((Finset.Icc (a + c) ua).card : ℝ) ^ Fintype.card ι * ((Finset.Icc (lb + c) ub).card : ℝ) ^ Fintype.card ι := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcard
    simp only [Nat.cast_add, hcS, hcQ, Nat.cast_mul, Nat.cast_pow] at h
    linarith
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hneg, Finset.sum_product]
  gcongr
  calc ∑ A ∈ qa, ∑ B ∈ qb, kf (fun s => A s - c) (fun s => B s - c)
      ≤ ∑ A ∈ qa, ∑ B ∈ pb, kf (fun s => A s - c) B := by
        apply Finset.sum_le_sum
        intro A _
        exact sub_le lb ub (fun B => kf (fun s => A s - c) B) (fun B => hkf _ _)
    _ ≤ ∑ A ∈ pa, ∑ B ∈ pb, kf A B :=
        sub_le a ua (fun A => ∑ B ∈ pb, kf A B)
          (fun A => Finset.sum_nonneg fun B _ => hkf A B)

private theorem sum_piFinset_Icc_shift_eq {ι : Type} [Fintype ι] [DecidableEq ι] (lo hi c : ℕ) (g : (ι → ℕ) → ℝ) :
    ∑ A ∈ Fintype.piFinset (fun _ : ι => Finset.Icc lo hi), g (fun s => A s + c) =
      ∑ A ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (lo + c) (hi + c)), g A := by
  refine Finset.sum_nbij' (fun A s => A s + c) (fun A s => A s - c) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc] at hA ⊢
    intro s
    have := hA s
    omega
  · intro A hA
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc] at hA ⊢
    intro s
    have := hA s
    omega
  · intro A _
    funext s
    show A s + c - c = A s
    omega
  · intro A hA
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc] at hA
    funext s
    have := hA s
    show A s - c + c = A s
    omega
  · intro A _
    rfl

theorem mean_of (K : Cst) (hKp : K.Pos) (X : Dat) (hF : ColumnSpanNumericalFacts K X) (R : RS X.p X.n') (h0 : Avg K X R 0)
    (hc : Avg K X R X.ccl) (hx : MeanX K X R) :
    meanKap X.TT X.m X.Y X.ar X.bl X.bu (X.kText K R) ≤ K.Cmean * X.TT.card * X.N₁ / X.Y := by
  classical
  obtain ⟨arnn, uann, blnn, bunn, Y1, N1, Npos, wpos, below, eps⟩ := hF
  have hu : 0 ≤ X.ar + X.ar / (((X.m : ℝ) + 1) * X.Y) := by simpa [Dat.k] using uann
  have hIa : Formalism.MainNotions.flipOneThree.IaZ X.m X.Y X.ar = Finset.Icc ((X.a : ℕ) : ℤ) ((X.ua : ℕ) : ℤ) := by
    unfold Formalism.MainNotions.flipOneThree.IaZ Dat.a Dat.ua Dat.k
    rw [ceil_cast arnn, floor_cast hu]
  have hIb : Formalism.MainNotions.flipOneThree.IbZ X.bl X.bu = Finset.Icc ((X.lb : ℕ) : ℤ) ((X.ub : ℕ) : ℤ) := by
    unfold Formalism.MainNotions.flipOneThree.IbZ Dat.lb Dat.ub
    rw [ceil_cast blnn, floor_cast bunn]
  have hWa0 : X.Wa 0 = Finset.Icc X.a X.ua := by simp [Dat.Wa]
  have hWb0 : X.Wb 0 = Finset.Icc X.lb X.ub := by simp [Dat.Wb]
  have hcA : (X.Wa X.ccl).card = (Finset.Icc X.a X.ua).card := by
    simp only [Dat.Wa, Nat.card_Icc]; omega
  have hcB : (X.Wb X.ccl).card = (Finset.Icc X.lb X.ub).card := by
    simp only [Dat.Wb, Nat.card_Icc]; omega
  have hN : Fintype.card X.TT = X.N := by simp [Dat.N]
  have hNN : X.TT.card = X.N := rfl
  have hkf : ∀ A B, 0 ≤ X.kF K R A B := by
    intro A B
    unfold Dat.kF
    exact Real.sInf_nonneg fun x hx => hx.1
  have Ypos : (0 : ℝ) < X.Y := by linarith
  unfold Avg at h0 hc
  unfold MeanX at hx
  rw [hWa0, hWb0] at wpos below h0
  have hT : (0 : ℝ) < ((Finset.Icc X.a X.ua).card : ℝ) ^ X.N * ((Finset.Icc X.lb X.ub).card : ℝ) ^ X.N :=
    mul_pos (pow_pos (by exact_mod_cast wpos.1) _) (pow_pos (by exact_mod_cast wpos.2) _)
  have s0 := sum_of_meanN _ _ (X.kF K R) _ wpos.1 wpos.2 h0
  have sc := sum_of_meanN _ _ (X.kF K R) _ (by rw [hcA]; exact wpos.1) (by rw [hcB]; exact wpos.2) hc
  have s1 := sum_first X.a X.ua X.lb X.ub X.ccl (X.kF K R) hkf
  rw [hN] at s0 sc s1
  rw [hcA, hcB] at sc
  have hsh : (∑ A ∈ Fintype.piFinset (fun _ : X.TT => Finset.Icc X.a X.ua),
      ∑ B ∈ Fintype.piFinset (fun _ : X.TT => Finset.Icc X.lb X.ub),
        X.kF K R (fun s => A s + X.ccl) (fun s => B s + X.ccl)) =
      ∑ A ∈ Fintype.piFinset (fun _ : X.TT => X.Wa X.ccl),
        ∑ B ∈ Fintype.piFinset (fun _ : X.TT => X.Wb X.ccl), X.kF K R A B := by
    unfold Dat.Wa Dat.Wb
    rw [← sum_piFinset_Icc_shift_eq X.a X.ua X.ccl (fun A => ∑ B ∈ Fintype.piFinset
      (fun _ : X.TT => Finset.Icc (X.lb + X.ccl) (X.ub + X.ccl)), X.kF K R A B)]
    refine Finset.sum_congr rfl fun A _ => ?_
    exact sum_piFinset_Icc_shift_eq X.lb X.ub X.ccl (fun B => X.kF K R (fun s => A s + X.ccl) B)
  rw [← hsh] at sc
  have hS : (∑ aa ∈ Fintype.piFinset (fun _ : X.TT => Formalism.MainNotions.flipOneThree.IaZ X.m X.Y X.ar),
      ∑ bb ∈ Fintype.piFinset (fun _ : X.TT => Formalism.MainNotions.flipOneThree.IbZ X.bl X.bu), X.kText K R aa bb) =
      ∑ A ∈ Fintype.piFinset (fun _ : X.TT => Finset.Icc X.a X.ua),
        ∑ B ∈ Fintype.piFinset (fun _ : X.TT => Finset.Icc X.lb X.ub),
          ((if (∀ s, X.a + X.ccl ≤ A s ∧ X.lb + X.ccl ≤ B s) then
            X.kF K R (fun s => A s - X.ccl) (fun s => B s - X.ccl) else 1) +
          2 * X.kF K R (fun s => A s + X.ccl) (fun s => B s + X.ccl) +
            12 * X.N * X.k * X.ccl / X.b') := by
    rw [hIa, hIb, sum_pi_cast]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [sum_pi_cast]
    refine Finset.sum_congr rfl fun B _ => ?_
    exact kText_cast K X R blnn A B
  unfold Formalism.MainNotions.flipOneThree.meanKap
  rw [hS, hIa, hIb, card_Icc_cast, card_Icc_cast, hNN, div_le_iff₀ hT]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hN, Nat.cast_pow]
  have p1 := mul_le_mul_of_nonneg_left eps hT.le
  have p2 := mul_le_mul_of_nonneg_left hx hT.le
  have hN1 : (1 : ℝ) ≤ (X.N : ℝ) * (X.N₁ : ℝ) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast Npos) (by exact_mod_cast N1)
  have p3 : 2 / X.Y ≤ 8 * (X.N : ℝ) * X.N₁ / X.Y := by
    apply div_le_div_of_nonneg_right _ Ypos.le
    nlinarith
  have p4 := mul_le_mul_of_nonneg_left p3 hT.le
  unfold Cst.Cmean
  have e1 : ((Finset.Icc X.a X.ua).card : ℝ) ^ X.N * ((Finset.Icc X.lb X.ub).card : ℝ) ^ X.N * (1 / X.Y) +
      ((Finset.Icc X.a X.ua).card : ℝ) ^ X.N * ((Finset.Icc X.lb X.ub).card : ℝ) ^ X.N * (1 / X.Y) =
      ((Finset.Icc X.a X.ua).card : ℝ) ^ X.N * ((Finset.Icc X.lb X.ub).card : ℝ) ^ X.N * (2 / X.Y) := by ring
  have e2 : (6 * (K.CA + K.Cs) + 8) * (X.N : ℝ) * X.N₁ / X.Y *
      (((Finset.Icc X.a X.ua).card : ℝ) ^ X.N * ((Finset.Icc X.lb X.ub).card : ℝ) ^ X.N) =
      6 * (((Finset.Icc X.a X.ua).card : ℝ) ^ X.N * ((Finset.Icc X.lb X.ub).card : ℝ) ^ X.N *
        ((K.CA + K.Cs) * X.N * X.N₁ / X.Y)) +
      ((Finset.Icc X.a X.ua).card : ℝ) ^ X.N * ((Finset.Icc X.lb X.ub).card : ℝ) ^ X.N *
        (8 * (X.N : ℝ) * X.N₁ / X.Y) := by ring
  rw [e2]
  nlinarith [s0, s1, sc, below, p1, p2, p4, e1]

end Formalism.MainNotions.flipOneThree.Pf

end
