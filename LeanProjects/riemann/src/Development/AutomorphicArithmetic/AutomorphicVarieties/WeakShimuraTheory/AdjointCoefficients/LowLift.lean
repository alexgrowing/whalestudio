import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

variable {A R : Type} [CommRing A] [CommRing R]

private def lowOf (a b c d : A) : M4 A := !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d, b - a * c, -a, 1]

private theorem lowOf_low (a b c d : A) : IsLow (lowOf a b c d) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsGSp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj, lowOf, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply] <;> ring
  · intro i
    fin_cases i <;> simp [lowOf]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [lowOf] <;> omega

private theorem eq_lowOf {n : M4 A} (h : IsLow n) : n = lowOf (n 1 0) (n 2 0) (n 2 1) (n 3 0) := by
  obtain ⟨hg, hd, hu⟩ := h
  have h01 := hu 0 1 (by decide); have h02 := hu 0 2 (by decide); have h03 := hu 0 3 (by decide)
  have h12 := hu 1 2 (by decide); have h13 := hu 1 3 (by decide); have h23 := hu 2 3 (by decide)
  have d0 := hd 0; have d1 := hd 1; have d2 := hd 2; have d3 := hd 3
  have e1 := congrFun (congrFun hg 1) 0
  have e4 := congrFun (congrFun hg 3) 1
  simp [adj, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply, h01, h02, h03, h12, h13,
    h23, d0, d1, d2, d3] at e1 e4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowOf, h01, h02, h03, h12, h13, h23, d0, d1, d2, d3]
  · linear_combination e4
  · linear_combination e1

private theorem low_mul {m n : M4 A} (hm : IsLow m) (hn : IsLow n) : IsLow (m * n) := by
  refine ⟨by simpa using (grp A).2.2.2.2.2.2.2.1 1 1 m n hm.1 hn.1, ?_, ?_⟩
  · intro i
    rw [eq_lowOf hm, eq_lowOf hn]
    fin_cases i <;> simp [lowOf, Matrix.mul_apply, Fin.sum_univ_four]
  · intro i j hij
    rw [eq_lowOf hm, eq_lowOf hn]
    fin_cases i <;> fin_cases j <;> simp_all [lowOf, Matrix.mul_apply, Fin.sum_univ_four] <;> omega

private theorem up_adj {b : M4 A} (h : IsUp b) : IsUp (adj b) := by
  intro i j hij
  rw [adj_apply, h j.rev i.rev (by simpa [Fin.lt_def, Fin.val_rev] using (by omega : (3 : ℕ) - i.val < 3 - j.val)), smul_zero]

private theorem aux (p : A →+* R) (hp : ∀ x y, p x = 0 → p y = 0 → x * y = 0) (n' : M4 A) (hn : IsGSp 1 n')
    (hl : IsLow (n'.map p)) :
    ∃ m b : M4 A, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧ m.map p = n'.map p ∧ m = n' * b := by
  obtain ⟨-, -, hadd, hsmul, hone, hmap, -, hgsp, -⟩ := grp A
  have kz : ∀ X Z : M4 A, X.map p = 0 → Z.map p = 0 → X * Z = 0 := by
    intro X Z hX hZ
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ =>
      hp _ _ (by simpa using congrFun (congrFun hX i) k) (by simpa using congrFun (congrFun hZ k) j)
  have adj0 : adj (0 : M4 A) = 0 := by simpa using hsmul 0 (0 : M4 A)
  have adjneg : ∀ X : M4 A, adj (-X) = -adj X := by
    intro X
    simpa using hsmul (-1) X
  have madj : ∀ X : M4 A, X.map p = 0 → (adj X).map p = 0 := by
    intro X hX
    rw [← hmap R p X, hX]
    simpa using (grp R).2.2.2.1 (0 : R) (0 : M4 R)
  set m0 := lowOf (n' 1 0) (n' 2 0) (n' 2 1) (n' 3 0) with hm0d
  have hm0 : IsLow m0 := lowOf_low _ _ _ _
  have hm0l : adj m0 * m0 = 1 := by simpa [IsGSp] using hm0.1
  have hm0r : m0 * adj m0 = 1 := mul_eq_one_comm.mp hm0l
  have hmap0 : m0.map p = n'.map p := by
    rw [eq_lowOf hl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm0d, lowOf]
  have hN : adj (n'.map p) * n'.map p = 1 := by simpa [IsGSp] using hl.1
  set Y := adj m0 * n' - 1 with hYd
  have hY : Y.map p = 0 := by
    show p.mapMatrix Y = 0
    rw [hYd, map_sub, map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hmap R p m0,
      hmap0, hN, sub_self]
  have h1Y : adj m0 * n' = 1 + Y := by rw [hYd]; abel
  have ha : IsGSp 1 (adj m0) := by
    show adj (adj m0) * adj m0 = (1 : A) • 1
    rw [(grp A).2.1, hm0r, one_smul]
  have hadjY : adj Y + Y = 0 := by
    have g : IsGSp 1 (adj m0 * n') := by simpa using hgsp 1 1 _ _ ha hn
    have g' : adj (1 + Y) * (1 + Y) = 1 := by simpa [IsGSp, h1Y] using g
    rw [hadd, hone] at g'
    have e : (1 + adj Y) * (1 + Y) = 1 + (adj Y + Y) + adj Y * Y := by noncomm_ring
    rw [e, kz _ _ (madj Y hY) hY, add_zero] at g'
    simpa using g'
  set Yu : M4 A := Matrix.of fun i j => if i ≤ j then Y i j else 0 with hYud
  have hYu : Yu.map p = 0 := by
    ext i j
    have := congrFun (congrFun hY i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [hYud, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
    split_ifs <;> simp [this]
  have hadjYu : adj Yu + Yu = 0 := by
    ext i j
    have h := congrFun (congrFun hadjY i) j
    simp only [Matrix.add_apply, adj_apply, Matrix.zero_apply] at h
    simp only [Matrix.add_apply, adj_apply, Matrix.zero_apply, hYud, Matrix.of_apply, Fin.rev_le_rev]
    split_ifs <;> simp_all
  set b : M4 A := 1 - Yu with hbd
  have hbup : IsUp b := by
    intro i j hij
    simp [hbd, hYud, Matrix.one_apply, hij.ne', not_le.mpr hij]
  have hbg : IsGSp 1 b := by
    show adj b * b = (1 : A) • 1
    have ea : adj b = 1 - adj Yu := by
      rw [hbd, sub_eq_add_neg, hadd, adjneg, hone, ← sub_eq_add_neg]
    rw [ea, one_smul]
    have e : (1 - adj Yu) * (1 - Yu) = 1 - (adj Yu + Yu) + adj Yu * Yu := by noncomm_ring
    rw [e, hadjYu, kz _ _ (madj Yu hYu) hYu]
    simp
  have hbmap : p.mapMatrix b = 1 := by
    rw [hbd, map_sub, map_one, RingHom.mapMatrix_apply, hYu, sub_zero]
  have e1 : adj m0 * n' * b = 1 + (Y - Yu) := by
    rw [h1Y, hbd]
    have e : (1 + Y) * (1 - Yu) = 1 + (Y - Yu) - Y * Yu := by noncomm_ring
    rw [e, kz _ _ hY hYu, sub_zero]
  have hlow : IsLow (adj m0 * n' * b) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hgsp _ _ _ _ (by simpa using hgsp 1 1 _ _ ha hn) hbg
    · intro i
      rw [e1]
      simp [hYud]
    · intro i j hij
      rw [e1]
      simp [hYud, Matrix.one_apply, hij.ne, hij.le]
  have hm := low_mul hm0 hlow
  have hmeq : m0 * (adj m0 * n' * b) = n' * b := by
    rw [← mul_assoc, ← mul_assoc, hm0r, one_mul]
  refine ⟨m0 * (adj m0 * n' * b), b, hm, hbg, hbup, up_adj hbup, ?_, hmeq⟩
  rw [hmeq]
  show p.mapMatrix (n' * b) = p.mapMatrix n'
  rw [map_mul, hbmap, mul_one]

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.lowLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ n' : M4 A, IsGSp 1 n' → IsLow (n'.map p) → ∃ m b : M4 A, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧ m.map p = n'.map p ∧ m = n' * b := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p _ hker n' hn hl
  have hle : RingHom.ker p ≤ maximalIdeal A := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    have h1 : (1 : A) ∈ RingHom.ker p := by rw [htop]; trivial
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  refine aux (p : A →+* R) (fun x y hx hy => ?_) n' hn hl
  have hm : x * y ∈ maximalIdeal A * RingHom.ker p :=
    Ideal.mul_mem_mul (hle (by simpa [RingHom.mem_ker] using hx)) (by simpa [RingHom.mem_ker] using hy)
  rw [hker] at hm
  simpa using hm
