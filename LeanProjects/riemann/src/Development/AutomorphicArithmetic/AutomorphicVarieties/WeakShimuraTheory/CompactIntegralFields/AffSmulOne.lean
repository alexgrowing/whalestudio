import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section

variable {R : Type} [CommRing R]

private noncomputable def aff (x y : M4 R) : M4 R[X] := Matrix.of fun i j => (1 - X) * C (x i j) + X * C (y i j)

private theorem aff_apply (x y : M4 R) (i j : Fin 4) : aff x y i j = (1 - X) * C (x i j) + X * C (y i j) := rfl

private theorem aff_eq {x y : M4 R} {i j : Fin 4} {c : R} (hx : x i j = c) (hy : y i j = c) : aff x y i j = C c := by
  rw [aff_apply, hx, hy]; ring

private theorem aff_zero {x y : M4 R} {i j : Fin 4} (hx : x i j = 0) (hy : y i j = 0) : aff x y i j = 0 := by
  rw [aff_apply, hx, hy]
  simp

private theorem aff_smul_one (c : R) : aff (c • (1 : M4 R)) (c • 1) = (C c : R[X]) • (1 : M4 R[X]) := by
  refine Matrix.ext fun i j => ?_
  rw [aff_apply]
  by_cases h : i = j
  · subst h
    simp
    ring
  · simp [h]

private theorem aff_one : aff (1 : M4 R) 1 = 1 := by
  ext i j
  rw [aff_apply]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

private theorem adj_aff (x y : M4 R) : adj (aff x y) = aff (adj x) (adj y) := by
  ext i j
  rw [adj_apply, aff_apply, aff_apply, adj_apply, adj_apply, map_zsmul, map_zsmul, smul_add,
    mul_smul_comm, mul_smul_comm]

private structure Cong (x y : M4 R) : Prop where
  x01 : x 0 1 = 0
  x03 : x 0 3 = 0
  x21 : x 2 1 = 0
  x23 : x 2 3 = 0
  y01 : y 0 1 = 0
  y03 : y 0 3 = 0
  y21 : y 2 1 = 0
  y23 : y 2 3 = 0
  e00 : x 0 0 = y 0 0
  e02 : x 0 2 = y 0 2
  e20 : x 2 0 = y 2 0
  e22 : x 2 2 = y 2 2
  e11 : x 1 1 = y 1 1
  e13 : x 1 3 = y 1 3
  e31 : x 3 1 = y 3 1
  e33 : x 3 3 = y 3 3

private theorem Cong.adj {x y : M4 R} (h : Cong x y) : Cong (adj x) (adj y) := by
  have r0 : (0 : Fin 4).rev = 3 := rfl
  have r1 : (1 : Fin 4).rev = 2 := rfl
  have r2 : (2 : Fin 4).rev = 1 := rfl
  have r3 : (3 : Fin 4).rev = 0 := rfl
  constructor <;> simp only [adj_apply, r0, r1, r2, r3, h.x01, h.x03, h.x21, h.x23, h.y01, h.y03,
    h.y21, h.y23, h.e00, h.e02, h.e20, h.e22, h.e11, h.e13, h.e31, h.e33, smul_zero]

private theorem Cong.mul {x y z w : M4 R} (h : Cong x y) (h' : Cong z w) : Cong (x * z) (y * w) := by
  constructor <;> simp only [Matrix.mul_apply, Fin.sum_univ_four, h.x01, h.x03, h.x21, h.x23, h.y01,
    h.y03, h.y21, h.y23, h.e00, h.e02, h.e20, h.e22, h.e11, h.e13, h.e31, h.e33, h'.x01, h'.x03,
    h'.x21, h'.x23, h'.y01, h'.y03, h'.y21, h'.y23, h'.e00, h'.e02, h'.e20, h'.e22, h'.e11, h'.e13,
    h'.e31, h'.e33, mul_zero, zero_mul, add_zero, zero_add]

private theorem Cong.aff_mul {x y z w : M4 R} (h : Cong x y) (h' : Cong z w) :
    aff x y * aff z w = aff (x * z) (y * w) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8⟩ := h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, d1, d2, d3, d4, d5, d6, d7, d8⟩ := h'
  refine Matrix.ext fun i j => ?_
  simp only [aff_apply, Matrix.mul_apply, Fin.sum_univ_four, map_add, map_mul]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, map_zero, *] <;> ring

private theorem entries_zero_and_relation_of_suppM_of_isGSp {x : M4 R} {ν : R} (hx : SuppM nP x) (gx : IsGSp ν x) :
    x 0 1 = 0 ∧ x 0 2 = 0 ∧ x 0 3 = 0 ∧ x 1 3 = 0 ∧ x 2 1 = 0 ∧ x 2 3 = 0 ∧
      x 0 0 * x 3 1 = x 1 1 * x 2 0 := by
  have r0 : (0 : Fin 4).rev = 3 := rfl
  have r1 : (1 : Fin 4).rev = 2 := rfl
  have r2 : (2 : Fin 4).rev = 1 := rfl
  have r3 : (3 : Fin 4).rev = 0 := rfl
  have s0 : sgn 0 = 1 := rfl
  have s1 : sgn 1 = 1 := rfl
  have s2 : sgn 2 = -1 := rfl
  have s3 : sgn 3 = -1 := rfl
  have a01 : x 0 1 = 0 := hx 0 1 (by decide) (by decide)
  have a02 : x 0 2 = 0 := hx 0 2 (by decide) (by decide)
  have a03 : x 0 3 = 0 := hx 0 3 (by decide) (by decide)
  have a13 : x 1 3 = 0 := hx 1 3 (by decide) (by decide)
  have a21 : x 2 1 = 0 := hx 2 1 (by decide) (by decide)
  have a23 : x 2 3 = 0 := hx 2 3 (by decide) (by decide)
  have ex := congrArg (fun m : M4 R => m 2 0) gx
  simp [IsGSp, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, r0, r1, r2, r3, s0, s1, s2, s3,
    a01, a02, a03, a13, a21, a23] at ex
  refine ⟨a01, a02, a03, a13, a21, a23, ?_⟩
  linear_combination -ex

private theorem cong_of {x y : M4 R} {ν ν' : R} (hx : SuppM nP x) (hy : SuppM nP y) (gx : IsGSp ν x) (gy : IsGSp ν' y)
    (hd : ∀ i, x i i = y i i) (hu : IsUnit (x 0 0)) (h20 : x 2 0 = y 2 0) : Cong x y := by
  obtain ⟨a01, a02, a03, a13, a21, a23, ax⟩ := entries_zero_and_relation_of_suppM_of_isGSp hx gx
  obtain ⟨b01, b02, b03, b13, b21, b23, bx⟩ := entries_zero_and_relation_of_suppM_of_isGSp hy gy
  refine ⟨a01, a03, a21, a23, b01, b03, b21, b23, hd 0, a02.trans b02.symm, h20, hd 2, hd 1,
    a13.trans b13.symm, ?_, hd 3⟩
  refine hu.mul_left_cancel ?_
  rw [ax, hd 0, bx, hd 1, h20]

private theorem supp_nP {x : M4 R} (h : SuppM qQ x) : SuppM nP x := by
  intro i j hij hw
  refine h i j hij fun hq => hw ?_
  simp only [qQ, nP, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  tauto

private theorem lc_of_cont {Γ : Type} [TopologicalSpace Γ] {f : Γ → R} (h : AdicCont ⊥ f) : IsLocallyConstant f := by
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]

end

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.lineP :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ c c' : PD Φ.ι Γ k, Φ.IsRes a c → Φ.IsRes a c' → c.In nP → c'.In nP → c.SamePs c' → Φ.Linked a c c' := by
  intro O Γ _ _ _ _ _ _ Φ k _ a hΦ c c' hc hc' hin hin' hs
  have cong : ∀ g, Cong (c.r g) (c'.r g) := fun g =>
    cong_of (hin.1 g) (hin'.1 g) (hc.pair.mult g) (hc'.pair.mult g)
      (fun i => (hc.res.diag g i).trans (hc'.res.diag g i).symm)
      (by rw [hc.res.diag g 0]; exact (Φ.χ 0 g).isUnit.map a) (hs.1 g)
  have congN : ∀ v, Cong (c.n v) (c'.n v) := fun v =>
    cong_of (supp_nP (hin.2 v)) (supp_nP (hin'.2 v)) (hc.pair.low v).1 (hc'.pair.low v).1
      (fun i => ((hc.pair.low v).2.1 i).trans ((hc'.pair.low v).2.1 i).symm)
      (by rw [(hc.pair.low v).2.1 0]; exact isUnit_one) (hs.2 v)
  have gsp : ∀ {x y : M4 k} {ν : k}, Cong x y → IsGSp ν x → IsGSp ν y → IsGSp (C ν) (aff x y) := by
    intro x y ν h gx gy
    unfold IsGSp at *
    rw [adj_aff, h.adj.aff_mul h, gx, gy, aff_smul_one]
  obtain ⟨ρ, hr⟩ : ∃ ρ : Γ →* M4 k[X], ∀ g, ρ g = aff (c.r g) (c'.r g) :=
    ⟨{ toFun := fun g => aff (c.r g) (c'.r g)
       map_one' := by
         show aff (c.r 1) (c'.r 1) = 1
         rw [map_one, map_one, aff_one]
       map_mul' := fun g h => by
         show aff (c.r (g * h)) (c'.r (g * h)) = aff (c.r g) (c'.r g) * aff (c.r h) (c'.r h)
         rw [map_mul, map_mul, (cong g).aff_mul (cong h)] }, fun _ => rfl⟩
  have conj : ∀ v s, adj (aff (c.n v) (c'.n v)) * ρ s * aff (c.n v) (c'.n v) =
      aff (adj (c.n v) * c.r s * c.n v) (adj (c'.n v) * c'.r s * c'.n v) := by
    intro v s
    rw [hr, adj_aff, (congN v).adj.aff_mul (cong s), ((congN v).adj.mul (cong s)).aff_mul (congN v)]
  refine ⟨⟨ρ, fun v => aff (c.n v) (c'.n v)⟩, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro g
    dsimp only
    rw [hr]
    exact gsp (cong g) (hc.pair.mult g) (hc'.pair.mult g)
  · intro g hg
    dsimp only
    rw [hr, hc.pair.kill g hg, hc'.pair.kill g hg, aff_one]
  · intro i j hij
    dsimp only
    rw [hr]
    exact aff_zero (hc.pair.nrm hij) (hc'.pair.nrm hij)
  · intro v
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · have h1 := gsp (congN v) (hc.pair.low v).1 (hc'.pair.low v).1
      rwa [map_one] at h1
    · exact (aff_eq ((hc.pair.low v).2.1 i) ((hc'.pair.low v).2.1 i)).trans (map_one C)
    · exact aff_zero ((hc.pair.low v).2.2 i j hij) ((hc'.pair.low v).2.2 i j hij)
  · intro v s hs' i j hij
    dsimp only
    rw [conj]
    exact aff_zero (hc.pair.flag v s hs' i j hij) (hc'.pair.flag v s hs' i j hij)
  · intro v s hs' i
    unfold PD.ψ
    dsimp only
    rw [conj]
    exact (aff_eq (hc.pair.mu v s hs' i) (hc'.pair.mu v s hs' i)).trans (map_one C)
  · intro g i
    dsimp only
    rw [hr]
    exact aff_eq (hc.res.diag g i) (hc'.res.diag g i)
  · intro v s hs' i
    unfold PD.ψ
    dsimp only
    rw [conj]
    exact aff_eq (hc.res.char v s hs' i) (hc'.res.char v s hs' i)
  · left
    refine ⟨fun g i j hij hw => ?_, fun v i j hij hw => ?_⟩
    · dsimp only
      rw [hr]
      exact aff_zero (hin.1 g i j hij hw) (hin'.1 g i j hij hw)
    · exact aff_zero (hin.2 v i j hij hw) (hin'.2 v i j hij hw)
  · intro i j N
    have l1 := lc_of_cont (hc.cont i j)
    have l2 := lc_of_cont (hc'.cont i j)
    have l3 := IsLocallyConstant.comp₂ l1 l2
      (fun u w => Ideal.Quotient.mk ((⊥ : Ideal k[X]) ^ N) ((1 - X) * C u + X * C w))
    dsimp only
    simp only [hr, aff_apply]
    exact l3
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, mapRep, hr, aff_apply]
    · funext v
      ext i j
      simp [PD.map, aff_apply]
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, mapRep, hr, aff_apply]
    · funext v
      ext i j
      simp [PD.map, aff_apply]
