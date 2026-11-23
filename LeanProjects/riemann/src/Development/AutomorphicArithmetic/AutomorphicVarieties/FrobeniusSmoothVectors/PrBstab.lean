import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C}
    (hM : UpT M) (hN : UpT N) : UpT (M * N) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : a < i
  · rw [hM i a ha, zero_mul]
  · rw [hN a j (lt_of_lt_of_le h (not_lt.mp ha)), mul_zero]

theorem UpperTheory.V.Fr.pr_bstab :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (C : Type) [CommRing C] (B : Box F n C) (v : F.V) (s : F.Gv v), ∀ X ∈ B.b v, B.ad (F.loc v s) X ∈ B.b v := by
  intro l _ k _ F n C _ B v s X hX
  have h1 : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have h2 : (B.r (F.loc v s⁻¹)).left = (B.r (F.loc v s)).left⁻¹ := by
    rw [map_inv, map_inv, SemidirectProduct.inv_left, h1, inv_one, sgnAct_one]
  have t1 := B.tri v s
  have t2 := B.tri v s⁻¹
  have t3 := upT_mul (upT_mul t1 hX) t2
  simp only [GG.mat, h2] at t3
  show UpT ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).adFun X *
    (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))
  have hg : ∀ Y : Matrix (Fin n) (Fin n) C,
      (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) * ((B.g v : Matrix (Fin n) (Fin n) C) * Y) = Y :=
    fun Y => Units.inv_mul_cancel_left _ Y
  simp only [Matrix.mul_assoc, hg] at t3
  simp only [GG.adFun, GG.mat, h1, if_true, Matrix.mul_assoc]
  exact t3
