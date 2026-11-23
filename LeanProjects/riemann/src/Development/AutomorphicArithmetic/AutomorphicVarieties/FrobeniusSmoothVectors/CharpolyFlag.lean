import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FlagLoc

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zpow_w_ne' {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) : a ^ w n i ≠ a ^ w n j := by
  have h1 : a ≠ 1 := fun h => ha (by rw [h, one_pow])
  have h2 : a ≠ a⁻¹ := fun h => ha (by rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel a)
  have h3 : (1 : kˣ) ≠ a⁻¹ := fun h => h1 (by rw [← inv_inv a, ← h, inv_one])
  rcases hn with rfl | rfl
  · fin_cases i <;> fin_cases j <;> simp_all [UpperTheory.V.Fr.w] <;> simp_all [eq_comm]
  · fin_cases i <;> fin_cases j <;> simp_all [UpperTheory.V.Fr.w] <;> simp_all [eq_comm]

private theorem residue_eq {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {x y : R} (h : res O R x = res O R y) : residue R x = residue R y := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← res_eq_zero_iff O R, map_sub, h, sub_self]

private theorem charpoly_flag' {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : UpperTheory.V.W.HasFlag r.toHomUnits κ) (s : H) :
    (r s).charpoly = ∏ i, (Polynomial.X - Polynomial.C (κ i s : k)) := by
  obtain ⟨g, hg⟩ := h
  have e : ((g * r.toHomUnits s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = (g : Matrix (Fin n) (Fin n) k) * r s * (g : Matrix (Fin n) (Fin n) k)⁻¹ := by
    simp [Matrix.coe_units_inv]
  have hc := Matrix.charpoly_units_conj g (r s)
  rw [← hc, ← e, Matrix.charpoly_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [(hg s).2 i]
  · intro i j hij
    exact (hg s).1 i j hij

theorem UpperTheory.V.Fr.o1 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ v g, (S.u.r (F.loc0 v g)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (S.u.ψ v i g : S.A)) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S v g
  obtain ⟨g₀, hg⟩ := hF.f3 v
  have h4 : ∀ i, res O S.R (S.ρ.ψ v i g₀) = ((F.Ψ (F.loc v g₀) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun i => S.lift.2.1.2 v i g₀
  have hfl : UpperTheory.V.W.HasFlag (S.ρ.r.comp (F.loc0 v)).toHomUnits (S.ρ.ψ v) := by
    refine flag_loc _ _ g₀ (fun i j hij => ?_) ?_ (fun s => S.ρ.ord v s)
    · by_contra hu
      have h2 : (S.ρ.ψ v i g₀ : S.R) - S.ρ.ψ v j g₀ ∈ maximalIdeal S.R := hu
      have h3 := (res_eq_zero_iff O S.R _).2 h2
      rw [map_sub, h4, h4, sub_eq_zero] at h3
      exact zpow_w_ne' hn _ hg i j hij (Units.ext h3)
    · have hd : ((S.ρ.r.comp (F.loc0 v)) g₀).map (residue S.R) =
          Matrix.diagonal fun i => residue S.R (S.ρ.ψ v i g₀) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq]
          refine residue_eq (O := O) ?_
          rw [h4]
          exact S.lift.2.1.1 (F.loc0 v g₀) i
        · rw [Matrix.diagonal_apply_ne _ hij, ← map_zero (residue S.R)]
          refine residue_eq (O := O) ?_
          rw [map_zero]
          exact S.lift.2.2 (F.loc0 v g₀) i j hij
      rw [hd, Matrix.charpoly_diagonal]
  have h := charpoly_flag' _ _ hfl g
  refine Polynomial.map_injective (S.A.val : S.A →+* S.R) Subtype.val_injective ?_
  rw [← Matrix.charpoly_map, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact h
