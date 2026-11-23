import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfE

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

section Local

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq] {k : ℕ}

theorem den_one (π : W) (hπ : Irreducible π) (x : Qq) :
    ∃ (n : ℕ) (c : W), algebraMap W Qq π ^ n * x = algebraMap W Qq c := by
  obtain ⟨⟨c, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors W) x
  have hs0 : (s : W) ≠ 0 := nonZeroDivisors.ne_zero s.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hπ
  refine ⟨n, ((u⁻¹ : Wˣ) : W) * c, ?_⟩
  simp only at hs
  rw [hu, map_mul, map_pow] at hs
  have hu' : algebraMap W Qq (u : W) * algebraMap W Qq ((u⁻¹ : Wˣ) : W) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul]
  linear_combination algebraMap W Qq ((u⁻¹ : Wˣ) : W) * hs - algebraMap W Qq π ^ n * x * hu'

theorem den_mat (π : W) (hπ : Irreducible π) (h : Matrix (Fin k) (Fin k) Qq) :
    ∃ (N : ℕ) (H : Matrix (Fin k) (Fin k) W), algebraMap W Qq π ^ N • h = H.map (algebraMap W Qq) := by
  choose nn cc hnc using fun i j => den_one π hπ (h i j)
  refine ⟨∑ i, ∑ j, nn i j, Matrix.of fun i j => π ^ (∑ i, ∑ j, nn i j - nn i j) * cc i j, ?_⟩
  ext i j
  have hle : nn i j ≤ ∑ i, ∑ j, nn i j :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (nn i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, nn i j) (fun i _ => Nat.zero_le _) (Finset.mem_univ i))
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, ← hnc i j]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem colSpan_mul_le (g : Matrix (Fin k) (Fin k) Qq) (U : Matrix (Fin k) (Fin k) W) :
    colSpan W (g * U.map (algebraMap W Qq)) ≤ colSpan W g := by
  unfold colSpan
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have h : (fun i => (g * U.map (algebraMap W Qq)) i c) = ∑ b, U b c • (fun i => g i b) := by
    funext i
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  show (fun i => (g * U.map (algebraMap W Qq)) i c) ∈ Submodule.span W (Set.range fun c : Fin k => fun i => g i c)
  rw [h]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem colSpan_mul_unit (g : Matrix (Fin k) (Fin k) Qq) (U : Matrix (Fin k) (Fin k) W) (hU : IsUnit U.det) :
    colSpan W (g * U.map (algebraMap W Qq)) = colSpan W g := by
  apply le_antisymm (colSpan_mul_le g U)
  have h := colSpan_mul_le (g * U.map (algebraMap W Qq)) U⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv U hU, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.mul_one] at h

theorem det_one_add_unit (π : W) (hπ : Irreducible π) (D : Matrix (Fin k) (Fin k) W) : IsUnit (1 + π • D).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hπ0 : IsLocalRing.residue W π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  have h1 : (IsLocalRing.residue W).mapMatrix (1 + π • D) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, hπ0, zero_mul, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1, Matrix.det_one]
  exact one_ne_zero

theorem approx_local (π : W) (hπ : Irreducible π) (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) :
    ∃ N : ℕ, ∀ N', N ≤ N' → ∀ (A : Matrix (Fin k) (Fin k) Qq) (C : Matrix (Fin k) (Fin k) W),
      A = g + algebraMap W Qq π ^ N' • C.map (algebraMap W Qq) → colSpan W A = colSpan W g ∧ IsUnit A.det := by
  obtain ⟨N, H, hH⟩ := den_mat π hπ g⁻¹
  refine ⟨N + 1, fun N' hN A C hA => ?_⟩
  have hU : IsUnit (1 + π • (π ^ (N' - (N + 1)) • (H * C))).det := det_one_add_unit π hπ _
  have hAU : A = g * (1 + π • (π ^ (N' - (N + 1)) • (H * C))).map (algebraMap W Qq) := by
    rw [hA, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, map_pow, ← hH,
      Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.one_mul, smul_smul, smul_smul]
    congr 2
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  refine ⟨by rw [hAU]; exact colSpan_mul_unit g _ hU, ?_⟩
  rw [hAU, Matrix.det_mul]
  refine hg.mul ?_
  have h2 : ((1 + π • (π ^ (N' - (N + 1)) • (H * C))).map (algebraMap W Qq)).det =
      algebraMap W Qq (1 + π • (π ^ (N' - (N + 1)) • (H * C))).det := by
    rw [RingHom.map_det]; rfl
  rw [h2]
  exact hU.map _

end Local

variable {p : ℕ} (G : GAtP p) {E : Type} [Field E] (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)

def WeakApprox : Prop :=
  ∀ (x : ∀ v, G.P.Qq v) (N : ℕ), ∃ a : E, ∀ v, ∃ c : G.P.W v,
    iw v a = x v + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c

theorem ratTup_of_weak (h : WeakApprox G iw) : RatTup G iw := by
  intro L hL
  by_cases hne : Nonempty (Fin G.P.nV)
  swap
  · exact ⟨1, fun v => (hne ⟨v⟩).elim⟩
  choose g hg hLg using hL
  have := fun v => (G.P.setting v).frac_alt
  choose N hN using fun v => approx_local (p : G.P.W v) (G.P.setting v).p_unif (g v) (hg v)
  choose a c hac using fun x y => h (fun v => g v x y) (∑ v, N v)
  have key : ∀ v, colSpan (G.P.W v) ((Matrix.of a).map (iw v)) = colSpan (G.P.W v) (g v) ∧
      IsUnit ((Matrix.of a).map (iw v)).det := fun v =>
    hN v (∑ v, N v) (Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))
      ((Matrix.of a).map (iw v)) (fun x y => c x y v) (by
        ext x y
        simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_natCast]
        exact hac x y v)
  obtain ⟨v0⟩ := hne
  have hdet : IsUnit (Matrix.of a).det := by
    have h1 := (key v0).2
    have h2 : ((Matrix.of a).map (iw v0)).det = iw v0 (Matrix.of a).det := by
      rw [RingHom.map_det]; rfl
    rw [h2] at h1
    rw [isUnit_iff_ne_zero] at h1 ⊢
    intro h0
    exact h1 (by rw [h0, map_zero])
  exact ⟨Matrix.nonsingInvUnit (Matrix.of a) hdet, fun v => by rw [hLg v]; exact (key v).1.symm⟩

end Formalism.L2.G.Cmp
