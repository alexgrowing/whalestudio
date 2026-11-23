import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CzBasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem dvr_norm {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A →+* PadicAlgCl l) (hle : ∀ x, ‖f x‖ ≤ 1) :
    (∀ u : A, IsUnit u → ‖f u‖ = 1) ∧
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ (n : ℕ) (x : A), x ∈ maximalIdeal A ^ n → ‖f x‖ ≤ q ^ n := by
  have hu : ∀ u : Aˣ, ‖f u‖ = 1 := by
    intro u
    have h1 : ‖f u‖ * ‖f ((u⁻¹ : Aˣ) : A)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Aˣ)
    have h4 := norm_nonneg (f u)
    nlinarith
  refine ⟨fun u ⟨v, hv⟩ => hv ▸ hu v, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hl0 : (l : A) ≠ 0 := by
    intro h
    have h' : f l = 0 := by rw [h, map_zero]
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖f l‖ < 1 := by
    have : f l = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine ⟨‖f ϖ‖, norm_nonneg _, ?_, fun n x hx => ?_⟩
  · obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    rw [h, map_mul, norm_mul, hu, one_mul, map_pow, norm_pow] at hl
    by_contra hc
    exact absurd hl (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))
  · rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle y)

private theorem conjBy_conjBy {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h k : GL (Fin 3) R) :
    conjBy h (conjBy k r) = conjBy (h * k) r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy, mul_assoc]

private theorem conjBy_mat {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h⁻¹ r g).mat =
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * (h : Matrix (Fin 3) (Fin 3) R) := by
  simp [conjBy, GG.mat, hg]

private theorem unit_diff {O : Type} [CommRing O] (x : Oˣ) (hx : IsUnit ((x : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((x ^ wt1 a : Oˣ) : O) - ((x ^ wt1 b : Oˣ) : O)) := by
  have h1 : IsUnit ((x : O) - 1) := by
    have e : (x : O) ^ 2 - 1 = ((x : O) - 1) * ((x : O) + 1) := by ring
    rw [e] at hx
    exact isUnit_of_mul_isUnit_left hx
  have hxy : ((x⁻¹ : Oˣ) : O) * (x : O) = 1 := Units.inv_mul x
  have h2 : IsUnit ((x : O) - ((x⁻¹ : Oˣ) : O)) := by
    have e : (x : O) - ((x⁻¹ : Oˣ) : O) = ((x⁻¹ : Oˣ) : O) * ((x : O) ^ 2 - 1) := by
      linear_combination (-(x : O)) * hxy
    rw [e]
    exact (Units.isUnit _).mul hx
  have h3 : IsUnit ((1 : O) - ((x⁻¹ : Oˣ) : O)) := by
    have e : (1 : O) - ((x⁻¹ : Oˣ) : O) = ((x⁻¹ : Oˣ) : O) * ((x : O) - 1) := by
      linear_combination (-1 : O) * hxy
    rw [e]
    exact (Units.isUnit _).mul h1
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | simpa [wt1]

theorem UpperTheory.V.UnitaryThreeInertia.rig_eig :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {G' Γ ι : Type} [Group G'] [TopologicalSpace G'] [Group Γ] [TopologicalSpace Γ] (F : Frame c.O G' Γ ι) (g₁ : Γ) (r : Γ →* GG 3 (PadicAlgCl l)), F.IsCharZeroPt g₁ r → ∀ g : Γ, F.η g = 1 → IsUnit ((F.Ψ g : c.O) ^ 2 - 1) → ∀ P : GL (Fin 3) (PadicAlgCl l), (∀ i j, j < i → (conjBy P⁻¹ r g).mat i j = 0) → ∀ i j, i ≠ j → ∀ u : PadicAlgCl l, ‖u - 1‖ < 1 → (conjBy P⁻¹ r g).mat i i ≠ (conjBy P⁻¹ r g).mat j j * u := by
  intro l _ c G' Γ ι _ _ _ _ F g₁ r hr g hη hΨ P
  obtain ⟨A, hA, hfin, t, r', hpt, hp⟩ := hr
  have hle : ∀ x : A, ‖A.val x‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ (isIntegral_trans (A := c.O) _ ((Algebra.IsIntegral.isIntegral (R := c.O) x).map A.val))
  obtain ⟨hu, q, hq0, hq1, hq⟩ := dvr_norm (A.val : A →+* PadicAlgCl l) hle
  simp only [RingHom.coe_coe] at hu hq
  have hO : ∀ x : c.O, IsUnit x → ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := fun x hx => by
    rw [← hu _ (hx.map (algebraMap c.O A)), AlgHom.commutes]
  have e : conjBy P⁻¹ r = conjBy (tor _ t * P)⁻¹ (push A.val r') := by
    rw [hp, conjBy_conjBy, _root_.mul_inv_rev, inv_mul_cancel_right]
  have hright : (push A.val r' g).right = 1 := (hpt.mult g).trans hη
  rw [e, conjBy_mat _ _ _ hright]
  refine rig_sep _ (fun a => algebraMap c.O (PadicAlgCl l) ((F.Ψ g ^ wt1 a : (c.O)ˣ) : c.O)) _ ?_ ?_ ?_
  · intro a b
    have h := hq 1 _ (by rw [pow_one]; exact hpt.red g a b)
    rw [pow_one, Matrix.sub_apply, map_sub, Matrix.map_apply, AlgHom.commutes] at h
    refine lt_of_le_of_lt (le_of_eq_of_le ?_ h) hq1
    congr 2
    show _ = algebraMap c.O (PadicAlgCl l) (Matrix.diagonal (fun i => ((F.Ψ g ^ wt1 i : (c.O)ˣ) : c.O)) a b)
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · rfl
    · rw [map_zero]
  · intro a
    exact hO _ (Units.isUnit _)
  · intro a b hab
    rw [← map_sub]
    exact hO _ (unit_diff _ hΨ a b hab)
