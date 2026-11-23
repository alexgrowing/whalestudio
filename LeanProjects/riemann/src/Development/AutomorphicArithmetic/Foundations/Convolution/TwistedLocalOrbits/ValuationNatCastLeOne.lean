import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake

open ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.BallG

section Bound

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private def Bd (c : ValueGroupWithZero E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, valuation E (M i j) ≤ c

variable {a b c : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E}

private theorem Bd.mono (h : Bd a M) (hab : a ≤ b) : Bd b M := fun i j => (h i j).trans hab

private theorem Bd.add (h : Bd a M) (h' : Bd a N) : Bd a (M + N) := fun i j =>
  Valuation.map_add_le _ (h i j) (h' i j)

private theorem Bd.neg (h : Bd a M) : Bd a (-M) := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]
  exact h i j

private theorem Bd.mul (h : Bd a M) (h' : Bd b N) : Bd (a * b) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem Bd.nsmul (h : Bd a M) (m : ℕ) : Bd a (m • M) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih => rw [succ_nsmul]; exact ih.add h

private theorem Bd.pow (h : Bd a M) (ha : a ≤ 1) (m : ℕ) : Bd (a * a) ((1 + M) ^ m - 1 - m • M) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih =>
    have e : (1 + M) ^ (m + 1) - 1 - (m + 1) • M =
        ((1 + M) ^ m - 1 - m • M) + ((1 + M) ^ m - 1 - m • M) * M + (m • M) * M := by
      rw [pow_succ, succ_nsmul]
      generalize m • M = D
      noncomm_ring
    rw [e]
    exact (ih.add ((ih.mul h).mono (mul_le_of_le_one_right' ha))).add ((h.nsmul m).mul h)

private theorem Bd.inv (h : Bd a M) (ha : a < 1) (e : N = -M + -(M * N)) : Bd a N := by
  intro i j
  haveI : Nonempty (Fin n × Fin n) := ⟨(i, j)⟩
  obtain ⟨p, hp⟩ := Finite.exists_max fun p : Fin n × Fin n => valuation E (N p.1 p.2)
  have hN : Bd (valuation E (N p.1 p.2)) N := fun i j => hp (i, j)
  refine (hp (i, j)).trans ?_
  have h1 : Bd (max a (a * valuation E (N p.1 p.2))) (-M + -(M * N)) :=
    (h.neg.mono (le_max_left _ _)).add ((h.mul hN).neg.mono (le_max_right _ _))
  have h2 := h1 p.1 p.2
  rw [← e] at h2
  rcases le_max_iff.mp h2 with h3 | h3
  · exact h3
  · by_contra h4
    have h0 : 0 < valuation E (N p.1 p.2) := lt_of_le_of_lt zero_le (not_le.mp h4)
    exact absurd h3 (not_le.mpr (mul_lt_of_lt_one_left h0 ha))

theorem valuation_natCast_le_one (q : ℕ) : valuation E (q : E) ≤ 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by simp)

end Bound

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

theorem ball_mono {r s : ValueGroupWithZero E} (h : r ≤ s) : ball n r ⊆ ball n s := fun _ hg i j => (hg i j).trans h

def ballSub (n : ℕ) (r : ValueGroupWithZero E) (hr : r < 1) : Subgroup (GL (Fin n) E) where
  carrier := ball n r
  one_mem' := fun i j => by simp
  mul_mem' := by
    intro x y hx hy
    have hx' : Bd r ((x : Matrix (Fin n) (Fin n) E) - 1) := hx
    have hy' : Bd r ((y : Matrix (Fin n) (Fin n) E) - 1) := hy
    have e : ((x * y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
        (x - 1) + (y - 1) + ((x : Matrix (Fin n) (Fin n) E) - 1) * (y - 1) := by
      rw [Units.val_mul]; noncomm_ring
    have := (hx'.add hy').add ((hx'.mul hy').mono (mul_le_of_le_one_right' hr.le))
    rw [← e] at this
    exact this
  inv_mem' := by
    intro x hx
    have hx' : Bd r ((x : Matrix (Fin n) (Fin n) E) - 1) := hx
    refine (hx'.inv hr (N := ((x⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) ?_ :)
    rw [mul_sub, sub_mul, Units.mul_inv]
    noncomm_ring

theorem isOpen_ball {r : ValueGroupWithZero E} (hr : r ≠ 0) : IsOpen (ball n r) := by
  have hO : IsOpen {x : E | valuation E x ≤ r} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨Units.mk0 r hr, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact Valuation.map_add_le _ hx (le_of_lt (show valuation E z < r from hz))
  have e : ball n r = ⋂ i, ⋂ j, (fun g : GL (Fin n) E =>
      (g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) ⁻¹' {x : E | valuation E x ≤ r} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hO.preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem isCompact_ball {r : ValueGroupWithZero E} (hr : r < 1) : IsCompact (ball n r) := by
  have h0 : IsCompact {M : Matrix (Fin n) (Fin n) E | Bd r M} :=
    isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ r}})
      fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E r
  have h1 : IsCompact {M : Matrix (Fin n) (Fin n) E | Bd r (M - 1)} :=
    (Homeomorph.subRight (1 : Matrix (Fin n) (Fin n) E)).isCompact_preimage.mpr h0
  have h2 := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.2.2 _ _ h1 h1
  convert h2 using 1
  ext g
  exact ⟨fun hg => ⟨hg, (ballSub n r hr).inv_mem hg⟩, fun hg => hg.1⟩

theorem pow_mem_ball {q : ℕ} {r : ValueGroupWithZero E} (hr : r < valuation E (q : E)) {u : GL (Fin n) E}
    (hu : u ∈ ball n r) : u ^ q ∈ ball n (r * valuation E (q : E)) := by
  have hu' : Bd r ((u : Matrix (Fin n) (Fin n) E) - 1) := hu
  have h1 := (hu'.pow (hr.le.trans (valuation_natCast_le_one q)) q).mono (mul_le_mul' le_rfl hr.le)
  have h2 : Bd (r * valuation E (q : E)) (q • ((u : Matrix (Fin n) (Fin n) E) - 1)) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, map_mul, mul_comm]
    exact mul_le_mul' (hu' i j) le_rfl
  have h3 := h1.add h2
  rw [sub_add_cancel, add_sub_cancel, ← Units.val_pow_eq_pow_val] at h3
  exact h3

theorem sg_mem_ball_iff {σ : E ≃+* E} (hσ : Isom σ) {r : ValueGroupWithZero E} {u : GL (Fin n) E} :
    sg σ u ∈ ball n r ↔ u ∈ ball n r := by
  refine forall₂_congr fun i j => ?_
  have e : ((sg σ u : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      σ ((u : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
    rw [map_sub]
    congr 1
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [e, hσ]

theorem exists_fixed_root {σ : E ≃+* E} (hσ : Isom σ) {q : ℕ} {r : ValueGroupWithZero E} (hr : r < valuation E (q : E))
    {g : GL (Fin n) E} (hg : g ∈ ball n (r * valuation E (q : E))) (hf : sg σ g = g) :
    ∃ u ∈ ball n r, sg σ u = u ∧ u ^ q = g := by
  obtain ⟨u, ⟨hu, huq⟩, huu⟩ := rootEx E n q r hr g hg
  exact ⟨u, hu, huu _ ⟨(sg_mem_ball_iff hσ).mpr hu, by rw [← map_pow, huq, hf]⟩, huq⟩

theorem exists_radius {w : ValueGroupWithZero E} (hw : w ≠ 0) : ∃ r : ValueGroupWithZero E, 0 < r ∧ r < w := by
  obtain ⟨c, hc0, hc1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := E)
  exact ⟨c * w, mul_pos hc0 (zero_lt_iff.mpr hw), mul_lt_of_lt_one_left (zero_lt_iff.mpr hw) hc1⟩

end UpperTheory.ConvolutionTheory.Loc.BallG
