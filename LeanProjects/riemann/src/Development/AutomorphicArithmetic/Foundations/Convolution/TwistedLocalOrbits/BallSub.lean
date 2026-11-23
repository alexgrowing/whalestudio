import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake

open ValuativeRel UpperTheory.ConvolutionTheory.Loc

section

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private theorem bd_mul {a b : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E} (h : ∀ i j, valuation E (M i j) ≤ a)
    (h' : ∀ i j, valuation E (N i j) ≤ b) (i j : Fin n) : valuation E ((M * N) i j) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem bd_one (i j : Fin n) : valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem bd_inv {r : ValueGroupWithZero E} (hr : r < 1) {A H : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, valuation E (A i j) ≤ r)
    (hH : H = 1 - H * A) (i j : Fin n) : valuation E (H i j) ≤ 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => valuation E (H p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  refine (hp (i, j) (Finset.mem_univ _)).trans ?_
  by_contra hc
  push Not at hc
  have h1 := bd_mul (fun a b => hp (a, b) (Finset.mem_univ _)) hA p.1 p.2
  have h2 : valuation E ((H * A) p.1 p.2) < valuation E (H p.1 p.2) :=
    h1.trans_lt (mul_lt_of_lt_one_right (zero_lt_one.trans hc) hr)
  have h3 : valuation E ((1 - H * A) p.1 p.2) < valuation E (H p.1 p.2) :=
    Valuation.map_sub_lt _ ((bd_one _ _).trans_lt hc) h2
  rw [← hH] at h3
  exact lt_irrefl _ h3

end

theorem UpperTheory.ConvolutionTheory.Loc.ballSub :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (r : ValueGroupWithZero E), 0 < r → r < 1 →
      ∃ K : Subgroup (GL (Fin n) E), (K : Set (GL (Fin n) E)) = ball n r ∧ IsOpen (K : Set (GL (Fin n) E)) ∧ IsCompact (K : Set (GL (Fin n) E)) := by
  intro E _ _ _ _ n r h0 h1
  have mb : ∀ {g : GL (Fin n) E}, g ∈ ball n r → ∀ i j, valuation E (((g : Matrix (Fin n) (Fin n) E) - 1) i j) ≤ r := fun hg i j => hg i j
  have hinv : ∀ g ∈ ball (E := E) n r, g⁻¹ ∈ ball n r := by
    intro g hg i j
    have e : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 - (g⁻¹ : GL (Fin n) E) * ((g : Matrix (Fin n) (Fin n) E) - 1) := by
      rw [mul_sub, Units.inv_mul]; simp
    have h := bd_mul (bd_inv h1 (mb hg) e) (mb hg) i j
    rw [one_mul] at h
    rw [e, Matrix.sub_apply, sub_sub_cancel_left, Valuation.map_neg]
    exact h
  let K : Subgroup (GL (Fin n) E) :=
    { carrier := ball n r
      one_mem' := fun i j => by simp
      inv_mem' := fun {g} hg => hinv g hg
      mul_mem' := fun {a b} ha hb i j => by
        have e : ((a * b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
            ((a : Matrix (Fin n) (Fin n) E) - 1) * ((b : Matrix (Fin n) (Fin n) E) - 1) + ((a : Matrix (Fin n) (Fin n) E) - 1) +
              ((b : Matrix (Fin n) (Fin n) E) - 1) := by
          rw [Units.val_mul]; noncomm_ring
        rw [← Matrix.sub_apply, e]
        refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (ha i j)) (hb i j)
        exact (bd_mul (mb ha) (mb hb) i j).trans
          (mul_le_of_le_one_right' h1.le) }
  have hent : ∀ i j, Continuous fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j :=
    fun i j => (Units.continuous_val.matrix_elem i j).sub continuous_const
  refine ⟨K, rfl, K.isOpen_of_mem_nhds (g := 1) ?_, ?_⟩
  · have hb : {x : E | valuation E x < r} ∈ nhds (0 : E) :=
      (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 r h0.ne', subset_rfl⟩
    have : ∀ᶠ g : GL (Fin n) E in nhds 1, ∀ i j,
        valuation E ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) < r := by
      refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact (hent i j).continuousAt.preimage_mem_nhds (t := {x : E | valuation E x < r}) (by simpa using hb)
    exact this.mono fun g hg i j => (hg i j).le
  · have hc : IsCompact {M : Matrix (Fin n) (Fin n) E | ∀ i j, valuation E (M i j) ≤ r} :=
      isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ r}})
        fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E r
    have hc' := hc.image (f := fun M => M + 1) (by fun_prop)
    have h := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.2.2 _ _ hc' hc'
    convert h using 1
    ext g
    constructor
    · intro hg
      exact ⟨⟨_, mb hg, sub_add_cancel _ _⟩, ⟨_, mb (hinv g hg), sub_add_cancel _ _⟩⟩
    · rintro ⟨⟨M, hM, e⟩, -⟩ i j
      rw [← e]
      simpa using hM i j
