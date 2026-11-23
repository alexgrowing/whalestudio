import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Ord2.locConst_mod_pow :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l), Continuous W →
      (∀ s i j, mat W s i j ∈ c.O) → ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j,
        ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o := by
  intro l _ Ω _ _ c W hW hO n s
  have hc : ∀ i j, Continuous fun t => mat W t i j := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp hW).matrix_elem i j
  have hr : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := by
    rw [norm_pos_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
  have hev : ∀ᶠ t in nhds s, mat W t i j ∈ Metric.closedBall (mat W s i j) ‖((l : ℕ) : Qbar l) ^ n‖ :=
    (hc i j).continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr)
  filter_upwards [hev] with t ht
  rw [Metric.mem_closedBall, dist_eq_norm] at ht
  have hmem : mat W t i j - mat W s i j ∈ c.O := c.O.sub_mem (hO t i j) (hO s i j)
  obtain ⟨o, ho⟩ := (GlobalTheory.Coef.norm_le_norm_pow_iff_dvd l c n ⟨_, hmem⟩).1 ht
  refine ⟨(o : Qbar l), o.2, ?_⟩
  have := congrArg (fun x : c.O => (x : Qbar l)) ho
  simpa using this
