import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict
import GroundTheory.AutomorphicForms.Cartan
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen
open GroundTheory.Automorphic

private theorem norm_unif_lt_one (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : Formalism.UG.IsUnifV E w x) : ‖x‖ < 1 := by
  have hv : Valued.v x < 1 := by
    rw [hx]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1)
  exact Valued.toNormedField.norm_lt_one_iff.mpr hv

private theorem nonneg_of_pow_mem (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (hU : ‖(GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E)‖ < 1)
    {Z : Set (GL (Fin a) (w.adicCompletion E))} (hZ : IsCompact Z) (ν : Fin a → ℤ)
    (hν : ∀ m : ℕ, Cartan.diagPow (w.adicCompletion E) a ν ^ m ∈ Z) (i : Fin a) : 0 ≤ ν i := by
  by_contra hneg
  push_neg at hneg
  set ϖ : w.adicCompletion E := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) with hϖ
  have h0 : ϖ ≠ 0 := Cartan.uniformizer_ne_zero _
  have hf : Continuous fun x : GL (Fin a) (w.adicCompletion E) =>
      (x : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i :=
    Continuous.matrix_elem Units.continuous_val i i
  obtain ⟨C, hC⟩ := (hZ.image hf).isBounded.exists_norm_le
  have hentry : ∀ m : ℕ, ‖ϖ ^ ν i‖ ^ m ≤ C := by
    intro m
    have h : ‖((Cartan.diagPow (w.adicCompletion E) a ν ^ m : GL (Fin a) (w.adicCompletion E)) :
        Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i‖ ≤ C := hC _ ⟨_, hν m, rfl⟩
    rw [Units.val_pow_eq_pow_val, Cartan.coe_diagPow, Matrix.diagonal_pow, Matrix.diagonal_apply_eq,
      Pi.pow_apply, norm_pow] at h
    exact h
  have hgt : 1 < ‖ϖ ^ ν i‖ := by
    rw [norm_zpow]
    have hp : 0 < ‖ϖ‖ := norm_pos_iff.2 h0
    exact one_lt_zpow_of_neg₀ hp hU hneg
  obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hgt).eventually (Filter.eventually_gt_atTop C)).exists
  exact absurd (hentry m) (not_le.2 hm)

theorem UpperTheory.Gal.Gen.maxCpt_pf :
    UpperTheory.Gal.Gen.MaxCpt := by
  intro E _ _ w a H Z hZ hHZ hKH g hg
  obtain ⟨hK, hU, -⟩ := UpperTheory.V.Af.Smo.sphDict E a w
  obtain ⟨μ, -, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul (w.adicCompletion E) a g
  rw [hK] at hk₁ hk₂
  have hD : Cartan.diagPow (w.adicCompletion E) a μ ∈ H := by
    have h := H.mul_mem (H.mul_mem (H.inv_mem (hKH hk₁)) hg) (H.inv_mem (hKH hk₂))
    simpa [mul_assoc] using h
  have hinv : Cartan.diagPow (w.adicCompletion E) a (-μ) = (Cartan.diagPow (w.adicCompletion E) a μ)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
    rw [Units.val_mul, Cartan.coe_diagPow, Cartan.coe_diagPow, Matrix.diagonal_mul_diagonal, Units.val_one,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ (Cartan.uniformizer_ne_zero _)]
    simp
  have hn := norm_unif_lt_one E w hU
  have h1 := nonneg_of_pow_mem E w a hn hZ μ fun m => hHZ (H.pow_mem hD m)
  have h2 := nonneg_of_pow_mem E w a hn hZ (-μ) fun m => hHZ (hinv ▸ H.pow_mem (H.inv_mem hD) m)
  have hμ : μ = 0 := by
    funext i
    have := h1 i
    have := h2 i
    simp only [Pi.neg_apply] at *
    simp only [Pi.zero_apply]
    omega
  have hone : Cartan.diagPow (w.adicCompletion E) a μ = 1 := by
    refine Units.ext ?_
    rw [Cartan.coe_diagPow, hμ]
    simp
  rw [hone, mul_one]
  exact (GlobalTheory.LFun.KGL w a).mul_mem hk₁ hk₂
