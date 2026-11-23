import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamParts
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftPow

open MeasureTheory NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T

private theorem pow_loc {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]
  exact h _

private theorem pow_val {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = (normV v : ℂ) ^ (-s) := by
  refine ⟨fun x hx => Units.ext ?_, ?_⟩
  · have hx' : Valued.v (x : v.adicCompletion K) = 1 := hx
    rw [pow_loc h, FinitePlace.norm_def, hx']
    simp
  · have hx' : Valued.v ((atFin v (unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
      unif_spec v
    refine (pow_loc h v (atFin v (unif v))).trans ?_
    rw [FinitePlace.norm_def, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    have e : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
    have e' : normV v = Ideal.absNorm v.asIdeal := rfl
    rw [e, e', zpow_neg_one, NNReal.coe_inv, Complex.ofReal_inv, NNReal.coe_natCast, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

private theorem bc_twist {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsTotallyComplex K]
    [IsTotallyComplex M] {ν : HChar K} {ν' : HChar M} {z : ℂ} (hν : IsPow ν z) (hν' : IsPow ν' z) {n : ℕ} (π : CG K n)
    {ι : Type} [Fintype ι] {m : ι → ℕ} (P : ∀ i, CG M (m i)) (h : WeakBC π.HasSat (R.sumSat P)) :
    WeakBC (π.twist ν).HasSat (R.sumSat fun i => (P i).twist ν') := by
  refine Filter.Eventually.mono h fun w hw f hf => ?_
  obtain ⟨B, hB, B', hB', e⟩ := hw f hf
  have hv : ν'.val w = ν.val (w.under (𝓞 K)) ^ f := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, (pow_val hν _).2, (pow_val hν' _).2, hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
      Complex.natCast_cpow_natCast_mul]
  refine ⟨_, satake_twist_holds K n π ν _ B (pow_val hν _).1 hB, fun i => (B' i).map (· * ν'.val w),
    fun i => satake_twist_holds M _ (P i) ν' w _ (pow_val hν' _).1 (hB' i), ?_⟩
  refine Eq.trans ?_ (map_sum (Multiset.mapAddMonoidHom (· * ν'.val w)) B' Finset.univ)
  rw [← e]
  simp [Multiset.map_map, hv, mul_pow]

theorem UpperTheory.ConvolutionTheory.T.liftStep :
    UpperTheory.ConvolutionTheory.T.CoreLift → UpperTheory.ConvolutionTheory.T.LiftStep := by
  intro hC F E _ _ _ _ _ _ _ _ σ hσ hp n hn hlow π
  let μF : Measure (normOneGL F n) := Measure.haar
  let μE : Measure (normOneGL E n) := Measure.haar
  obtain ⟨χ, ⟨s, hχ⟩, V, hV⟩ := Dp.exTwist F n μF π hn
  obtain ⟨hex, hpw⟩ := powTwist F E
  obtain ⟨χ', hχ'⟩ := (hex s).2
  obtain ⟨hi, hi', hrest⟩ := hpw s χ χ' hχ hχ'
  have hback := (hrest n hn).1 π
  obtain ⟨-, -, hrest'⟩ := hpw (-s) χ⁻¹ χ'⁻¹ hi hi'
  obtain ⟨-, -, hL, hCj, -⟩ := hrest' n hn
  obtain ⟨c1, -, c3, c4, -, θ, hθ, c6⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, hAt⟩ := c1 V hV.summand
  by_cases hO : OffAll F n (bcInf (K := E) Λ) (bcSat t)
  · obtain ⟨V', hV', hst, hAt'⟩ := hC F E σ hσ hp n hn μE μF θ hθ V Λ t hV.summand hAt hO
    obtain ⟨P, hP, -⟩ := Dp.exCusp E n μE V' hV'
    have h1 := hL _ _ (c3 _ P V V' Λ t _ _ hV hP hAt hAt' rfl (Filter.Eventually.of_forall fun _ => rfl))
    rw [hback] at h1
    exact Or.inr ⟨_, h1, fun g => hCj _ _ ((c6 P V' hP).2 hst g)⟩
  · obtain ⟨ι, _, m, Q, hm, hι, hW⟩ := c4 _ V Λ t hV hAt (famParts F E σ hσ hp n hn hlow _ _ hO)
    refine Or.inl ⟨ι, inferInstance, m, fun i => (Q i).twist χ'⁻¹, hm, hι, ?_⟩
    have h1 := bc_twist hi hi' _ Q hW
    have e : (CG.mk (π.twist χ)).twist χ⁻¹ = CG.mk π := congrArg CG.mk hback
    rwa [e] at h1
