import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftPow

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS

private theorem exPow (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : ∃ ν : ℂ → HChar E,
    ∀ z v, (ν z).UnrAt v ∧ ((ν z).val v : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-z) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ → HChar E, ∀ t, (a t).IsAbsPow t :=
    ⟨UnitExponent.nu E, fun t => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) t⟩
  obtain ⟨b, hb, -⟩ := norm_exponent_equality E
  refine ⟨fun z => a z.re * b z.im, fun z v => ⟨fun x hx => ?_, ?_⟩⟩
  · rw [HChar.loc_mul, (ha _).1 v x hx, (hb _ v).1 x hx, one_mul]
  · have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    rw [HChar.val_mul, Units.val_mul, (ha _).2.1 v, (hb _ v).2, ← Complex.cpow_add _ _ h0, ← neg_add, Complex.re_add_im]

theorem UpperTheory.ConvolutionTheory.T.famSat :
    UpperTheory.ConvolutionTheory.T.FamSat := by
  intro K _ _ _ n b S _ Λ t h
  obtain ⟨lam, m, B, hAt, -, ht⟩ := h
  obtain ⟨ν, hν⟩ := exPow K
  choose π hπ using fun i => (UpperTheory.ConvolutionTheory.Dp.exCusp K (b.d i) (b.μ i) (b.V i) (b.summand i)).exists
  refine ⟨fun i => (CG.mk (π i)).twist (ν (lam i)), fun w hw => ?_⟩
  choose B' hB' hs using fun i =>
    (UpperTheory.ConvolutionTheory.Dp.sSatIff K (b.d i) (b.μ i) (π i) (b.V i) (hπ i) w (B i w)).1 ((hAt i).2 w hw)
  refine ⟨_, ⟨fun i => (B' i).map (· * (ν (lam i)).val w),
    fun i => satake_twist_holds K _ _ (ν (lam i)) w _ (hν _ _).1 (hs i), rfl⟩, ?_⟩
  rw [ht w hw]
  refine Eq.trans ?_ (map_sum (Multiset.mapAddMonoidHom (fun z : ℂˣ => (z : ℂ))) _ Finset.univ).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hB' i, Multiset.map_map, (hν _ _).2]
