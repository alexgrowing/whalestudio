import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.TwReg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.SatConj
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem sat_twist {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CG E a)
    {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem algSat_shift {E : Type} [Field E] [NumberField E] (a n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    {χ : HChar E} (hχ : χ.IsAbsPow (((n : ℝ) - a) / 2)) (B : Multiset ℂˣ) :
    algSat n (Formalism.ConjugateSelfDual.normV w) (B.map (· * χ.val w)) = algSat a (Formalism.ConjugateSelfDual.normV w) B := by
  have h := hχ.2.1 w
  have hq : (0 : ℝ) < (Formalism.ConjugateSelfDual.normV w : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w : Formalism.ConjugateSelfDual.normV w ≠ 0)
  rw [algSat_eq, algSat_eq, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  rw [h]
  have e : Ideal.absNorm w.asIdeal = Formalism.ConjugateSelfDual.normV w := by
    first | rfl | exact Ideal.absNorm_apply _ | simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have e2 : ((a : ℝ) - 1) / 2 = ((n : ℝ) - 1) / 2 + -(((n : ℝ) - a) / 2) := by ring
  rw [e, e2, Real.rpow_add hq, Complex.ofReal_mul, Complex.ofReal_cpow hq.le (-_), Complex.ofReal_neg,
    Complex.ofReal_natCast]
  ring

theorem UpperTheory.V.Cj.blockConj :
    UpperTheory.V.Cj.BlockConj := by
  intro E _ _ _ a n hC π μ m h1 h2 h3 σ
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (((n : ℝ) - a) / 2)
  have hν' := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (((a : ℝ) - n) / 2)
  obtain ⟨π', hπ'⟩ := satConj E n hC _ (twReg E a n π μ m h1 h2 h3 _ hν) σ
  refine ⟨π'.twist (GlobalTheory.HeckeGal.Model.absPow E (((a : ℝ) - n) / 2)), fun w B hB => ?_⟩
  obtain ⟨B', b1, b2⟩ := hπ' w _ (sat_twist π hB (hν.1 w))
  refine ⟨_, sat_twist π' b1 (hν'.1 w), ?_⟩
  rw [algSat_shift n a w hν', b2, algSat_shift a n w hν]
