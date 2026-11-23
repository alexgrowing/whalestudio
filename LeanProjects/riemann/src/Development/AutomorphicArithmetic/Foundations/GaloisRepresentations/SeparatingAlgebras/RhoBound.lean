import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.rhoBound_pf :
    UpperTheory.Gal.Gen.DegLe → UpperTheory.Gal.Gen.BlockBound → UpperTheory.Gal.Gen.DetBound → UpperTheory.Gal.Gen.SizeLe → UpperTheory.Gal.Gen.RhoBound := by
  intro hdeg hblk hdet hsize E _ _ _ l _ ι a W A R hR hA x hx m
  have hx' : (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ).totalDegree
      ≤ ∑ τ, ∑ i, (W τ).natW i := hdeg (InfinitePlace E) a W x x.2
  have hb := hblk l ι (InfinitePlace E) a (fun τ => ((A τ : Matrix (Fin a) (Fin a) ℂ)).transpose) R hR
    (fun τ i j => (hA τ j i).1) _ x hx' hx m
  have hd := hdet l ι (InfinitePlace E) a W A R hR hA
  have hs := hsize E a W
  have hcoe : (((Formalism.L2.DIV.rhoK W) A) x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ)
      = Formalism.L2.DIV.detTwK W A • Formalism.L2.DIV.trAct A (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ) := rfl
  rw [hcoe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, norm_mul]
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  calc ‖ι.symm (Formalism.L2.DIV.detTwK W A)‖ * ‖ι.symm (MvPolynomial.coeff m (Formalism.L2.DIV.trAct A (x : MvPolynomial _ ℂ)))‖
      ≤ R ^ (∑ τ, a * (W τ).detShift.natAbs) * R ^ (∑ τ, ∑ i, (W τ).natW i) :=
        mul_le_mul hd hb (norm_nonneg _) (pow_nonneg hR0 _)
    _ = R ^ (∑ τ, ∑ i, (W τ).natW i + ∑ τ, a * (W τ).detShift.natAbs) := by
        rw [← pow_add, add_comm]
    _ ≤ R ^ (a * GlobalTheory.CongW.wtSize W.at) := pow_le_pow_right₀ hR hs
