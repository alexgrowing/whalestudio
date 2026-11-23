import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeLinearRootSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormConstantDivisorLocalHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRootUnitSectionAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCurveFiniteFieldPlaceStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.ArDegIndep.TieOther

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertDegHT

theorem topSelf_comb_root_eq_zero : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (B : ℝ), 2 ≤ B → ∀ (c : O.s.Comp) (W : O.LatModel (GlobalTheory.FlagAr.setB O.Y B) c) (τ : D.what₂.Tau)
    (Z : Scheme.{0}) (i : Z ⟶ W.V.X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → ringChar κ ∈ GlobalTheory.FlagAr.setB O.Y B → topSelfIntersection κ ((comb (W.gens (GlobalTheory.FlagAr.setB O.Y B)) (fun o : Option (D.what₂.Tau × Fin O.N) => o.elim (0 : ℤ) fun x => if x.1 = τ then (-1 : ℤ) else 0)).B.pull i) 1 = 0 := by
  intro hP hH hSW D O hO hf B hB c W τ Z i _ _ κ _ _ _ hd hp
  have hG : ∀ o : Option (D.what₂.Tau × Fin O.N), Norms W.V (W.gens (GlobalTheory.FlagAr.setB O.Y B) o)
      (o.elim (fun y => genAt (O.met.ab c).D y ^ W.k) fun x y => (genAt (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).D y ^ 1)⁻¹)
      (o.elim (fun σ y => (W.k : ℝ) * lnAdl (O.met.ab c) σ y) fun x σ y => -((1 : ℕ) * lnAdl (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x) σ y))
      (o.elim (fun v e y => (W.k : ℝ) * (O.met.ab c).lg v e y) fun x v e y => -((1 : ℕ) * (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).lg v e y)) := by
    rintro (_ | x)
    · exact norms_of_induces W.amp_spec
    · exact Norms.dual _ _ _ _ _ _ _ (norms_of_induces (Setup.induces_root0 D O hO.dualRef (GlobalTheory.FlagAr.setB O.Y B) c W (GlobalTheory.FlagAr.setB O.Y B) le_rfl x))
  have hN := norms_prod hG (fun o : Option (D.what₂.Tau × Fin O.N) => o.elim (0 : ℤ) fun x => if x.1 = τ then (-1 : ℤ) else 0)
  have hN' := hN.congr (f' := fun y => ∏ x : D.what₂.Tau × Fin O.N, if x.1 = τ then genAt (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).D y else 1)
    (a' := _) (l' := fun v e y => ∑ x : D.what₂.Tau × Fin O.N, if x.1 = τ then (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) x).lg v e y else 0)
    (fun y => ?_) (fun _ _ => rfl) (fun v e y => ?_)
  rotate_left
  · rw [Fintype.prod_option]
    simp only [Option.elim, zpow_zero, one_mul]
    refine Finset.prod_congr rfl fun x _ => ?_
    split_ifs <;> simp
  · rw [Fintype.sum_option]
    simp only [Option.elim, Int.cast_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  haveI := Fintype.ofFinite κ
  have hpr : (ringChar κ).Prime := CharP.char_is_prime κ (ringChar κ)
  obtain ⟨v, hpv, hZv⟩ := GlobalTheory.T.integral_curve_finite_field_place D.what₂.LL W.V.X Z W.V.p i κ
  obtain ⟨σ, hσ, C, hC⟩ := GlobalTheory.T.flag_root_unit_section_at_prime hP hH hSW D O hO hf B hB c τ v (ringChar κ) hpr hpv hp
  exact GlobalTheory.T.norm_constant_divisor_local_height D.what₂.LL (O.var c) W.V _ _ _ _ hN' σ hσ v C hC Z i κ hd hZv

end GlobalTheory.VertDegHT
