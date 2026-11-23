import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SplitParity

theorem exists_eq_of_sigR_fixed {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (z : R ⊗[F] E) (hz : sigR R σ z = z) : ∃ r : R, algebraMap R (R ⊗[F] E) r = z := by
  obtain ⟨δ, b, -, hb0, hb1, -⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hr hσ hne
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have hz' := B.sum_repr z
  rw [Fin.sum_univ_two] at hz'
  set x := B.repr z 0
  set y := B.repr z 1
  have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
    rw [map_add, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
      map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
  rw [← hz', e] at hz
  have h2 : (2 * y) • B 1 = 0 := by
    have : x • B 0 - y • B 1 - (x • B 0 + y • B 1) = 0 := by rw [hz, sub_self]
    rw [two_mul, add_smul]
    linear_combination (-1 : R ⊗[F] E) * this
  have h3 : 2 * y = 0 := by
    have := congrArg (fun w => B.repr w 1) h2
    simpa using this
  have h4 : y = 0 := by
    have hu : (2 : R) * algebraMap F R (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
    calc y = algebraMap F R (1 / 2) * (2 * y) := by linear_combination (-y) * hu
      _ = 0 := by rw [h3, mul_zero]
  refine ⟨x, ?_⟩
  rw [← hz', h4, zero_smul, add_zero, h0, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.SplitParity

namespace GlobalTheory.SplitParity

theorem exists_idF_of_fixed (D : D7) (u : (AE D)ˣ) (hu : cA D (u : AE D) = u) : ∃ y, idF D y = u := by
  have hfx : ∀ z : AE D, cA D z = z → ∃ r : AF D.host.F, algebraMap (AF D.host.F) (AE D) r = z := fun z hz =>
    exists_eq_of_sigR_fixed D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x)
      (GlobalTheory.VolHeckeCompare.exists_not_fixed D) z hz
  obtain ⟨r, hr⟩ := hfx _ hu
  have hu' : cA D ((u⁻¹ : (AE D)ˣ) : AE D) = ((u⁻¹ : (AE D)ˣ) : AE D) := by
    have h1 : (u : AE D) * cA D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := by
      rw [← hu, ← map_mul, Units.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h1).symm
  obtain ⟨r', hr'⟩ := hfx _ hu'
  have m1 : r * r' = 1 := GlobalTheory.VolHeckeCompare.algebraMap_AE_injective D (by
    rw [map_mul, hr, hr', Units.mul_inv, map_one])
  refine ⟨⟨r, r', m1, by rw [mul_comm]; exact m1⟩, Units.ext ?_⟩
  exact hr

theorem exists_int_add_half : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau) (a : ℚ),
    IsHeckeChar D χ → ResEta D χ n → HasInfExp D χ τ a → ∃ e : ℤ, (e : ℚ) = a + (n : ℚ) / 2 := by
  intro D χ n τ a _ hr ha
  classical
  obtain ⟨N, hN, ⟨θ, hθ⟩, hχ⟩ := ha
  obtain ⟨η, -, -, hη1, hη2⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨N1, hN1, -, hηx⟩ := hη2 τ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw
  have wτ : w τ = -1 := by simp [w]
  have wo : ∀ τ', τ' ≠ τ → w τ' = 1 := fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]
  have ww : w * w = 1 := by
    funext τ'
    by_cases ht : τ' = τ
    · subst ht; simp [wτ]
    · simp [wo τ' ht]
  let x : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have x1 : finPart D (x : AE D) = 1 := e1 w
  have x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ' := e2 w
  have xτ : θ τ (infPart D (x : AE D)) = -1 := by rw [x2, wτ]
  have xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' ht => by rw [x2, wo τ' ht]
  have hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N := by rw [hχ θ hθ x x1 xo, xτ]; simp
  have hN1' : N1 = 1 := by
    have : (N1 : ℚ) = 1 := by rw [hN1]; norm_num
    exact_mod_cast this
  have hηc : ((η x : Circle) : ℂ) = -1 := by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp
  have hfix : cA D (x : AE D) = x := by
    refine GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
      rw [e3, x1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, x2]
      by_cases ht : τ' = τ
      · rw [ht, wτ]; simp
      · rw [wo τ' ht]; simp
  obtain ⟨y, hy⟩ := exists_idF_of_fixed D x hfix
  obtain ⟨⟨ε, hε⟩, hrχ⟩ := hr
  have c1 := hrχ ε hε y
  have c2 := hη1.2 ε hε y
  rw [hy] at c1 c2
  have c2' : ((ε y : Circle) : ℂ) = -1 := by rw [← hηc, c2, pow_one]
  have c1' : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ n := by rw [c1, Circle.coe_pow, c2']
  have hE : (-1 : ℂ) ^ N = (-1 : ℂ) ^ (n : ℤ) := by rw [← hcx, c1', zpow_natCast]
  have hP : (-1 : ℂ) ^ (N + (n : ℤ)) = 1 := by
    rw [zpow_add₀ (by norm_num), hE, ← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  rcases Int.even_or_odd (N + (n : ℤ)) with ⟨k, hk⟩ | ho
  · refine ⟨k, ?_⟩
    have : ((N + (n : ℤ) : ℤ) : ℚ) = ((k + k : ℤ) : ℚ) := by rw [hk]
    push_cast at this
    linarith
  · rw [ho.neg_one_zpow] at hP
    norm_num at hP

end GlobalTheory.SplitParity
