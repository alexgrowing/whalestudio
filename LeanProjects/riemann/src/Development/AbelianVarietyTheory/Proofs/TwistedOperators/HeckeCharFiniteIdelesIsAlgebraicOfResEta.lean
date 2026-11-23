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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Formalism.LocalToGlobal.UnitaryNorms.CharExGen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUniformiserValueIsAlgebraic
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

section Reformulated
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open IsDedekindDomain NumberField Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinValAlg

theorem isAlgebraic_unit_zpow {z : ℂ} (hz : IsAlgebraic ℚ z) (n : ℤ) :
    IsAlgebraic ℚ ((z / ((‖z‖ : ℝ) : ℂ)) ^ n) := by
  have hc : IsAlgebraic ℚ (starRingEnd ℂ z) := hz.algHom (starRingEnd ℂ).toRatAlgHom
  have hn : IsAlgebraic ℚ (((‖z‖ : ℝ) : ℂ)) := by
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [← Complex.conj_mul']
    exact (mem_algebraicClosure_iff.1 (mul_mem (mem_algebraicClosure_iff.2 hc) (mem_algebraicClosure_iff.2 hz)))
  rw [← mem_algebraicClosure_iff] at hz hn ⊢
  exact zpow_mem (div_mem hz hn) n

variable {D : D7}

theorem finPart_incA (e : D.host.E) : finPart D (incA D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e := by
  change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem int_of_val_eq_one (ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) (z : (AE D)ˣ)
    (hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (z : AE D)) P) = 1) :
    finPart D (z : AE D) ∈ intAE D ∧ finPart D ((z⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  refine ⟨(hι2 _).2 fun P => (hv P).le, (hι2 _).2 fun P => le_of_eq ?_⟩
  have e : ι (finPart D ((z⁻¹ : (AE D)ˣ) : AE D)) * ι (finPart D (z : AE D)) = 1 := by
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  have e2 : ι (finPart D ((z⁻¹ : (AE D)ˣ) : AE D)) P * ι (finPart D (z : AE D)) P = 1 := by
    have := congrArg (fun w : FiniteAdeleRing (𝓞 D.host.E) D.host.E => w P) e
    exact this
  have := congrArg Valued.v e2
  rwa [map_mul, hv, mul_one, map_one] at this

theorem ι_finPart_pow_mul (ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (x : (AE D)ˣ) (h : ℕ) (k : D.host.Eˣ) :
    ι (finPart D ((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D)) =
      ι (finPart D (x : AE D)) ^ h * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) := by
  have e : ((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D) = (x : AE D) ^ h * incA D (k : D.host.E) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  rw [e, map_mul, map_pow, map_mul, map_pow, finPart_incA, hι1]

theorem exists_pow_mul_int (x : (AE D)ˣ) : ∃ h : ℕ, 0 < h ∧ ∃ k : D.host.Eˣ,
    finPart D (((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ)) : AE D) ∈ intAE D ∧
    finPart D ((((x ^ h * Units.map (incA D).toMonoidHom k)⁻¹ : (AE D)ˣ)) : AE D) ∈ intAE D := by
  obtain ⟨ι, hι1, hι2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h, hh, hX⟩ := Formalism.L2.Host.CharEx.classExp D.host.E
  obtain ⟨a, a', haa, haa', ha⟩ : ∃ a a' : Af D.host.F ⊗[D.host.F] D.host.E, a * a' = 1 ∧ a' * a = 1 ∧
      a = finPart D (x : AE D) :=
    ⟨_, _, by rw [← map_mul, Units.mul_inv, map_one], by rw [← map_mul, Units.inv_mul, map_one], rfl⟩
  let X : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨((1 : InfiniteAdeleRing D.host.E), ι a), ((1 : InfiniteAdeleRing D.host.E), ι a'),
      Prod.ext (show (1 : InfiniteAdeleRing D.host.E) * 1 = 1 from mul_one _)
        (show ι a * ι a' = 1 by rw [← map_mul, haa, map_one]),
      Prod.ext (show (1 : InfiniteAdeleRing D.host.E) * 1 = 1 from mul_one _)
        (show ι a' * ι a = 1 by rw [← map_mul, haa', map_one])⟩
  obtain ⟨k, hk⟩ := hX X
  refine ⟨h, hh, k, int_of_val_eq_one ι hι2 _ fun P => ?_⟩
  rw [ι_finPart_pow_mul ι hι1, ← ha]
  have e : ((X ^ h * Neutral.B1.diagUnits D.host.E k : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      AdeleRing (𝓞 D.host.E) D.host.E).2 = ι a ^ h * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  rw [← e]
  exact hk P

end GlobalTheory.FinValAlg

namespace GlobalTheory.FinValAlg

variable {D : D7}

theorem infPart_incA (e : D.host.E) : infPart D (incA D e) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] e := by
  change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem infPart_pairE (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    infPart D (Formalism.L2.Fam.ThC.pairE a b) = a := Formalism.L2.Fam.ThC.fst_pairE a b

theorem finPart_pairE (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (Formalism.L2.Fam.ThC.pairE a b) = b := Formalism.L2.Fam.ThC.snd_pairE a b

theorem pairE_mul_eq_one (z : (AE D)ˣ) :
    Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 * Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 = 1 := by
  refine Formalism.L2.Fam.ThC.ae_ext ?_ ?_
  · rw [map_mul, infPart_pairE, infPart_pairE, ← map_mul, Units.mul_inv]
  · rw [map_mul, finPart_pairE, finPart_pairE, mul_one, map_one]

theorem pairE_mul_eq_one' (z : (AE D)ˣ) :
    Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 * Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 = 1 := by
  refine Formalism.L2.Fam.ThC.ae_ext ?_ ?_
  · rw [map_mul, infPart_pairE, infPart_pairE, ← map_mul, Units.inv_mul]
  · rw [map_mul, finPart_pairE, finPart_pairE, mul_one, map_one]

set_option maxHeartbeats 1000000 in

theorem exists_decomp (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) :
    ∃ h : ℕ, 0 < h ∧ ∃ (k : D.host.Eˣ) (y u : (AE D)ˣ), finPart D (y : AE D) = 1 ∧ Formalism.L2.Pj.FinUnit u ∧
      infPart D (y : AE D) = infPart D (incA D (k : D.host.E)) ∧ x ^ h * Units.map (incA D).toMonoidHom k = y * u := by
  obtain ⟨h, hh, k, h1, h2⟩ := exists_pow_mul_int x
  refine ⟨h, hh, k, ?_⟩
  generalize hz : x ^ h * Units.map (incA D).toMonoidHom k = z at h1 h2
  have hiz : infPart D (z : AE D) = infPart D (incA D (k : D.host.E)) := by
    rw [← hz, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hx, one_pow, one_mul]
    rfl
  have m1 := pairE_mul_eq_one z
  have m2 := pairE_mul_eq_one' z
  obtain ⟨y, hyv, hyi⟩ : ∃ y : (AE D)ˣ, (y : AE D) = Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 ∧
      ((y⁻¹ : (AE D)ˣ) : AE D) = Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 :=
    ⟨⟨_, _, m1, m2⟩, rfl, rfl⟩
  refine ⟨y, y⁻¹ * z, by rw [hyv, finPart_pairE], ⟨?_, ?_, ?_⟩, by rw [hyv, infPart_pairE, hiz], by rw [mul_inv_cancel_left]⟩
  · rw [Units.val_mul, map_mul, hyi, infPart_pairE, ← map_mul, Units.inv_mul, map_one]
  · rw [Units.val_mul, map_mul, hyi, finPart_pairE, one_mul]; exact h1
  · rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul, hyv, finPart_pairE, mul_one]; exact h2

theorem char_eq_prod {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle} (nτ : D.what₂.Tau → ℤ)
    (hn : ∀ τ (x : (AE D)ˣ), finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ nτ τ)
    (y : (AE D)ˣ) (hy : finPart D (y : AE D) = 1) :
    ((χ y : Circle) : ℂ) = ∏ τ, (θ τ (infPart D (y : AE D)) / (‖θ τ (infPart D (y : AE D))‖ : ℂ)) ^ nτ τ := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom hσ
  let wU : D.what₂.Tau → ℂˣ := fun τ => (y.isUnit.map ((θ τ).comp (infPart D))).unit
  have hwU : ∀ τ, ((wU τ : ℂˣ) : ℂ) = θ τ (infPart D (y : AE D)) := fun τ => rfl
  let f : (D.what₂.Tau → ℂ)ˣ →* (AE D)ˣ := Units.map e
  have hf1 : ∀ W, finPart D ((f W : (AE D)ˣ) : AE D) = 1 := fun W => e1 _
  have hf2 : ∀ W τ, θ τ (infPart D ((f W : (AE D)ˣ) : AE D)) = (W : D.what₂.Tau → ℂ) τ := fun W τ => e2 _ τ
  have hy' : y = ∏ τ, f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ))) := by
    rw [← map_prod, ← map_prod, Finset.univ_prod_mulSingle]
    apply Units.ext
    refine GlobalTheory.SplitCharExp.ext_of_chart hσ (by rw [hy, hf1]) fun τ => ?_
    rw [hf2]
    exact (hwU τ).symm
  have hc : ((χ y : Circle) : ℂ) = ∏ τ, ((χ (f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ)))) : Circle) : ℂ) := by
    show Circle.coeHom (χ y) = ∏ τ, Circle.coeHom (χ (f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ)))))
    rw [← map_prod, ← map_prod, ← hy']
  rw [hc]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hs : ∀ τ', θ τ' (infPart D ((f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ))) : (AE D)ˣ) : AE D)) =
      (((Pi.mulSingle τ (wU τ) : D.what₂.Tau → ℂˣ) τ' : ℂˣ) : ℂ) := fun τ' => by rw [hf2]; rfl
  rw [hn τ _ (hf1 _) fun τ' h => by rw [hs, Pi.mulSingle_eq_of_ne h, Units.val_one], hs, Pi.mulSingle_eq_same, hwU]

theorem isAlgebraic_of_infPart_eq_one : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ},
    IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) := by
  intro D θ χ n hθ hχ hr x hx
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ n τ hθ hχ hr
  choose nτ hn2 hn using ha
  have hn' : ∀ τ (x : (AE D)ˣ), finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ nτ τ :=
    fun τ => (hn τ).2 θ hθ
  obtain ⟨h, hh, k, y, u, hy1, hu, hyi, e⟩ := exists_decomp x hx
  obtain ⟨-, -, -, m, hm, hum⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ.1
  have hyalg : IsAlgebraic ℚ ((χ y : Circle) : ℂ) := by
    rw [char_eq_prod hθ nτ hn' y hy1, ← mem_algebraicClosure_iff]
    refine prod_mem fun τ _ => ?_
    rw [mem_algebraicClosure_iff, hyi, infPart_incA, (hθ τ).1]
    exact isAlgebraic_unit_zpow (GlobalTheory.isAlgebraic_embedding_apply _ _) _
  have e2 : χ x ^ (h * m) = χ y ^ m := by
    have := congrArg (fun g => χ g ^ m) e
    simp only [map_mul, mul_pow, hum u hu, mul_one, hχ.2 k, one_pow, map_pow] at this
    rw [pow_mul]
    exact this
  refine IsAlgebraic.of_pow (Nat.mul_pos hh hm) ?_
  rw [← Circle.coe_pow, e2, Circle.coe_pow, ← mem_algebraicClosure_iff]
  exact pow_mem (mem_algebraicClosure_iff.2 hyalg) _

end GlobalTheory.FinValAlg

end

end Reformulated

theorem GlobalTheory.FinValAlg.finite_values_isAlgebraic : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ}, IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) :=
  GlobalTheory.FinValAlg.isAlgebraic_of_infPart_eq_one
