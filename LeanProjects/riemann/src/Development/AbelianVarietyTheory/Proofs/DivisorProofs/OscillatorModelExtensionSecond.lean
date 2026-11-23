import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMapExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFifthStatement

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SerAll

open NumberField Matrix Complex MeasureTheory IsDedekindDomain in
open scoped TensorProduct Classical ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

theorem _root_.GlobalTheory.AdTh.SerAll.lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) {x : ℝ} (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) :
    _root_.Formalism.L2.Pj.lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ _root_.GlobalTheory.PtId.degW Dw a := by
  have hy : 0 < 2 * Real.pi * x := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le, ← Real.rpow_natCast, ← Real.rpow_mul hy.le,
    Real.rpow_def_of_pos hy]
  unfold _root_.Formalism.L2.Pj.lieFac _root_.GlobalTheory.PtId.degW
  congr 1
  push_cast
  ring

set_option maxHeartbeats 1000000 in

theorem exists_serOf : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∃ u : ℂ, ‖u‖ = 1 ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 := by
  intro _ D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT hI i Tp tup O hP cc hcc
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨h1, h2, -⟩ := GlobalTheory.PtId.dict_cast T hT.laws _ (inR i) O.s0 (hs ▸ T.toCore.good_σ₀) (Wc D i) O.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.lattice_isometry_sign_third D G Pl0 T0 A _ R F hR i hP.lift.std _ _ (iotaW T i) h1 h2
  obtain ⟨ka, hka, hio⟩ := GlobalTheory.T.oscillator_model_extension_first D G Pl0 T0 A T R F κ v₀ hR hT hI i Tp tup O hP
  obtain ⟨c0, hc0, hcov⟩ := GlobalTheory.T.oscillator_model_values_fifth D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP
  have hd : ‖((δ : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> simp
  have hu : ‖ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹‖ = 1 := by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_inv, hka, hc0, hd]
    simp
  refine ⟨_, hu, fun k => ?_, norm_one, fun t h J' hrep y x hpl f _ hf g => ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, norm_mul, hu, hcc.1 k, one_mul]
  have hne : c0 ≠ 0 := norm_ne_zero_iff.1 (hc0 ▸ one_ne_zero)
  have hx : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have key := GlobalTheory.PtId.exact_identity hR hT O hP hio hδ hcov hcc t h J' hrep y x hpl f hf g
  refine mul_left_cancel₀ hne ?_
  rw [one_mul, key, lieFac_eq_pow _ hx, GlobalTheory.PtId.cmpConst, Pi.smul_apply, smul_eq_mul, neg_pow]
  have hre : rdU (GlobalTheory.PtId.unfO O) f (O.dict g).1 (O.dict g).2 =
      rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2 := rfl
  rw [hre]
  generalize rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2 = z
  rw [Complex.ofReal_pow, Complex.ofReal_inv]
  generalize ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) = s
  have e : c0 * c0⁻¹ = 1 := mul_inv_cancel₀ hne
  linear_combination (-(ka * ((-1) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * ((δ : ℤ) : ℂ) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * cc (O.dict g).1 * s * O.mu g * z)) * e

end GlobalTheory.AdTh.SerAll
