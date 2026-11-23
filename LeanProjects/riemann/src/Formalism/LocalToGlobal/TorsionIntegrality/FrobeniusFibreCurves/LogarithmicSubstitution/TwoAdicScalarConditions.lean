import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BiextensionFormalMulMul
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementI

noncomputable section

namespace Formalism.L2.Th1.B.Van

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (IsLogPair mulBy EndInt PhNormAt IsBinomScalar FGInt LG)

theorem Th0Vanish_of (hC : CubeE) (hN : PhENorm) : ThetaZeroVanishing := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT al albar S P l linv i ep F ι _ xQ wp wm hP hL hI hlp hCu
    hCu3 hT hQ hFib hN1 hS hEnd hcl h0 hne h1 hb1 hb2
  have hl0 : PowerSeries.constantCoeff l = 0 := hL.2.2.1
  obtain ⟨hc0, hth⟩ :=
    phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl0
  obtain ⟨-, -, hd1, -⟩ := hC K g2 g3 s2 c0 a1 a3 xT yT P l i ep F hP hL hI hCu hCu3 hT
  obtain ⟨-, hFG, hF1⟩ := Formalism.L2.Th1.C.first_level_from_universal_law K F l linv _ hlp hL hc0 hd1
  have hPN := hN K g2 g3 s2 c0 xT al albar S P l linv i ep F ι xQ wp wm hP hT.2.1 hlp hCu
    hT.2.2.1 hQ hFib hN1 hS
  have hLG : LG (unitBall K) (phTw g2 s2 c0 xT P l) :=
    Split.split_vanishing_at_two K (unitBall K) (Formalism.L2.Th1.C.unitBallClosed K) l linv _ al albar
      ⟨hlp, hFG, hc0⟩ hF1 hEnd hcl hPN h0 hne h1 hb1 hb2
  have hth' : PowerSeries.subst l (thTw g2 s2 c0 xT P) = fExp (-phTw g2 s2 c0 xT P l) := hth
  have hneg : LG (unitBall K) (-phTw g2 s2 c0 xT P l) :=
    (Formalism.L2.Th1.C.lGSubgroup K (unitBall K) Unit).2.2 _ hLG
  refine ⟨?_, ?_, ?_⟩
  · refine (Formalism.L2.Th1.C.simeqIffCong K Unit _ _).2 ?_
    rw [Formalism.L2.Th1.C.Cong, sub_zero]
    exact hLG
  · rw [hth']
    exact constantCoeff_fExp hneg.1
  · rw [hth']
    exact hneg.2

section Two

variable {K : Type} [NormedField K] [NormedAlgebra ℚ_[2] K]

def phi (K : Type) [NormedField K] [NormedAlgebra ℚ_[2] K] : ℤ_[2] →+* K :=
  (algebraMap ℚ_[2] K).comp PadicInt.Coe.ringHom

theorem phi_apply (x : ℤ_[2]) : phi K x = algebraMap ℚ_[2] K (x : ℚ_[2]) := rfl

theorem continuous_phi : Continuous (phi K) := by
  exact (continuous_algebraMap ℚ_[2] K).comp continuous_subtype_val

theorem phi_mem_closure (x : ℤ_[2]) : phi K x ∈ closure (Set.range (fun n : ℤ => (n : K))) := by
  have hd : DenseRange (Int.cast : ℤ → ℤ_[2]) := PadicInt.denseRange_intCast
  have h1 : x ∈ closure (Set.range (Int.cast : ℤ → ℤ_[2])) := by rw [hd.closure_eq]; trivial
  refine map_mem_closure continuous_phi h1 ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by rw [map_intCast]⟩

theorem phi_mem_of_closed {s : Set K} (hs : IsClosed s) (hn : ∀ n : ℤ, (n : K) ∈ s) (x : ℤ_[2]) :
    phi K x ∈ s := closure_minimal (Set.range_subset_iff.mpr hn) hs (phi_mem_closure x)

theorem phi_injective : Function.Injective (phi K) := (algebraMap ℚ_[2] K).injective.comp Subtype.val_injective

theorem phi_inv {x : ℤ_[2]} (hx : ‖x‖ = 1) : ∃ y : ℤ_[2], (phi K x)⁻¹ = phi K y := by
  obtain ⟨u, rfl⟩ := PadicInt.isUnit_iff.mpr hx
  exact ⟨((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), by rw [map_units_inv]⟩

end Two

theorem norm_sub_eq_one {b b' : ℤ_[2]} (hb : ‖b‖ = 1) (hb' : ‖b'‖ < 1) : ‖b - b'‖ = 1 := by
  have h1 : ‖b - b'‖ ≤ max ‖b‖ ‖b'‖ := by
    have h3 := PadicInt.nonarchimedean b (-b')
    rwa [norm_neg, ← sub_eq_add_neg] at h3
  have h2 : ‖b‖ ≤ max ‖b - b'‖ ‖b'‖ := by
    have h3 := PadicInt.nonarchimedean (b - b') b'
    rwa [sub_add_cancel] at h3
  rw [hb] at h1 h2
  rcases le_total ‖b - b'‖ ‖b'‖ with h | h
  · rw [max_eq_right h] at h2
    linarith
  · rw [max_eq_left (by linarith)] at h1
    rw [max_eq_left h] at h2
    linarith

theorem endInt_int {K : Type} [Field K] (R : Subring K) {l linv : PowerSeries K}
    (h : IsLogPair l linv) (hF : FGInt R l linv) (n : ℤ) : EndInt R l linv (n : K) := by
  obtain ⟨-, -, h0, h1, hm, hadd, -⟩ := Formalism.L2.Th1.C.ptClosure K R l linv h hF
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ n ih =>
    have := hadd _ _ ih h1
    simpa using this
  | pred n ih =>
    have := hadd _ _ ih hm
    simpa [sub_eq_add_neg] using this

theorem two_adic_scalar_conditions : TwoAdicScalars := by
  intro K _ _ _ _ F l linv b b' hL hlp hb hb' al albar
  have hcl := Formalism.L2.Th1.C.unitBallClosed K
  have hFG : FGInt (unitBall K) l linv := by
    rw [FGInt, ← Formalism.L2.Th1.C.Dict.law_eq hlp hL.1 hL.2.2.2.2]
    exact hL.2.1
  have hbin : ∀ x : ℤ_[2], IsBinomScalar (unitBall K) (phi K x) :=
    phi_mem_of_closed (Formalism.L2.Th1.C.binomClosed K (unitBall K) hcl)
      (Formalism.L2.Th1.C.intBinomScalar K (unitBall K))
  have hal : al = phi K b := rfl
  have halb : albar = phi K b' := rfl
  have h1b' : ‖(1 : ℤ_[2]) - b'‖ = 1 := norm_sub_eq_one norm_one hb'
  have hbb' : ‖b - b'‖ = 1 := norm_sub_eq_one hb hb'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact phi_mem_of_closed (Formalism.L2.Th1.C.endIntClosed K (unitBall K) hcl l linv hlp.1)
      (endInt_int (unitBall K) hlp hFG) b
  · exact phi_mem_closure b
  · rw [hal, ← map_zero (phi K)]
    intro h
    have := phi_injective h
    rw [this, norm_zero] at hb
    exact zero_ne_one hb
  · rw [hal, halb]
    intro h
    have := phi_injective h
    rw [this] at hb
    exact hb'.ne hb
  · rw [halb, ← map_one (phi K)]
    intro h
    have := phi_injective h
    rw [this, norm_one] at hb'
    exact lt_irrefl _ hb'
  · have e : al * (al - albar) = phi K (b * (b - b')) := by
      rw [hal, halb, map_mul, map_sub]
    obtain ⟨y, hy⟩ := phi_inv (K := K) (x := b * (b - b')) (by rw [norm_mul, hb, hbb', one_mul])
    rw [e, hy]
    exact hbin y
  · have e : al * (1 - albar) = phi K (b * (1 - b')) := by
      rw [hal, halb, map_mul, map_sub, map_one]
    obtain ⟨y, hy⟩ := phi_inv (K := K) (x := b * (1 - b')) (by rw [norm_mul, hb, h1b', one_mul])
    rw [e, hy]
    exact hbin y

end Formalism.L2.Th1.B.Van
