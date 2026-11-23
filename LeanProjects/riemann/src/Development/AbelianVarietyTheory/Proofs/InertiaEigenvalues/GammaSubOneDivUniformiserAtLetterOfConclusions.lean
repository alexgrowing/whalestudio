import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.SemisimpleLetterIffForallMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachOperatorProductShiftMemLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsEqOfPowPredEqOfValOne
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.AdmDssLet

open Formalism.MainNotions.LiftingTheory

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem qp_isUnit (W : LocWach PD LL O v n) (hπu : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    IsUnit (algebraMap (LetA O n) W.EE (qp W)) := by
  have := W.EE_complete
  obtain ⟨u, hu⟩ := hπu
  have hj := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _
    (Ideal.mem_span_singleton_self ((PD.p : ℕ) : W.EE)))) (↑u⁻¹ : W.EE)
  have e : algebraMap (LetA O n) W.EE (qp W) = (u : W.EE) * (((PD.p : ℕ) : W.EE) * ↑u⁻¹ + 1) := by
    rw [qp, map_add, ← hu, map_natCast]
    rw [mul_add, mul_one, mul_comm ((PD.p : ℕ) : W.EE), ← mul_assoc, Units.mul_inv, one_mul, add_comm]
  rw [e]
  exact u.isUnit.mul hj

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [letE]
  · simp [letE, Pi.single_apply, hj]

theorem letter_of_qp_pow_mem (W : LocWach PD LL O v n)
    (hqu : IsUnit (algebraMap (LetA O n) W.EE (qp W))) (T : LocLat G Qp LL O) (i : ZMod n) (Y : ℕ)
    (y : W.DD T) (hy : qp W ^ Y • y ∈ W.Nl T i) :
    (letE i : LetA O n) • y = y ∧ qp W ^ Y • y ∈ W.N T := by
  obtain ⟨m, hm, hm'⟩ := Submodule.mem_map.1 hy
  have hm'' : (letE i : LetA O n) • m = qp W ^ Y • y := hm'
  have hqYu : IsUnit (algebraMap (LetA O n) W.EE (qp W ^ Y)) := by
    rw [map_pow]; exact hqu.pow _
  refine ⟨Formalism.MainNotions.UnusedSlot35.DssRec.smul_inj (E := W.EE) _ hqYu ?_, ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, ← hm'', smul_smul, letE_mul_self]
  · rw [← hm'']; exact (W.N T).smul_mem _ hm

theorem mem_Nl_of (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (a : LetA O n)
    (x : W.DD T) (hx : (letE i : LetA O n) • x = x) (hN : a • x ∈ W.N T) : a • x ∈ W.Nl T i := by
  refine Submodule.mem_map.2 ⟨_, hN, ?_⟩
  show (letE i : LetA O n) • (a • x) = a • x
  rw [smul_smul, mul_comm, ← smul_smul, hx]

theorem mem_xListL (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (M h y' Y : ℕ)
    (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ) (hτ : Over W τ i) (ha : IsJumpV PD T.ρ τ a)
    (hwin : a ∈ Set.Icc (-(M : ℤ)) (h : ℤ)) (hj1 : y' < j) (hj2 : j ≤ Y) :
    a + (j : ℤ) ∈ Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i M h y' Y := by
  unfold Formalism.MainNotions.RamifiedCoefficientChains.xListL
  rw [Finset.mem_sort, Finset.mem_image]
  refine ⟨(a, (j : ℤ)), ?_, rfl⟩
  rw [Finset.mem_product]
  refine ⟨?_, ?_⟩
  · classical
    unfold Formalism.MainNotions.RamifiedCoefficientChains.jumpSetL
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨hwin, τ, hτ, ha⟩
  · rw [Finset.mem_Icc]; constructor <;> push_cast <;> omega

end Gen

end GlobalTheory.AdmDssLet

namespace GlobalTheory

open GlobalTheory.AdmDssLet in

theorem adm18_of_N1used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.RamifiedCoefficientChains.adm18 D HW F := by
  intro D HW F Cm hN l _ K s LL h
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL h) := hN.2.2.2.2.2.2.2.2.1 l K s LL h
  rw [Formalism.MainNotions.UnusedSlot35.DssRec.dssLet_iff_mem _ h9]
  intro hA T Mi hi hT hJ ug hug hv cO hc i y' Y y₀ hyY hy hΔ seq h0 hrec
  have hs : s = 1 := ((HW l).W_s K s LL h).symm.trans hA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hA.2.2, h⟩
    obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
    have h2 := y.2.2
    have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
    rw [this] at h2
    exact h2

  have hgen : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have h1 := ((HW l).W K 1 LL h).gam_gen
    have h2 : ((((HW l).W K 1 LL h).s : ℕ) : WithTop ℚ) = 1 := by rw [hA.2.1]; rfl
    exact h1.trans h2
  have hug2 : ug ^ (l - 1) = (((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (l - 1) := by
    have e : ((D.loc l).PD K).p - 1 = l - 1 := congrArg (· - 1) hpl
    rw [← e]; exact hug
  have hug' : ug = ((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam :=
    GlobalTheory.units_eq_of_pow_pred_eq_of_val_one l (D.loc l) LL ug _ hug2 hv hgen
  subst hug'
  have hc' : ∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x =
      1 - (((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL)) := by
    intro x
    have e : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) = ((l : ℕ) : ↥(OL LL)) := congrArg _ hpl
    rw [← e]; exact hc x

  have hqu := qp_isUnit _ (Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit _ h9 hA T hT)
  obtain ⟨hey, hN0⟩ := letter_of_qp_pow_mem _ hqu T i Y y₀ hy
  have hDL0 : Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL h) T i (seq 0) := by
    rw [h0]; exact ⟨hey, hΔ⟩
  rw [← h0] at hN0
  obtain ⟨hDL, hmem⟩ := GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl T hT i y' Y cO hc'
    (Formalism.MainNotions.RamifiedCoefficientChains.xListL ((HW l).W K 1 LL h) T i (Mi i) (hi i) y' Y)
    (fun τ a j hτ ha hj1 hj2 => mem_xListL _ T i (Mi i) (hi i) y' Y τ a j hτ ha (hJ i τ hτ a ha) hj1 hj2)
    seq hDL0 hN0 hrec
  exact mem_Nl_of _ T i _ _ hDL.1 hmem

end GlobalTheory
