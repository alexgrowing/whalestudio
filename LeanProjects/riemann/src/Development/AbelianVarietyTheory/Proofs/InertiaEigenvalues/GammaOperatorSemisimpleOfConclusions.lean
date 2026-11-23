import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.SemisimpleLetterIffForallMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachOperatorProductShiftMemLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsEqOfPowPredEqOfValOne

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

section LetterAux

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem γD_letE_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) : W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]
  congr 1
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem sum_letE_eq_one [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem le_Mmax_of [NeZero n] (Mi : ZMod n → ℕ) (i : ZMod n) : Mi i ≤ Formalism.MainNotions.LiftingTheory.Mmax n Mi := by
  have h := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n)) (Finset.mem_range.2 (ZMod.val_lt i))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem smul_letE_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (a : LetA O n)
    (x : W.DD T) (hx : a • x ∈ W.N T) : a • ((letE i : LetA O n) • x) ∈ W.N T := by
  rw [smul_smul, mul_comm, ← smul_smul]
  exact (W.N T).smul_mem _ hx

theorem letE_rec (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (c : O)
    (y z : W.DD T) (h : W.π₀ • (y + c • z) = W.γD T W.gam z - z) :
    W.π₀ • ((letE i : LetA O n) • y + c • ((letE i : LetA O n) • z)) =
      W.γD T W.gam ((letE i : LetA O n) • z) - (letE i : LetA O n) • z := by
  rw [smul_comm c (letE i : LetA O n) z, ← smul_add, smul_smul, mul_comm W.π₀, ← smul_smul, h,
    smul_sub, γD_letE_smul]

theorem mem_N_of_letE [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : ∀ i : ZMod n, (letE i : LetA O n) • x ∈ W.N T) : x ∈ W.N T := by
  have e : x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE_eq_one, one_smul]
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => h i)

theorem mem_of_qp_pow_zero (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : Formalism.MainNotions.LiftingTheory.qp W ^ 0 • x ∈ W.N T) : x ∈ W.N T := by
  rwa [pow_zero, one_smul] at h

end LetterAux

theorem dss_semisimple_of_used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.LiftingTheory.adm19 D HW F := by
  intro D HW F Cm hN l _ K s LL h
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL h) := hN.2.2.2.2.2.2.2.2.1 l K s LL h
  rw [Formalism.MainNotions.UnusedSlot35.DssRec.coreDss_iff_mem _ h9]
  intro hA T Mi hi hT hJ ug hug hv cO hc Y y₀ hy hΔ seq h0 hrec
  subst h0
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
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hw1 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL h).gam_gen
    rw [hA.2.1, Nat.cast_one] at this
    exact this
  have hug1 : ug ^ (l - 1) = (((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (l - 1) := by
    have := hug
    rw [hpl] at this
    exact this
  have hug' : ug = ((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam :=
    GlobalTheory.units_eq_of_pow_pred_eq_of_val_one l (D.loc l) LL ug _ hug1 hv hw1
  have hc' : ∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - ((((((HW l).W K 1 LL h).χΓ
      ((HW l).W K 1 LL h).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) := by
    intro x
    have := hc x
    rw [hpl, hug'] at this
    exact this
  have hjx : ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ),
      Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL h) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → 0 < j → j ≤ Y →
      a + (j : ℤ) ∈ Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y := by
    intro i τ a j hO hjump hj0 hjY
    have ha := hJ i τ hO a hjump
    have hM := le_Mmax_of Mi i
    have hH := le_Mmax_of hi i
    rw [Formalism.MainNotions.LiftingTheory.xList, Finset.mem_sort, Finset.mem_image]
    refine ⟨(a, (j : ℤ)), Finset.mem_product.2 ⟨?_, ?_⟩, rfl⟩
    · simp only [Formalism.MainNotions.LiftingTheory.jumpSet, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, τ, hjump⟩
      · have := ha.1; omega
      · have := ha.2; omega
    · rw [Finset.mem_Icc]; omega
  have hmem : ∀ i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)),
      (letE i : LetA ↥(OL LL) _) • seq (Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y).length ∈ ((HW l).W K 1 LL h).N T := by
    intro i
    have hDL : Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL h) T i ((letE i : LetA ↥(OL LL) _) • seq 0) := by
      refine ⟨by rw [smul_smul, letE_mul_self], fun δ hδ => ?_⟩
      rw [γD_letE_smul ((HW l).W K 1 LL h) T δ i (seq 0)]
      have e2 := hΔ δ hδ
      exact congrArg (fun z => (letE i : LetA ↥(OL LL) _) • z) e2
    have hYi : Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL h) ^ Y • ((letE i : LetA ↥(OL LL) _) • seq 0) ∈
        ((HW l).W K 1 LL h).N T := by
      exact smul_letE_mem ((HW l).W K 1 LL h) T i _ (seq 0) hy
    have key := GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl T hT i 0 Y cO hc' _
      (fun τ a j hO hjump hj hjY => hjx i τ a j hO hjump hj hjY)
      (fun k => (letE i : LetA ↥(OL LL) _) • seq k) hDL hYi
      (fun k hk => letE_rec ((HW l).W K 1 LL h) T i _ _ _ (hrec k hk))
    exact mem_of_qp_pow_zero ((HW l).W K 1 LL h) T _ key.2
  exact mem_N_of_letE ((HW l).W K 1 LL h) T _ hmem

end GlobalTheory
