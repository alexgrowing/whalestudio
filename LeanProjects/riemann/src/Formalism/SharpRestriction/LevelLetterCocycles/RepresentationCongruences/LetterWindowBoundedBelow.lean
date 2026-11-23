import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaLiftAlongArc
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SectionInIdealOfLevels

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.UnivF

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem letter_window_bounded_below (ty : Formalism.MainNotions.LocalTheoryWindows.LT) (G₁ S₁ η₁ : ℕ) :
    ∃ U : ℤ, ∀ x ∈ ty.win G₁ S₁ η₁, U ≤ x := by
  cases ty with
  | thin => exact ⟨-(G₁ : ℤ), fun x hx => hx.1⟩
  | up b =>
    refine ⟨-(η₁ : ℤ), fun x hx => ?_⟩
    rcases hx with hx | hx
    · have := hx.1; omega
    · exact hx.1
  | down b =>
    refine ⟨-(b : ℤ) - S₁ - η₁, fun x hx => ?_⟩
    rcases hx with hx | hx
    · have := hx.1; omega
    · have := hx.1; omega

theorem arc_gamma_lift [IsDomain O] [FiniteDimensional Qp LL]
    (hinj : Function.Injective (algebraMap O LL)) (hArc : ArcCore W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hFL : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore W) : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore W := by
  intro hCA h5 A hA c hc e hje hel T hT d b sol hhor g hg hyp
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W hP9 hCA W.one (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have : NeZero n := ⟨by
    rw [W.n_eq]
    have := PD.finK₀
    exact Module.finrank_pos.ne'⟩
  have hS := Formalism.MainNotions.UnusedSlot80.KF.psStable_of W hR
  have hC := Formalism.MainNotions.UnusedSlot80.KF.psCoprime_of W hR
  obtain ⟨t, htΔ, hγπ⟩ := Formalism.MainNotions.LiftingTheory.gamma_uniformizer_eq_mul_unit' W hR
  have hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u :=
    ⟨_, W.AΔ.add_mem (W.AΔ.algebraMap_mem _) (W.AΔ.mul_mem hR.1 htΔ), hγπ⟩
  obtain ⟨h, hγ, hhFr, hlev⟩ := hyp
  refine gamma_lift_along_arc W hinj hArc hR hS hP hCA h5 A hA c hc e hje hel T hT d b sol hhor g hg
    ⟨h, ⟨hhFr, ?_⟩, hγ⟩
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0
    refine ⟨0, d, h, fun i => Pi.single i 1, fun _ _ => 0,
      fun i => ⟨?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩, fun k => ?_⟩
    · have := hhFr i
      simpa [InId, abelian₂] using this
    · rw [Finset.sum_eq_single k (fun i _ hik => by simp [hik.symm]) (by simp)]
      simp [lE]
  · refine section_in_ideal_of_levels W hR hC T _ e hpos b h hlev fun t' ht' => ?_
    obtain ⟨U, hU⟩ := letter_window_bounded_below
      (A.ty ((c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) - (t' : ZMod n))) A.G₀ A.S A.η
    exact ⟨U, fun u hu c₀ =>
      (hFL hCA h5 A hA c hc e hje hel T hT d b sol hhor c₀ t' ht').1 u fun x hx => hu.trans (hU x hx)⟩

end Core

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem arc_gamma_lift_at {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    (hFL : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore ((HW l).W K 1 LL hG)) :
    Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore ((HW l).W K 1 LL hG) := by
  intro hCA h5
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have h5' : 5 ≤ l := hpl ▸ h5
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact arc_gamma_lift _ Subtype.val_injective (hU.a12 l K LL hG hK h5').1 (hU.p9 l K 1 LL hG) hFL
    hCA h5

end Record

end Formalism.MainNotions.N.Ln17
