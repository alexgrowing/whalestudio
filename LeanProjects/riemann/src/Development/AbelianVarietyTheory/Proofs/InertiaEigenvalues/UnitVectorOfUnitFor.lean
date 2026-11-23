import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitForOfTie

noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitVector_of_unitFor (E : EtTie W RA RW inclR φR gR πA)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span O {e₀} = ⊤ ∧
      W.one.L.T = Submodule.span O {(e₀ : W.one.V)} ∧
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      W.N W.one = Submodule.span (LetA O n) {e} ∧
      Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧
      W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧
      ∀ a : LetA O n, a • e = 0 → a = 0 := by
  obtain ⟨-, e₀, h₀, -, -⟩ := E.one_e
  obtain ⟨e, hj, hbij, hφ, hγ, hN⟩ := hU e₀ h₀
  refine ⟨e, e₀, h₀, ?_, hj, hN, ?_, hφ, hγ, fun a ha => ?_⟩
  · have h1 := congrArg (Submodule.map W.one.L.T.subtype) h₀
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton] at h1
    exact h1.symm
  · rw [eq_top_iff]
    rintro z -
    exact Submodule.mem_span_singleton.2 (hbij.2 z)
  · apply W.EE_inj
    apply hbij.1
    simp only
    rw [algebraMap_smul, algebraMap_smul, ha, zero_smul]

end Generic

open Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem unitVector : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span ↥(OL LL) {e₀} = ⊤ ∧ W.one.L.T = Submodule.span ↥(OL LL) {(e₀ : W.one.V)} ∧ E.jD W.one e = (1 : RW LL) ⊗ₜ[↥(OL LL)] e₀ ∧ W.N W.one = Submodule.span (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) {e} ∧ Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧ W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧ ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a • e = 0 → a = 0 := by
  intro D HW F l _ K s LL h
  exact unitVector_of_unitFor _ (unitPart l (D.loc l) (D.locA l) (HW l) (F l) K s LL h)

end GlobalTheory.WachUnit
