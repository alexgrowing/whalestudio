import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasis

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem hfrac_of {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL] (a : LL) :
    ∃ y o : O, algebraMap O LL y ≠ 0 ∧ algebraMap O LL y * a = algebraMap O LL o := by
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors O) a
  refine ⟨s, x, ?_, ?_⟩
  · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  · rw [mul_comm]
    exact hx

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem rank_eq [IsFractionRing O LL] (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    {r : ℕ} (e : Fin r → C.V)
    (hind : LinearIndependent (PowerSeries O) e)
    (hspan : Submodule.span (PowerSeries O) (Set.range e) = (latOf C).N c) :
    FiniteDimensional LL (Dc W T c) ∧ r = Module.finrank LL (Dc W T c) := by
  classical
  let hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N c) :=
    (Module.Basis.span hind).map (LinearEquiv.ofEq _ _ hspan)
  have hBasis_e : ∀ k, (hBasis k : C.V) = e k := fun k => by
    simp [hBasis, Module.Basis.span_apply]
  have hcmpLI := Pf.lvBasis_cmp_ind hP3 hmod hfrac_of hBasis hBasis_e
  let w : Fin r → Dc W T c := fun k =>
    ⟨W.cmp T ⟨C.t c (e k), Pf.lvBasis_e_mem hBasis hBasis_e k⟩, Pf.lvBasis_cmp_e_letter hBasis hBasis_e k⟩
  have hwLI : LinearIndependent LL w :=
    LinearIndependent.of_comp (DcrisL PD T.ρ (W.emb c)).subtype hcmpLI
  have hwsp : ⊤ ≤ Submodule.span LL (Set.range w) := by
    intro x _
    have hx := Pf.lvBasis_letter_le hP3 hmod hBasis hBasis_e x.2
    have hr : (Set.range fun k => W.cmp T ⟨C.t c (e k), Pf.lvBasis_e_mem hBasis hBasis_e k⟩) =
        (DcrisL PD T.ρ (W.emb c)).subtype '' Set.range w := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, Submodule.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  let bD := Module.Basis.mk hwLI hwsp
  have hFD : FiniteDimensional LL (Dc W T c) := Module.Finite.of_basis bD
  refine ⟨hFD, ?_⟩
  rw [Module.finrank_eq_card_basis bD, Fintype.card_fin]

end Formalism.MainNotions.N.Ln03.K8
