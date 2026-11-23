import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section F2Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def unitQProds : Submonoid (LetA O n) where
  carrier := {f | ∃ (u : (LetA O n)ˣ) (J : Multiset ℕ), f = (u : LetA O n) * (J.map fun j => (W.φA ^ j) W.Q).prod}
  one_mem' := ⟨1, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨u, J, rfl⟩ ⟨u', J', rfl⟩
    refine ⟨u * u', J + J', ?_⟩
    rw [Multiset.map_add, Multiset.prod_add, Units.val_mul]
    ring

theorem ps_mem_unitQProds (hs : W.s = 1) (hq : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * (W.π₀ + ((PD.p : ℕ) : LetA O n)))
    (s : ℕ) : (W.φA ^ s) (W.π₀ + ((PD.p : ℕ) : LetA O n)) ∈ unitQProds W := by
  obtain ⟨w, hw⟩ := hq
  have hQ : W.Q = W.q := by
    simp [LocWach.Q, hs]
  have e : W.π₀ + ((PD.p : ℕ) : LetA O n) = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.Q := by
    rw [hQ, hw, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨Units.map ((W.φA ^ s : LetA O n →ₐ[O] LetA O n) : LetA O n →* LetA O n) w⁻¹, {s}, ?_⟩
  rw [e, map_mul]
  simp

theorem pi0pow_mem_aN (T : LocLat G Qp LL O) (M : ℕ) (hM : 1 ≤ (PD.p - 1) * M)
    (hπ : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (x : W.DD T) (hx : x ∈ W.N T) :
    W.π₀ ^ M • x ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ := by
  obtain ⟨w, hw⟩ := hπ
  refine ⟨((w : LetA O n) ^ M * letπ ^ ((PD.p - 1) * M - 1)) • x, (W.N T).smul_mem _ hx, ?_⟩
  have e : W.π₀ ^ M = letπ * ((w : LetA O n) ^ M * letπ ^ ((PD.p - 1) * M - 1)) := by
    rw [hw, mul_pow, ← pow_mul]
    have : (PD.p - 1) * M = ((PD.p - 1) * M - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  rw [e]
  simp only [mul_smul]

theorem restriction_eq_restriction_H1 (H : Subgroup G) (T : LocLat G Qp LL O) (κ : LatticeCohomology T.L) :
    Formalism.MainNotions.DeltaInvariantLattices.res H T κ = resH1 T H κ := rfl

theorem wach_cocycle_class_mem_latticeFiniteCohomology (hs : W.s = 1) (hp : PD.p ≠ 2) (hfr : Module.finrank K₀ K = 1)
    (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr')
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (M : ℕ) (hM : 1 ≤ (PD.p - 1) * M)
    (x : ↥(W.wachCocyclesDelta T)) (hz : ∃ z' ∈ W.NΔ T, (x : W.DD T × W.DD T).2 = W.π₀ ^ M • z')
    (Λ : LetA O n) (hΛ : Λ ∈ unitQProds W) (hy : Λ • (x : W.DD T × W.DD T).1 ∈ W.N T) :
    W.clK T x ∈ latticeFiniteCohomology PD T.L := by
  have hg : W.gamK = W.gam := W.gamK_eq_one hs hp
  have hr := ((h9 T hT hs hp).2.2 hfr).1
  obtain ⟨_, _, hπ, _, hq, _⟩ := hr
  have hq' : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * (W.π₀ + ((PD.p : ℕ) : LetA O n)) := by
    obtain ⟨w, hw⟩ := hq
    refine ⟨w, ?_⟩
    rw [hw]
    congr 1
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat]
  have hmem : (x : W.DD T × W.DD T) ∈ W.divisibleCocycles T := by
    have h1 := (Submodule.mem_inf.mp x.2).1
    rw [hg] at h1
    exact h1
  rw [h2b T hT, restriction_eq_restriction_H1, hres T x ⟨_, hmem⟩ rfl]
  obtain ⟨u, J, rfl⟩ := hΛ
  obtain ⟨z', hz', hzz⟩ := hz
  have hy' : (J.map fun j => (W.φA ^ j) W.Q).prod • (x : W.DD T × W.DD T).1 ∈ W.N T := by
    have := (W.N T).smul_mem ((u⁻¹ : (LetA O n)ˣ) : LetA O n) hy
    rwa [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  have hzN : (x : W.DD T × W.DD T).2 ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ := by
    rw [hzz]; exact pi0pow_mem_aN W T M hM hπ z' hz'.1
  have := h7 T hT J (x : W.DD T × W.DD T).1 (x : W.DD T × W.DD T).2 hy' hzN hmem
  exact this

theorem frobenius_iterate_uniformizer_unit_products (hs : W.s = 1) (hp : PD.p ≠ 2) (hfr : Module.finrank K₀ K = 1)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (s : ℕ) :
    (W.φA ^ s) (W.π₀ + ((PD.p : ℕ) : LetA O n)) ∈ unitQProds W := by
  obtain ⟨_, _, _, _, hq, _⟩ := ((h9 T hT hs hp).2.2 hfr).1
  refine ps_mem_unitQProds W hs ?_ s
  obtain ⟨w, hw⟩ := hq
  refine ⟨w, ?_⟩
  rw [hw]
  congr 1
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat]

end F2Core

section F2Rows

theorem caseA_of_le_Kur_of_ne_two {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) {K LL : FinExt l} (h : Good K 1 LL)
    (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL h) := by
  refine ⟨⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x, x.2, hK x.2⟩, rfl⟩⟩, H.W_s K 1 LL h, ?_⟩
  rw [P.PD_p]
  exact hl

theorem finrank_of_caseA {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) :
    Module.finrank K₀ K = 1 := by
  have e : K₀ ≃ₗ[K₀] K := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1
  rw [← e.finrank_eq, Module.finrank_self]

end F2Rows

section F2At

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem wach_cohomology_class_unramified_functor (hC : Formalism.MainNotions.LiftingTheory.CaseA W) (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr') :
    Formalism.MainNotions.WachCoordinates.F2 W := by
  intro hh M hM T hT _ c x hx hΛ
  have hfr := finrank_of_caseA W hC
  obtain ⟨Λ, ⟨k, m, rfl⟩, hΛy⟩ := hΛ
  refine wach_cocycle_class_mem_latticeFiniteCohomology W hC.2.1 hC.2.2 hfr h7 h9 h2b hres T hT M (by omega) x hx.2.2 _ ?_ hΛy.1
  exact Submonoid.prod_mem _ fun s _ => pow_mem (frobenius_iterate_uniformizer_unit_products W hC.2.1 hC.2.2 hfr h9 T hT s) _

theorem wach_cohomology_class_at_functor (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : W.gamK = W.gam → ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr') :
    Formalism.MainNotions.ArcLiftingSetup.SecondWachFiltration W := by
  intro hC hh M hM T hT _ c y x Λ hΛ _ hΛy hcls
  have hfr := finrank_of_caseA W hC
  obtain ⟨z, hc, hz, rfl⟩ := hcls
  obtain ⟨y', hy', _, hyy⟩ := hΛy
  refine wach_cocycle_class_mem_latticeFiniteCohomology W hC.2.1 hC.2.2 hfr h7 h9 h2b (hres (W.gamK_eq_one hC.2.1 hC.2.2))
    T hT M (by omega) ⟨(y, z), hc⟩ hz Λ ?_ ?_
  · refine (Submonoid.closure_le.mpr ?_) hΛ
    rintro _ ⟨s, rfl⟩
    exact frobenius_iterate_uniformizer_unit_products W hC.2.1 hC.2.2 hfr h9 T hT s
  · show Λ • y ∈ W.N T
    rw [hyy, one_smul]
    exact hy'.1

end F2At

section F2Rows2

theorem wach_cohomology_class_unramified_case (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : SecondFiltrationHypotheses D HW F) :
    SecondFiltrationEtale D HW F := fun l _ K LL hA _ =>
  wach_cohomology_class_unramified_functor ((HW l).W K 1 LL hA.2.2) (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1)
    (h.1 l K 1 LL hA.2.2) (h.2.1 l K 1 LL hA.2.2) (h.2.2 l K 1 LL hA.2.2)
    (((F l).E K 1 LL hA.2.2).tie.clK_res
      (((HW l).W K 1 LL hA.2.2).gamK_eq_one (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1).2.1
        (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1).2.2))

theorem cohomology_class_unramified_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : FamilyMassExplicitOfVolumeAgreement D HW F :=
  fun h => wach_cohomology_class_unramified_case D HW F h.1

theorem second_filtration_case_a_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : SecondFiltrationHypotheses D HW F) :
    SecondFiltrationArcLifting D HW F := fun l _ K LL hG _ _ =>
  wach_cohomology_class_at_functor ((HW l).W K 1 LL hG) (h.1 l K 1 LL hG) (h.2.1 l K 1 LL hG) (h.2.2 l K 1 LL hG)
    ((F l).E K 1 LL hG).tie.clK_res

theorem second_filtration_theorem_arc_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : SecondFiltrationTheoremArcLifting D HW F :=
  fun h => second_filtration_case_a_of_hypotheses D HW F h.1

end F2Rows2

end Formalism.MainNotions.UnusedSlot80
