import Formalism.SharpRestriction.LevelLetterCocycles.HorTrUnique

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

variable [IsDomain O]

theorem horTr_exists (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ)
    (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol)
    (M : ℕ) : ∃ κ : ℕ, ∃ Hh : Fin d → W.DD T, ∀ k, IsHorTr W T b sol M κ k (Hh k) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hHc := hH hCA T hTc c'
  have hBd := (hHc.2.2.2.2 d b hb.1 sol hb.2).1
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hBd k r m)
  refine ⟨Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r •
    Formalism.MainNotions.LiftingTheory.vecB W T b (fun m => ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M -
      Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m), fun k => ⟨_, fun r hr m => ?_, rfl⟩⟩
  have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
  simp only [map_mul, map_pow, map_natCast, hg]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem horTr_mem (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (hπ : W.π₀ ∈ W.AΔ)
    (R κ e : ℕ) (k : Fin d) {H : W.DD T} (h : IsHorTr W T b sol R κ k H) :
    ((W.φD T) ^ e) H ∈ Pp W T c' e := by
  obtain ⟨y, -, rfl⟩ := h
  rw [map_sum]
  refine AddSubgroup.sum_mem _ fun r _ => ?_
  rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul]
  refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W (W.AΔ.pow_mem hπ r) e) ?_
  unfold Formalism.MainNotions.LiftingTheory.vecB
  refine ⟨?_, ?_⟩
  · refine ⟨(W.N T).sum_mem fun m _ => (W.N T).smul_of_tower_mem _ ((hb.1 m).1.1), fun δ hδ => ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_smul, (hb.1 m).1.2 δ hδ]
  · refine ⟨∑ m, y r m • b m, (W.N T).sum_mem fun m _ => (W.N T).smul_of_tower_mem _ ((hb.1 m).1.1), ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_comm, Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2]

theorem yM_gen (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (hπ : W.π₀ ∈ W.AΔ) (h5p : 5 ≤ PD.p)
    (A : ArcP n) (hA : A.OK) (a : ZMod n) (e : ℕ) :
    ∃ ν ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ A.M PD.p = W.π₀ * abelian₂ W A a e ^ 2 * ν := by
  obtain ⟨u, hu, u', -, -, hT⟩ := (hTr hCA).2.1 e (A.M PD.p)
  have hlt := Formalism.MainNotions.UnusedSlot80.ArcC.two_h_lt A h5p
  have hM : 1 ≤ A.M PD.p := by unfold ArcP.M; exact Nat.le_add_left 1 _
  have hle : ∀ s, 2 * A.Hs a e s ≤ (PD.p - 1) * A.M PD.p := fun s => by
    have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_le_h A hA a e s; omega
  refine ⟨u * W.π₀ ^ (A.M PD.p - 1) * ∏ s ∈ Finset.range e, ps W s ^ ((PD.p - 1) * A.M PD.p - 2 * A.Hs a e s),
    W.AΔ.mul_mem (W.AΔ.mul_mem hu (W.AΔ.pow_mem hπ _)) (W.AΔ.prod_mem fun s _ =>
      W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hπ s) _), ?_⟩
  rw [hT]
  have e1 : W.π₀ ^ A.M PD.p = W.π₀ * W.π₀ ^ (A.M PD.p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM]
  have e2 : ∏ k ∈ Finset.range e, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * A.M PD.p) =
      abelian₂ W A a e ^ 2 * ∏ s ∈ Finset.range e, ps W s ^ ((PD.p - 1) * A.M PD.p - 2 * A.Hs a e s) := by
    unfold abelian₂
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Formalism.MainNotions.UnusedSlot80.ArcC.pk_eq_ps, ← pow_mul, ← pow_add]
    congr 1
    have := hle s
    omega
  rw [e1, e2]
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
