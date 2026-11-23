import Formalism.SharpRestriction.LevelLetterCocycles.InFNcSmul

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

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

theorem inFNc_add (T : LocLat G Qp LL O) (a : ZMod n) {x y : W.DD T} (hx : InFNc W T a 1 x)
    (hy : InFNc W T a 1 y) : InFNc W T a 1 (x + y) := by
  obtain ⟨x', hx', hxl, rfl⟩ := hx
  obtain ⟨y', hy', hyl, rfl⟩ := hy
  exact ⟨x' + y', (W.NΔ T).add_mem hx' hy', by rw [smul_add, hxl, hyl], by simp⟩

theorem inFNc_neg (T : LocLat G Qp LL O) (a : ZMod n) {x : W.DD T} (hx : InFNc W T a 1 x) :
    InFNc W T a 1 (-x) := by
  obtain ⟨x', hx', hxl, rfl⟩ := hx
  exact ⟨-x', (W.NΔ T).neg_mem hx', by rw [smul_neg, hxl], by simp⟩

theorem inFNc_zero (T : LocLat G Qp LL O) (a : ZMod n) : InFNc W T a 1 (0 : W.DD T) :=
  ⟨0, (W.NΔ T).zero_mem, smul_zero _, by simp⟩

theorem mem_of_sec_eq (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (x z : W.DD T) (k k' t : ℕ) (f : Fin d → W.EE)
    (hxP : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x))
    (hzP : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z))
    (hzN : InFNc W T (c' + (e : ZMod n)) 1 z)
    (hx : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k • x) f)
    (hz : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k' • z)
      (fun m => lE W t * f m)) :
    InFNc W T (c' + (e : ZMod n)) 1 x := by
  set Λ := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  have r1 := repVV_lA T c' e _ _ b sol x f (k + k' + t) k hx
  have r2 := repVV_lA T c' e _ _ b sol z _ (k' + k) k' hz
  have hsec : (fun m => lE W (k' + k) * (lE W t * f m)) = (fun m => lE W (k + k' + t) * f m) := by
    funext m; rw [lE_mul]; congr 2; ring
  rw [hsec] at r2
  have r3 := repVV_sub W C.hinj T c' e _ _ b sol _ _ _ _ r1 r2
  rw [sub_self] at r3
  have hΛu := lam_unit W C.hR A (c' + (e : ZMod n)) e
  have hwP : InFP W T c' e 1 (Λ • (lA W ^ (k + (k + k' + t)) • x - lA W ^ (k' + (k' + k)) • z)) := by
    rw [smul_sub, smul_comm Λ, smul_comm Λ (lA W ^ (k' + (k' + k)))]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_sub W T c' e _ (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hxP)
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hzP)
  have hw := piLam_of_sec W C.hR C.hsatP C.hCA T hT.1 A c' e _ b sol hb.1 _ hwP _ r3 (fun m => inFr_zero W)
  have hwN := inN_of_piLam W C.hR.1 T A c' e
    (Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' e T hT) _ hw
  have hzN' := inFNc_smul C.hR.1 T _ (lA_mem W (k' + (k' + k))) hzN
  have hxN := inFNc_add T _ hwN hzN'
  rw [sub_add_cancel] at hxN
  exact Formalism.MainNotions.UnusedSlot80.ArcC.arc_sat W C.hCA C.hsat C.hR T hT.1 A c' e
    (Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' e T hT) x hxP ⟨_, hxN⟩

end Formalism.MainNotions.UnusedSlot80.LevC
