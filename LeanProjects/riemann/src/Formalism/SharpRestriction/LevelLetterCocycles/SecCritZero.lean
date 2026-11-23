import Formalism.SharpRestriction.LevelLetterCocycles.ProdPsUnitE

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

theorem repVV_zero (C : Ctx W) (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ)
    {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (Λ : LetA O n) :
    RepVV W T c' e (A.M PD.p) Λ b sol 0 (fun _ => 0) := by
  obtain ⟨κ, Hh, hHh⟩ := horTr_exists W C.hO2 C.hH C.hCA T hTc c' b sol hb (A.M PD.p)
  exact ⟨κ, 0, Hh, fun _ => 0, hHh, fun k => ⟨W.AΔ.zero_mem, by simp⟩, by
    simp only [smul_zero, zero_smul, Finset.sum_const_zero, sub_zero]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _⟩

theorem repVV_sum (C : Ctx W) (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ)
    {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (Λ : LetA O n)
    {ι : Type} (s : Finset ι) (z : ι → W.DD T) (F : ι → Fin d → W.EE)
    (h : ∀ j ∈ s, RepVV W T c' e (A.M PD.p) Λ b sol (z j) (F j)) :
    RepVV W T c' e (A.M PD.p) Λ b sol (∑ j ∈ s, z j) (fun m => ∑ j ∈ s, F j m) := by
  induction s using Finset.induction_on with
  | empty => simpa using repVV_zero C A c' e T hTc b sol hb Λ
  | insert j s hj ih =>
    have := repVV_add W C.hinj T c' e _ Λ b sol _ _ _ _ (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert hj]
    convert this using 1
    funext m
    rw [Finset.sum_insert hj]
    rfl

theorem inFNc_sum (T : LocLat G Qp LL O) (a : ZMod n) {ι : Type} (s : Finset ι) (z : ι → W.DD T)
    (h : ∀ j ∈ s, InFNc W T a 1 (z j)) : InFNc W T a 1 (∑ j ∈ s, z j) := by
  induction s using Finset.induction_on with
  | empty => simpa using inFNc_zero T a
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact inFNc_add T a (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem secCrit_zero (A : ArcP n) (c' : ZMod n) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) : Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' 0 T d b sol := by
  intro x k f hx _ hfr
  have hc : c' + ((0 : ℕ) : ZMod n) = c' := by simp
  constructor
  · intro _
    refine ⟨0, d, fun m => lE W 0 * f m, fun m => Pi.single m 1, fun _ _ => 0, fun m => ⟨?_, fun s hs => absurd hs (by omega)⟩,
      fun k => ?_⟩
    · obtain ⟨u, hu, hfu⟩ := hfr m
      refine ⟨lA W ^ 0 * u, W.AΔ.mul_mem (lA_mem W 0) hu, ?_⟩
      rw [lam_zero, map_one, one_mul] at hfu
      simp only [Finset.range_zero, Finset.prod_empty, pow_zero, map_one, one_mul, mul_one, map_mul] at hfu ⊢
      rw [show lE W 0 = 1 by simp [lE], one_mul]
      exact hfu
    · simp [Pi.single_apply]
  · intro _
    rw [lam_zero, one_smul] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [one_smul]
    have : ∀ y ∈ Pp W T c' 0, InFNc W T (c' + ((0 : ℕ) : ZMod n)) 1 y := by
      refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T c' 0 _ (inFNc_zero T _) (fun x y hx hy => inFNc_add T _ hx hy)
        (fun x hx => inFNc_neg T _ hx) ?_
      intro a ha y hy
      rw [pow_zero, Module.End.one_apply]
      obtain ⟨hyN, ⟨y', -, hyl⟩⟩ := hy
      refine ⟨a • y, Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T ha hyN, ?_, (one_smul _ _).symm⟩
      rw [hc, ← hyl, LinearMap.smul_apply, LinearMap.id_apply, smul_comm (letE c' : LetA O n) a,
        smul_smul (letE c' : LetA O n) (letE c' : LetA O n), Formalism.MainNotions.WachCoordinates.Br.letE_mul_self]
    exact this p hp

end Formalism.MainNotions.UnusedSlot80.LevC
