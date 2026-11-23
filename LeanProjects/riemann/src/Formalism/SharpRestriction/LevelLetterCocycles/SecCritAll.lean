import Formalism.SharpRestriction.LevelLetterCocycles.SecCritZero

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

theorem step_mpr (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (IH : Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' e T d b sol)
    (h0 : SecCrit0 A c' e T b sol) (x : W.DD T) (k : ℕ) (f : Fin d → W.EE)
    (hxP : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x))
    (hrep : RepVV W T c' (e + 1) (A.M PD.p) (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol
      (lA W ^ k • x) f)
    (hfr : ∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) (f m))
    (κ : ℕ) (hS : SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b)
      fun m => lE W κ * f m) :
    InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x := by
  set a : ZMod n := c' + (e : ZMod n) with hadef
  have ha' : c' + ((e + 1 : ℕ) : ZMod n) = a + 1 := by rw [hadef]; push_cast; ring
  set a' : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with ha'def
  set H : ℕ := A.Hs a' (e + 1) 0 with hHdef
  set U : LetA O n := LamUp W A c' e with hUdef
  set Λ' : LetA O n := abelian₂ W A a' (e + 1) with hΛ'def
  have hUΔ : U ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W C.hR.1 A _ e)
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W C.hR.1 0
  have hS' := hS
  obtain ⟨I, g, c₀, α, hg, hF⟩ := hS
  set N : ℕ := H + ∑ i, (-(α i 0)).toNat with hNdef
  obtain ⟨m₀, u₀, hu₀, u₁, hu₁, hl, ⟨r₀, hr₀, hu₀e⟩, ⟨s₁, hs₁, hu₁e⟩⟩ :=
    crt W (W.AΔ.mul_mem C.hR.1 (W.AΔ.pow_mem hUΔ 2)) (W.AΔ.pow_mem hp0Δ N) (cop_lamUp W C.hR C.hp0 A c' e N)

  have hx0 : InFNc W T a' 1 (u₀ • x) := by
    have hz : InFP W T c' (e + 1) 1 (Λ' • (u₀ • x)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ hu₀ hxP
    have hrep0 := repVV_smul W T c' (e + 1) _ _ b sol _ f hu₀ hrep
    rw [smul_comm] at hrep0
    have hfr0 : ∀ m, InFr W a' (W.π₀ * U) (ps W 0 ^ H) (algebraMap (LetA O n) W.EE u₀ * f m) := by
      intro m
      obtain ⟨t, ht, hft⟩ := hfr m
      refine ⟨r₀ * t, W.AΔ.mul_mem hr₀ ht, ?_⟩
      rw [hΛ'def, lam_succ] at hft
      rw [hu₀e]
      simp only [map_mul, map_pow, map_one] at hft ⊢
      linear_combination (algebraMap (LetA O n) W.EE W.π₀ * algebraMap (LetA O n) W.EE U *
        algebraMap (LetA O n) W.EE r₀) * hft
    refine (h0 (u₀ • x) k _ hz hrep0 hfr0).2 ⟨κ, ?_⟩
    have := secIn_mulA W hS' hu₀
    convert this using 1
    funext m; ring

  have hMH : Mw A.G₀ A.S A.η (A.ty (a + 1)) ≤ H := by
    have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' (e + 1) (e + 1) (by omega) le_rfl
    rw [Nat.sub_self, ← ha'def, ha'] at this
    rw [hHdef, ha']; exact this
  have key : ∀ i, ∃ (t : ℕ) (z : W.DD T), InFNc W T a' 1 z ∧ InFP W T c' (e + 1) 1 (Λ' • z) ∧
      RepVV W T c' (e + 1) (A.M PD.p) Λ' b sol z
        (fun m => lE W t * (algebraMap (LetA O n) W.EE u₁ * (g i * algebraMap O W.EE (c₀ i m)))) := by
    intro i
    by_cases hci : c₀ i = 0
    · refine ⟨0, 0, inFNc_zero T a', by rw [smul_zero]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' (e + 1) _,
        ?_⟩
      convert repVV_zero C A c' (e + 1) T hT.1 b sol hb Λ' using 1
      funext m
      simp [hci]
    · have hα : ∀ s, s < e → -(A.Hs a e s : ℤ) ≤ α i (s + 1) := by
        intro s hs
        by_contra hlt
        push_neg at hlt
        apply hci
        have hcond := (hg i).2 (s + 1) (by omega)
        have hH1 : A.Hs a' (e + 1) (s + 1) = A.Hs a e s := by
          rw [hs_succ, ha', add_sub_cancel_right]
        refine dvO_zero_high W C.hbij C.hinj C.hV C.hs C.h5 A hA c' hc' T hT (C.h3 T hT.1) (C.hmod T hT.1) b hb.1
          (e + 1) (s + 1) (by omega) (-(α i (s + 1))) ?_ (c₀ i) hcond
        rw [hH1]; omega
      have hgi : InId W (a + 1) (e + 1) (α i) (g i) := by rw [← ha']; exact (hg i).1
      have hNi : H + (-(α i 0)).toNat ≤ N := by
        have := Finset.single_le_sum (f := fun j => (-(α j 0)).toNat) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
        omega
      obtain ⟨vv, hvv, g', heq, hId, hFr⟩ := mono_lift W C.hR A a e (α i) (g i) hgi hα N H hNi hs₁
      have hcondE : condNN W T a e b (fun s => α i (s + 1)) (c₀ i) := by
        intro s hs
        have h1 := (hg i).2 (s + 1) (by omega)
        rw [ha', filS_succ, dvO_succ] at h1
        obtain ⟨y, hy, hye⟩ := h1
        rwa [Formalism.MainNotions.UnusedSlot80.ArcF.φVB_inj T hye] at hy
      set F : Fin d → W.EE := fun m => g' * algebraMap O W.EE (c₀ i m) with hFdef
      have hFfr : ∀ m, InFr W a 1 (abelian₂ W A a e) (F m) := fun m => by
        have := inFr_mulA W hFr (W.AΔ.algebraMap_mem (c₀ i m))
        convert this using 1
        show g' * algebraMap O W.EE (c₀ i m) = _
        rw [mul_comm, ← IsScalarTower.algebraMap_apply]
      obtain ⟨κi, y, hyP, hyrep⟩ := pOfSec' W C.hO2 C.hR C.hH C.hCA A c' e (A.M PD.p) T hT.1 b sol hb F hFfr
      have hyN : InFNc W T a 1 y := by
        have hrepy : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ 0 • y)
            (fun m => lE W κi * F m) := by simpa using hyrep
        refine (IH y 0 _ hyP hrepy (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hFfr m) κi)).2 ⟨0, ?_⟩
        refine ⟨1, fun _ => lE W κi * g', fun _ => c₀ i, fun _ s => α i (s + 1),
          fun _ => ⟨Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W hId κi, hcondE⟩, fun m => ?_⟩
        simp only [Fin.sum_univ_one, hFdef]
        rw [show lE W 0 = 1 by simp [lE]]
        ring
      have hzN := up1 C T A hA hT a H hMH hvv y hyN
      obtain ⟨hzP, hzrep, -⟩ := transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol y (fun m => lE W κi * F m) hyP hyrep
        (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hFfr m) κi) H le_rfl hvv
      refine ⟨κi, (ps W 0 ^ H * vv) • W.φD T y, by rw [ha']; exact hzN, hzP, ?_⟩
      convert hzrep using 1
      funext m
      rw [hFdef]
      simp only [map_mul W.φE, φE_lE, AlgHom.commutes]
      rw [hu₁e]
      linear_combination (lE W κi * algebraMap O W.EE (c₀ i m)) * heq
  choose t z hzN hzP hzrep using key
  set Tt : ℕ := ∑ i, t i with hTt
  have htle : ∀ i, t i ≤ Tt := fun i =>
    Finset.single_le_sum (f := t) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hZrep : RepVV W T c' (e + 1) (A.M PD.p) Λ' b sol (∑ i, lA W ^ (Tt - t i) • z i)
      (fun m => lE W (Tt + κ) * (algebraMap (LetA O n) W.EE u₁ * f m)) := by
    have h1 := repVV_sum C A c' (e + 1) T hT.1 b sol hb Λ' Finset.univ (fun i => lA W ^ (Tt - t i) • z i)
      (fun i m => lE W (Tt - t i) * (lE W (t i) * (algebraMap (LetA O n) W.EE u₁ *
        (g i * algebraMap O W.EE (c₀ i m))))) (fun i _ => by
          have := repVV_smul W T c' (e + 1) _ Λ' b sol _ _ (lA_mem W (Tt - t i)) (hzrep i)
          rwa [← lE_eq] at this)
    convert h1 using 1
    funext m
    simp only [lE_mul]
    have : ∀ i, Tt - t i + t i = Tt := fun i => Nat.sub_add_cancel (htle i)
    simp only [this]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hF m]
    unfold lE; rw [pow_add]; ring
  have hZN : InFNc W T a' 1 (∑ i, lA W ^ (Tt - t i) • z i) :=
    inFNc_sum T a' _ _ fun i _ => inFNc_smul C.hR.1 T a' (lA_mem W _) (hzN i)
  have hZP : InFP W T c' (e + 1) 1 (Λ' • ∑ i, lA W ^ (Tt - t i) • z i) := by
    rw [Finset.smul_sum]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_sum W T c' (e + 1) _ _ _ fun i _ => by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ (lA_mem W _) (hzP i)
  have hx1P : InFP W T c' (e + 1) 1 (Λ' • (u₁ • x)) := by
    rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ hu₁ hxP
  have hrep1 := repVV_smul W T c' (e + 1) _ _ b sol _ f hu₁ hrep
  rw [smul_comm] at hrep1
  have hx1 := mem_of_sec_eq C A hA c' hc' T hT b sol hb (e + 1) (u₁ • x) _ k 0 (Tt + κ) _ hx1P hZP hZN hrep1
    (by rw [pow_zero, one_smul]; exact hZrep)
  have hsum := inFNc_add T a' hx0 hx1
  rw [← add_smul, ← hl] at hsum
  exact Formalism.MainNotions.UnusedSlot80.ArcC.arc_sat W C.hCA C.hsat C.hR T hT.1 A c' (e + 1)
    (Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' (e + 1) T hT) x hxP ⟨m₀, hsum⟩

theorem secCrit_all (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (h0 : ∀ e, SecCrit0 A c' e T b sol) :
    ∀ e, Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' e T d b sol := by
  intro e
  induction e with
  | zero => exact secCrit_zero A c' T b sol
  | succ e IH =>
    intro x k f hxP hrep hfr
    constructor
    · intro hxN
      exact (step_mp C A hA c' hc' T hT b sol hb e IH (h0 e) x hxP hxN).2 k f hrep hfr
    · rintro ⟨κ, hS⟩
      exact step_mpr C A hA c' hc' T hT b sol hb e IH (h0 e) x k f hxP hrep hfr κ hS

end Formalism.MainNotions.UnusedSlot80.LevC
