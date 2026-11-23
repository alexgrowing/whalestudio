import Formalism.SharpRestriction.LevelLetterCocycles.GoodOfLpow

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

def SecCrit0 (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ (x : W.DD T) (k : ℕ) (f : Fin d → W.EE),
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x) →
    RepVV W T c' (e + 1) (A.M PD.p) (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol (lA W ^ k • x) f →
    (∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * LamUp W A c' e)
      (ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) (f m)) →
    (InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x ↔
      ∃ κ : ℕ, SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)
        (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b) fun m => lE W κ * f m)

theorem inFNc_smul (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (a : ZMod n) {c : LetA O n} (hc : c ∈ W.AΔ)
    {x : W.DD T} (hx : InFNc W T a 1 x) : InFNc W T a 1 (c • x) := by
  obtain ⟨y, hy, hyl, rfl⟩ := hx
  exact ⟨c • y, Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hc hy, by rw [smul_comm, hyl], by simp⟩

theorem inFP_up (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n)
    (e N : ℕ) {vv : LetA O n} (hv : vv ∈ W.AΔ) (y : W.DD T)
    (hy : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • y)) :
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • ((ps W 0 ^ N * vv) • W.φD T y)) := by
  obtain ⟨p, hp, hyp⟩ := hy
  rw [one_smul] at hyp
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  refine ⟨(ps W 0 ^ N * vv * ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) • W.φD T p,
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hp0Δ N) hv)
      (W.AΔ.pow_mem hp0Δ _)) _ (φ_Pp W T c' e p hp), ?_⟩
  rw [one_smul, lam_succ, ← hyp, φD_smulA, smul_smul, smul_smul]
  unfold LamUp
  congr 1; ring

theorem good_zero (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) : Good A c' e T b sol 0 := by
  have hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (0 : W.DD T)) := by
    rw [smul_zero]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _
  obtain ⟨κ, Hh, hHh⟩ := horTr_exists W C.hO2 C.hH C.hCA T hT.1 c' b sol hb (A.M PD.p)
  refine good_of_sec C A hA c' hc' T hT b sol hb e 0 hz 0 (fun _ => 0)
    ⟨κ, 0, Hh, fun _ => 0, hHh, fun k => ⟨W.AΔ.zero_mem, by simp⟩, by
      simp only [smul_zero, zero_smul, Finset.sum_const_zero, sub_zero]
      exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _⟩
    (fun m => inFr_zero W) 0 ?_
  simpa using secIn_zero W (condNN W T (c' + (e : ZMod n)) e b) (a := c' + (e : ZMod n)) (e := e)

theorem good_sum (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) {ι : Type} (s : Finset ι) (z : ι → W.DD T)
    (h : ∀ j ∈ s, Good A c' e T b sol (z j)) : Good A c' e T b sol (∑ j ∈ s, z j) := by
  induction s using Finset.induction_on with
  | empty => simpa using good_zero C A hA c' hc' T hT b sol hb e
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact good_add C A hA c' hc' T hT b sol hb e _ _ (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem φE_lE (t : ℕ) : W.φE (lE W t) = lE W t := by
  unfold lE; rw [map_pow, map_natCast]

theorem step_mp (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (IH : Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' e T d b sol)
    (h0 : SecCrit0 A c' e T b sol) (x : W.DD T)
    (hxP : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x))
    (hxN : InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x) : Good A c' (e + 1) T b sol x := by
  set a : ZMod n := c' + (e : ZMod n) with hadef
  have ha' : c' + ((e + 1 : ℕ) : ZMod n) = a + 1 := by rw [hadef]; push_cast; ring
  set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
  set hq : ℕ := Hw A.G₀ A.S A.η (A.ty (a + 1)) with hqdef
  set U : LetA O n := LamUp W A c' e with hUdef
  have hUΔ : U ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W C.hR.1 A _ e)
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W C.hR.1 0
  obtain ⟨m₀, u₀, hu₀, u₁, hu₁, hl, ⟨r₀, hr₀, hu₀e⟩, ⟨s₁, hs₁, hu₁e⟩⟩ :=
    crt W (W.AΔ.mul_mem C.hR.1 (W.AΔ.pow_mem hUΔ 2)) (W.AΔ.pow_mem hp0Δ (H + hq))
      (cop_lamUp W C.hR C.hp0 A c' e (H + hq))

  have g0 : Good A c' (e + 1) T b sol (u₀ • x) := by
    have hz : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u₀ • x)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ hu₀ hxP
    obtain ⟨κ, f, hrep, hfr⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' (e + 1) T hT.1
      b sol hb x hxP
    have hrep0 := repVV_smul W T c' (e + 1) _ _ b sol _ f hu₀ hrep
    rw [smul_comm] at hrep0
    have hfr0 : ∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * U) (ps W 0 ^ H)
        (algebraMap (LetA O n) W.EE u₀ * f m) := by
      intro m
      obtain ⟨t, ht, hft⟩ := hfr m
      refine ⟨r₀ * t, W.AΔ.mul_mem hr₀ ht, ?_⟩
      rw [lam_succ] at hft
      rw [hu₀e]
      simp only [map_mul, map_pow, map_one] at hft ⊢
      linear_combination (algebraMap (LetA O n) W.EE W.π₀ * algebraMap (LetA O n) W.EE U *
        algebraMap (LetA O n) W.EE r₀) * hft
    obtain ⟨κ₀, hS⟩ := (h0 (u₀ • x) κ _ hz hrep0 hfr0).1 (inFNc_smul C.hR.1 T _ hu₀ hxN)
    exact good_of_sec C A hA c' hc' T hT b sol hb (e + 1) _ hz κ _ hrep0 (fun m => inFr_mulA W (hfr m) hu₀) κ₀ hS

  obtain ⟨r, bb, β, hbb, hβ, hdec⟩ := exists_smul_pow_eq_sum_of_inFNc C T A hA hT a hq le_rfl x (by rwa [ha'] at hxN)
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  have gj : ∀ j, Good A c' (e + 1) T b sol ((ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j)) := by
    intro j
    have hbl : (letE a : LetA O n) • bb j = bb j := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T a (hbb j).2
    have hbN : InFNc W T a 1 (bb j) := ⟨bb j, (hbb j).1, hbl, (one_smul _ _).symm⟩
    have hbP : InFP W T c' e 1 (abelian₂ W A a e • bb j) :=
      Formalism.MainNotions.UnusedSlot80.ArcC.arc_down W C.hs C.hR T A hA h5T (C.hmod T hT.1) C.hΔ c' hc' e (bb j) hbN
    obtain ⟨κj, fj, hrepj, hfrj⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1
      b sol hb (bb j) hbP
    obtain ⟨κ'j, hSj⟩ := (IH (bb j) κj fj hbP hrepj hfrj).1 hbN
    have hv : s₁ * β j ∈ W.AΔ := W.AΔ.mul_mem hs₁ (hβ j)
    have hPκ : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (lA W ^ κj • bb j)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W κj) hbP
    obtain ⟨-, hrep', -⟩ := transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol (lA W ^ κj • bb j) fj hPκ
      (by simpa using hrepj) hfrj H le_rfl hv
    have hel : (ps W 0 ^ H * (s₁ * β j)) • W.φD T (lA W ^ κj • bb j) =
        lA W ^ κj • ((ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j)) := by
      rw [φD_smulA, φA_lA, smul_comm]
    rw [hel] at hrep'
    have hlow0 : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T (a + 1) 0 (-(H : ℤ)) := by
      intro c₀
      have := dvO_filLow W C.hbij A hA c' hc' T hT b hb.1 (e + 1) 0 (by omega) c₀
      rw [hHdef, ha']; rwa [ha'] at this
    have hS' := secIn_transport W T a e b H hv C.hR.1 hlow0 _ hSj
    rw [← ha'] at hS'
    refine good_of_sec C A hA c' hc' T hT b sol hb (e + 1) _ (inFP_up C.hR T A c' e H hv (bb j) hbP) κj _ hrep'
      (fun m => (transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol (lA W ^ κj • bb j) fj hPκ
        (by simpa using hrepj) hfrj H le_rfl hv).2.2 m) κ'j ?_
    convert hS' using 1
    funext m
    rw [map_mul W.φE, φE_lE]
    ring
  have hu₁x : u₁ • x = ∑ j, (ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j) := by
    rw [hu₁e, show ps W 0 ^ (H + hq) * s₁ = (ps W 0 ^ H * s₁) * ps W 0 ^ hq by ring, mul_smul, hdec,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]; congr 1; ring
  have g1 : Good A c' (e + 1) T b sol (u₁ • x) := by
    rw [hu₁x]
    exact good_sum C A hA c' hc' T hT b sol hb (e + 1) _ _ fun j _ => gj j
  have g2 : Good A c' (e + 1) T b sol (lA W ^ m₀ • x) := by
    rw [hl, add_smul]
    exact good_add C A hA c' hc' T hT b sol hb (e + 1) _ _ g0 g1
  exact good_of_lpow C A hA c' hc' T hT b sol hb (e + 1) m₀ x hxP g2

end Formalism.MainNotions.UnusedSlot80.LevC
