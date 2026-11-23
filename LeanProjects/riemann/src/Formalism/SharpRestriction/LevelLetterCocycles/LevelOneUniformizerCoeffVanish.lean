import Formalism.SharpRestriction.LevelLetterCocycles.MembershipCriterionOfLevelZero
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemOfExp

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevE

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    (levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B))

theorem smulS_map {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V'] [Module LL V']
    (L : V →ₗ[LL] V') {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) :
    smulS g (fun k => L (f k)) = fun k => L (smulS g f k) := by
  have hf0 : ∀ k < m, f k = 0 := hf
  have hf' : LB m (fun k => L (f k)) := by
    intro k hk
    show L (f k) = 0
    rw [hf0 k hk, map_zero]
  funext k
  rw [smulS_eq_sum hf' g k ((k - m).toNat + 1) (by omega), smulS_eq_sum hf g k ((k - m).toNat + 1) (by omega),
    map_sum]
  simp only [map_smul]

theorem levB_smul (hEq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levB T i ζ x k))
    (hsupp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)), ∃ m : ℤ, ∀ k < m, levB T i ζ x k = 0)
    (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) :
    levB T i ζ (a • x) = smulS (W.lev i ζ a) (levB T i ζ x) := by
  obtain ⟨m, hm⟩ := hsupp T i ζ x
  funext k
  apply Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (LL := LL) (V := T.V)
  have h1 := smulS_map (ιV PD (LL := LL) (V := T.V)) (f := levB T i ζ x) hm (W.lev i ζ a)
  have h2 : (fun k => W.levN T i ζ x k) = fun k => ιV PD (LL := LL) (V := T.V) (levB T i ζ x k) :=
    funext fun k => hEq T i ζ x k
  have := congrFun h1 k
  rw [← hEq, W.levN_smul, ← this]
  show smulS (W.lev i ζ a) (fun k => W.levN T i ζ x k) k = _
  rw [h2]

structure Comparison₂ : Prop where
  hEq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
    W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levB T i ζ x k)
  hsupp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)), ∃ m : ℤ, ∀ k < m, levB T i ζ x k = 0
  hcmp : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T)),
    W.cmp T ((letE i : LetA O n) • x) = levB T i 1 x 0
  hΓ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T W.gam (x : W.DD T) ∈ W.N T) (k : ℤ),
    levB T i 1 ⟨W.γD T W.gam (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ W.gam : O)) ^ k • levB T i 1 x k
  hφ : Formalism.MainNotions.UnusedSlot80.LevR.LevBφ W levB
  hlevφ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
    W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f)
  hneg : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T)) (k : ℤ), k < 0 →
    levB T i 1 ((letE i : LetA O n) • x) k = 0

variable {W levB}

theorem smulS_vanish {V : Type} [AddCommGroup V] [Module LL V] {f : ℤ → V} (hf : LB 0 f)
    {g : PowerSeries LL} {N : ℕ} (hg : ∀ i < N, PowerSeries.coeff i g = 0) (k : ℤ) (hk : k < N) :
    smulS g f k = 0 := by
  have hf0 : ∀ k < (0 : ℤ), f k = 0 := hf
  rw [smulS_eq_sum hf g k (k.toNat + 1) (by omega)]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  by_cases hj : j < N
  · rw [hg j hj, zero_smul]
  · rw [hf0 (k - j) (by omega), smul_zero]

theorem level_one_uniformizer_coeff_vanish (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (c : ZMod n) (r : ℕ) :
    ∀ i < (PD.p - 1) * r, PowerSeries.coeff i (W.lev c 1 (W.π₀ ^ r)) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π c 1 ⟨0, by simp⟩
  have hπ : PowerSeries.constantCoeff (W.lev c 1 letπ) = 0 := by
    have := congrArg PowerSeries.constantCoeff hE
    rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at this
    linear_combination this
  obtain ⟨q₁, hq₁⟩ := PowerSeries.X_dvd_iff.2 hπ
  obtain ⟨w, hw⟩ := (Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR).1
  have hdvd : (PowerSeries.X : PowerSeries LL) ^ ((PD.p - 1) * r) ∣ W.lev c 1 (W.π₀ ^ r) := by
    rw [hw, map_pow, map_mul, map_pow, hq₁, mul_pow]
    exact ⟨W.lev c 1 (w : LetA O n) ^ r * (q₁ ^ (PD.p - 1)) ^ r, by rw [mul_pow, ← pow_mul]; ring⟩
  exact PowerSeries.X_pow_dvd_iff.1 hdvd

theorem chi_pow_ne (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hTc : IsCrys PD T.ρ) (c : ZMod n) (k : ℤ) (hk : 0 < k) :
    (algebraMap O LL (W.χΓ W.gam : O)) ^ k ≠ 1 := by
  intro h1
  have hv := (hH hCA T hTc c).2.1 k.toNat (by omega)
  have e1 : algebraMap O LL (Formalism.MainNotions.LiftingTheory.u₁ W ^ k.toNat - 1) = 0 := by
    rw [map_sub, map_one, map_pow, Formalism.MainNotions.LiftingTheory.u₁, map_pow]
    have : (algebraMap O LL (W.χΓ W.gam : O)) ^ (k.toNat : ℤ) = 1 := by
      rwa [show ((k.toNat : ℕ) : ℤ) = k by omega]
    rw [zpow_natCast] at this
    show ((algebraMap O LL ((W.χΓ W.gam : Oˣ) : O)) ^ (PD.p - 1)) ^ k.toNat - 1 = 0
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow, sub_self]
  rw [e1, AddValuation.map_zero] at hv
  exact WithTop.top_ne_coe hv

theorem vecB_letter (T : LocLat G Qp LL O) (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b) (y : Fin d → O) :
    (letE c : LetA O n) • Formalism.MainNotions.LiftingTheory.vecB W T b y = Formalism.MainNotions.LiftingTheory.vecB W T b y := by
  have key : ∀ m, (letE c : LetA O n) • b m = b m := by
    intro m
    obtain ⟨a, ⟨ha, hx⟩, -⟩ := hb.2 (b m) (hb.1 m)
    rw [hx, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    rw [smul_smul, (ha m').2]
  unfold Formalism.MainNotions.LiftingTheory.vecB
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [smul_comm, key m]

theorem hor_exp [IsDomain O] (Ti : Comparison₂ W levB) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) (c' : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (sol : Fin d → ℕ → Fin d → LL)
    (hsol : ∀ k, Formalism.MainNotions.LiftingTheory.IsSol W T c' b 0 (sol k) ∧ sol k 0 = Pi.single k 1) (M κ : ℕ) (j : Fin d)
    {Hh : W.DD T} (hHh : IsHorTr W T b sol M κ j Hh) (hHN : Hh ∈ W.N T) :
    ∀ k : ℤ, k < (((PD.p - 1) * M : ℕ) : ℤ) → levB T c' 1 ⟨Hh, hHN⟩ k =
      if k = 0 then ((PD.p : LL) ^ κ) • cmpD W T (b j) else 0 := by
  obtain ⟨y, hy, hHe⟩ := hHh
  have hl : (letE c' : LetA O n) • Hh = Hh := by
    rw [hHe, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_comm, vecB_letter T c' b hb]
  have hx : (letE c' : LetA O n) • (⟨Hh, hHN⟩ : ↥(W.N T)) = ⟨Hh, hHN⟩ := Subtype.ext hl
  intro k hk
  rcases lt_trichotomy k 0 with hneg | rfl | hpos
  · rw [if_neg (by omega), ← hx]; exact Ti.hneg T hTc c' _ k hneg
  · rw [if_pos rfl, ← Ti.hcmp T hTc c' ⟨Hh, hHN⟩, hx, ← Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hHN]
    have hM : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · rw [h, mul_zero] at hk; exact absurd hk (by omega)
      · exact h
    have hH0 : Hh = ∑ m, (∑ r ∈ Finset.range M, W.π₀ ^ r * algebraMap O (LetA O n) (y r m)) • b m := by
      rw [hHe]
      have := Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc W T 0 M b y
      simpa using this
    rw [hH0, Formalism.MainNotions.UnusedSlot80.LevC.cmpD_sum W T c' _ b (fun m => (hb.1 m).1.1)
      (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2)]
    have hcc : ∀ m, PowerSeries.constantCoeff ((∑ r ∈ Finset.range M, W.π₀ ^ r *
        algebraMap O (LetA O n) (y r m)) c') = y 0 m := by
      intro m
      rw [Finset.sum_apply, map_sum, Finset.sum_eq_single 0]
      · simp [Pi.mul_apply]
      · intro r _ hr
        simp only [Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, show W.π₀ c' = W.π₀₁ from rfl,
          Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR, zero_pow hr, zero_mul]
      · intro h; exact absurd (Finset.mem_range.2 hM) h
    simp only [hcc, hy 0 hM, (hsol j).2]
    rw [Finset.sum_eq_single j]
    · simp
    · intro m _ hm; simp [Pi.single_apply, hm]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg (by omega)]
    obtain ⟨x', hx'Δ, hx'e⟩ := (hsol j).1 M κ y hy
    rw [← hHe, smul_zero, sub_zero] at hx'e
    have hγ : W.γD T W.gam Hh = Hh + W.π₀ ^ M • x' := by
      rw [← hx'e]; show W.γ T Hh = Hh + (W.γ T Hh - Hh); abel
    have hx'N : x' ∈ W.N T := hx'Δ.1.1
    have hγN : W.γD T W.gam Hh ∈ W.N T := by
      rw [hγ]; exact (W.N T).add_mem hHN ((W.N T).smul_mem _ hx'N)
    have e1 : (⟨W.γD T W.gam Hh, hγN⟩ : ↥(W.N T)) = ⟨Hh, hHN⟩ + W.π₀ ^ M • (⟨x', hx'N⟩ : ↥(W.N T)) :=
      Subtype.ext (by simp [hγ])
    have h1 := Ti.hΓ T hTc c' ⟨Hh, hHN⟩ hγN k
    have hx'l : (letE c' : LetA O n) • (⟨x', hx'N⟩ : ↥(W.N T)) = ⟨x', hx'N⟩ :=
      Subtype.ext (Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' hx'Δ.2)
    have hLB : LB 0 (levB T c' 1 ⟨x', hx'N⟩) := fun k hk => by
      rw [← hx'l]; exact Ti.hneg T hTc c' _ k hk
    have hvan := smulS_vanish hLB (level_one_uniformizer_coeff_vanish hR c' M) k hk
    simp only [e1, map_add, Pi.add_apply, levB_smul W levB Ti.hEq Ti.hsupp, hvan, add_zero] at h1
    have h2 : ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1) • levB T c' 1 ⟨Hh, hHN⟩ k = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (chi_pow_ne hH hCA T hTc c' k hpos))

theorem resc_resc {V : Type} [AddCommGroup V] [Module LL V] (a b : LL) (F : ℤ → V) :
    resc a (resc b F) = resc (a * b) F := by
  funext k
  simp only [resc, smul_smul, mul_zpow]

theorem resc_one {V : Type} [AddCommGroup V] [Module LL V] (F : ℤ → V) : resc (1 : LL) F = F := by
  funext k
  simp only [resc, one_zpow, one_smul]

theorem resc_map {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V'] [Module LL V']
    (L : V →ₗ[LL] V') (a : LL) (F : ℤ → V) : resc a (fun k => L (F k)) = fun k => L (resc a F k) := by
  funext k
  simp only [resc, map_smul]

theorem levB_Qφ (Ti : Comparison₂ W levB) (hs : W.s = 1) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) (i : ZMod n)
    (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (z : ↥(W.N T)) (m : ℕ)
    (hz : W.q ^ m • W.φD T (z : W.DD T) ∈ W.N T) :
    levB T i ζ ⟨W.q ^ m • W.φD T (z : W.DD T), hz⟩ =
      smulS (W.lev i ζ (W.q ^ m)) (resc (PD.p : LL)
        (fun k => Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) (levB T (i - 1) (ζ ^ PD.p) z k))) := by
  have hQ : W.Q = W.q := by
    first
    | exact Formalism.MainNotions.LiftingTheory.wmap_Q_one W hs
    | exact Formalism.MainNotions.LiftingTheory.lifta_Q_eq W hs
    | exact Formalism.MainNotions.N.Pv.LocalLengthBound.Q_eq_q hs
  have hx : W.Q ^ m • W.φD T (z : W.DD T) ∈ W.N T := by rw [hQ]; exact hz
  have h1 : (⟨W.q ^ m • W.φD T (z : W.DD T), hz⟩ : ↥(W.N T)) = ⟨W.Q ^ m • W.φD T (z : W.DD T), hx⟩ :=
    Subtype.ext (show W.q ^ m • W.φD T (z : W.DD T) = W.Q ^ m • W.φD T (z : W.DD T) by rw [hQ])
  funext k
  have key := Ti.hφ T hTc i ζ hζ z m hx k
  rw [h1, key, hQ]
  rfl

theorem LB_map {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V'] [Module LL V']
    (L : V →ₗ[LL] V') {m : ℤ} {f : ℤ → V} (hf : LB m f) : LB m (fun k => L (f k)) := by
  have hf0 : ∀ k < m, f k = 0 := hf
  intro k hk
  show L (f k) = 0
  rw [hf0 k hk, map_zero]

variable [IsDomain O]

theorem levB_lam_phi (Ti : Comparison₂ W levB) (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T)
    (y : W.DD T) (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T c' y) :
    ∀ (e : ℕ) (hz : abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y ∈ W.N T),
      levB T (c' + (e : ZMod n)) 1 ⟨_, hz⟩ = smulS (W.lev (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e))
        (resc ((PD.p : LL) ^ e) (fun k => ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ e)
          (levB T c' 1 ⟨y, hy.1.1⟩ k))) := by
  obtain ⟨m₀, hm₀⟩ := Ti.hsupp T c' 1 ⟨y, hy.1.1⟩
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  intro e
  induction e with
  | zero =>
    intro hz
    have e0 : (⟨abelian₂ W A (c' + ((0 : ℕ) : ZMod n)) 0 • ((W.φD T) ^ 0) y, hz⟩ : ↥(W.N T)) = ⟨y, hy.1.1⟩ :=
      Subtype.ext (by simp [Formalism.MainNotions.UnusedSlot80.LevC.lam_zero])
    have hc0 : c' + ((0 : ℕ) : ZMod n) = c' := by simp
    rw [e0, Formalism.MainNotions.UnusedSlot80.LevC.lam_zero, map_one, pow_zero, resc_one, hc0,
      smulS_one (LB_map _ (fun k hk => hm₀ k hk))]
    funext k; simp
  | succ e ih =>
    intro hz
    have hyP : ((W.φD T) ^ e) y ∈ Pp W T c' e := Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T c' e hy
    obtain ⟨z', hz'N, hz'l, hz'e⟩ := Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W hs hR h5 A hA c' hc' e T hT _ hyP
    rw [one_smul] at hz'e
    set z : W.DD T := abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y with hzdef
    have hzN : z ∈ W.N T := by rw [hz'e]; exact hz'N.1
    have hzl : (letE (c' + (e : ZMod n)) : LetA O n) • z = z := by rw [hz'e]; exact hz'l
    have ihz := ih hzN
    set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
    obtain ⟨w, hw, w', hww, hw'⟩ := Formalism.MainNotions.UnusedSlot80.LevC.q_unit W hR hp0
    have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]

    have h5T := h5 T _ _ hT.1 (Formalism.MainNotions.UnusedSlot80.PhiPowers.jumpsLet_of_win W A hA T hT)
    have hQ : W.Q = W.q := by simp [LocWach.Q, hs]
    set i : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with hidef
    have hi1 : i - 1 = c' + (e : ZMod n) := by rw [hidef]; push_cast; ring
    have hzNl : z ∈ W.Nl T (i - 1) := by
      rw [hi1]; exact ⟨z, hzN, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hzl⟩
    have hM := h5T.1 i z hzNl
    rw [hQ] at hM
    have hMH : Formalism.MainNotions.UnusedSlot80.PhiPowers.Mw A.G₀ A.S A.η (A.ty i) ≤ H := by
      have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' (e + 1) (e + 1) (by omega) le_rfl
      rwa [Nat.sub_self] at this
    have hqN : W.q ^ H • W.φD T z ∈ W.N T := by
      obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hMH
      rw [hdd, pow_add, mul_comm, mul_smul]
      exact (W.N T).smul_mem _ hM
    have e1 : (⟨abelian₂ W A i (e + 1) • ((W.φD T) ^ (e + 1)) y, hz⟩ : ↥(W.N T)) =
        w' ^ H • (⟨W.q ^ H • W.φD T z, hqN⟩ : ↥(W.N T)) := by
      apply Subtype.ext
      show abelian₂ W A i (e + 1) • ((W.φD T) ^ (e + 1)) y = w' ^ H • (W.q ^ H • W.φD T z)
      rw [hidef, Formalism.MainNotions.UnusedSlot80.LevC.lam_succ, Formalism.MainNotions.UnusedSlot80.PhiPowers.pow_apply_succ, smul_smul, hzdef, φD_smulA,
        smul_smul, hp0w]
      unfold Formalism.MainNotions.UnusedSlot80.LevC.LamUp
      congr 1; ring
    have hB := levB_Qφ Ti hs T hT.1 i 1 ⟨0, by simp⟩ ⟨z, hzN⟩ H hqN
    rw [one_pow, hi1, ihz] at hB
    rw [e1, levB_smul W levB Ti.hEq Ti.hsupp, hB]

    obtain ⟨m₀, hm₀⟩ := Ti.hsupp T c' 1 ⟨y, hy.1.1⟩
    set F : ℤ → T.V ⊗[Qp] B := fun k => ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ e)
      (levB T c' 1 ⟨y, hy.1.1⟩ k) with hFdef
    have hLB0 : LB m₀ F := LB_map _ (fun k hk => hm₀ k hk)
    set φ1 : T.V ⊗[Qp] B →ₗ[LL] T.V ⊗[Qp] B := Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) with hφ1
    set g₀ : PowerSeries LL := W.lev (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) with hg₀
    have s1 : (fun k => φ1 (smulS g₀ (resc ((PD.p : LL) ^ e) F) k)) =
        smulS g₀ (resc ((PD.p : LL) ^ e) (fun k => φ1 (F k))) := by
      rw [← smulS_map φ1 (LB_resc hLB0 _) g₀, ← resc_map φ1 ((PD.p : LL) ^ e) F]
    have hLB2 : LB m₀ (resc ((PD.p : LL) ^ e) (fun k => φ1 (F k))) := LB_resc (LB_map φ1 hLB0) _
    have hLB3 : LB m₀ (resc ((PD.p : LL) ^ (e + 1)) (fun k => φ1 (F k))) := LB_resc (LB_map φ1 hLB0) _
    rw [s1, ← smulS_rescale hLB2 (PD.p : LL) hp g₀, resc_resc, ← pow_succ', ← smulS_mul hLB3,
      ← smulS_mul hLB3]
    have hLam : W.lev (c' + ((e + 1 : ℕ) : ZMod n)) 1 (w' ^ H) * (W.lev i 1 (W.q ^ H) *
        PowerSeries.rescale (PD.p : LL) g₀) = W.lev (c' + ((e + 1 : ℕ) : ZMod n)) 1
          (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) := by
      rw [Formalism.MainNotions.UnusedSlot80.LevC.lam_succ, map_mul, map_pow, hg₀]
      unfold Formalism.MainNotions.UnusedSlot80.LevC.LamUp
      rw [Ti.hlevφ _ 1 ⟨0, by simp⟩, one_pow, ← hidef, hi1, hp0w, mul_pow, map_mul, map_pow, map_pow]
      ring
    rw [hLam]
    congr 1
    funext k
    simp only [resc, hFdef, hφ1]
    rw [pow_succ' (Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) e, Module.End.mul_apply]

omit [IsDomain O] in
theorem smulS_congr_lt {V : Type} [AddCommGroup V] [Module LL V] {m : ℤ} {F F' : ℤ → V} (hF : LB m F)
    (hF' : LB m F') (g : PowerSeries LL) (N : ℤ) (h : ∀ k < N, F k = F' k) :
    ∀ r < N, smulS g F r = smulS g F' r := by
  intro r hr
  rw [smulS_eq_sum hF g r ((r - m).toNat + 1) (by omega), smulS_eq_sum hF' g r ((r - m).toNat + 1) (by omega)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [h (r - j) (by omega)]

theorem hor_mem (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (sol : Fin d → ℕ → Fin d → LL) (hπ : W.π₀ ∈ W.AΔ) (M κ : ℕ)
    (j : Fin d) {Hh : W.DD T} (hHh : IsHorTr W T b sol M κ j Hh) : Formalism.MainNotions.LiftingTheory.InNΔi W T c' Hh := by
  obtain ⟨y, -, rfl⟩ := hHh
  have hvec : ∀ yy : Fin d → O, Formalism.MainNotions.LiftingTheory.vecB W T b yy ∈ W.NΔ T := by
    intro yy
    refine ⟨(W.N T).sum_mem fun m _ => (W.N T).smul_of_tower_mem _ ((hb.1 m).1.1), fun δ hδ => ?_⟩
    unfold Formalism.MainNotions.LiftingTheory.vecB
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_smul, (hb.1 m).1.2 δ hδ]
  refine ⟨?_, ?_⟩
  · refine ⟨(W.N T).sum_mem fun r _ => (W.N T).smul_mem _ (hvec (y r)).1, fun δ hδ => ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun r _ =>
      (Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T (W.AΔ.pow_mem hπ r) (hvec (y r))).2 δ hδ
  · refine ⟨∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r),
      (W.N T).sum_mem fun r _ => (W.N T).smul_mem _ (hvec (y r)).1, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_comm, vecB_letter T c' b hb]

theorem levB_frame (Ti : Comparison₂ W levB) (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T)
    (e : ℕ) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (y : W.DD T) (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T c' y) (m : ℕ)
    (hZ : W.q ^ m • W.φD T (abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y) ∈ W.N T) :
    levB T (c' + ((e + 1 : ℕ) : ZMod n)) ζ ⟨_, hZ⟩ =
      smulS (W.lev (c' + ((e + 1 : ℕ) : ZMod n)) ζ (W.q ^ m * W.φA (abelian₂ W A (c' + (e : ZMod n)) e)))
        (resc ((PD.p : LL) ^ (e + 1)) (fun k => ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ (e + 1))
          (levB T c' 1 ⟨y, hy.1.1⟩ k))) := by
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  have hyP : ((W.φD T) ^ e) y ∈ Pp W T c' e := Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T c' e hy
  obtain ⟨z', hz'N, -, hz'e⟩ := Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W hs hR h5 A hA c' hc' e T hT _ hyP
  rw [one_smul] at hz'e
  have hzN : abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y ∈ W.N T := by rw [hz'e]; exact hz'N.1
  have hB := levB_Qφ Ti hs T hT.1 (c' + ((e + 1 : ℕ) : ZMod n)) ζ ⟨1, by simpa using hζ⟩ ⟨_, hzN⟩ m hZ
  have hi1 : c' + ((e + 1 : ℕ) : ZMod n) - 1 = c' + (e : ZMod n) := by push_cast; ring
  rw [hζ.pow_eq_one, hi1, levB_lam_phi Ti hs hR hp0 h5 A hA c' hc' T hT y hy e hzN] at hB
  obtain ⟨m₀, hm₀⟩ := Ti.hsupp T c' 1 ⟨y, hy.1.1⟩
  set F : ℤ → T.V ⊗[Qp] B := fun k => ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ e)
    (levB T c' 1 ⟨y, hy.1.1⟩ k) with hFdef
  have hLB0 : LB m₀ F := LB_map _ (fun k hk => hm₀ k hk)
  set φ1 : T.V ⊗[Qp] B →ₗ[LL] T.V ⊗[Qp] B := Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) with hφ1
  set g₀ : PowerSeries LL := W.lev (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) with hg₀
  have s1 : (fun k => φ1 (smulS g₀ (resc ((PD.p : LL) ^ e) F) k)) =
      smulS g₀ (resc ((PD.p : LL) ^ e) (fun k => φ1 (F k))) := by
    rw [← smulS_map φ1 (LB_resc hLB0 _) g₀, ← resc_map φ1 ((PD.p : LL) ^ e) F]
  have hLB2 : LB m₀ (resc ((PD.p : LL) ^ e) (fun k => φ1 (F k))) := LB_resc (LB_map φ1 hLB0) _
  have hLB3 : LB m₀ (resc ((PD.p : LL) ^ (e + 1)) (fun k => φ1 (F k))) := LB_resc (LB_map φ1 hLB0) _
  rw [s1, ← smulS_rescale hLB2 (PD.p : LL) hp g₀, resc_resc, ← pow_succ', ← smulS_mul hLB3] at hB
  have hlev : W.lev (c' + ((e + 1 : ℕ) : ZMod n)) ζ (W.q ^ m * W.φA (abelian₂ W A (c' + (e : ZMod n)) e)) =
      W.lev (c' + ((e + 1 : ℕ) : ZMod n)) ζ (W.q ^ m) * PowerSeries.rescale (PD.p : LL) g₀ := by
    rw [map_mul, Ti.hlevφ _ ζ ⟨1, by simpa using hζ⟩, hζ.pow_eq_one, hi1]
  rw [show (⟨_, hZ⟩ : ↥(W.N T)) = ⟨W.q ^ m • W.φD T ((⟨_, hzN⟩ : ↥(W.N T)) : W.DD T), hZ⟩ from rfl, hB, hlev]
  congr 1
  funext k
  simp only [resc, hFdef, hφ1]
  rw [pow_succ' (Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) e, Module.End.mul_apply]

theorem coeff_lev_q_pow (Ti : Comparison₂ W levB) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (m : ℕ)
    (g : PowerSeries LL) : ∀ i < m, PowerSeries.coeff i (W.lev a ζ (W.q ^ m) * g) = 0 := by
  obtain ⟨u, hu, -⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.lev_q_simple W a ζ hζ
  have hdvd : (PowerSeries.X : PowerSeries LL) ^ m ∣ W.lev a ζ (W.q ^ m) * g := by
    rw [map_pow, hu, mul_pow]
    exact ⟨u ^ m * g, by ring⟩
  exact PowerSeries.X_pow_dvd_iff.1 hdvd

omit [IsDomain O] in
theorem smulS_congr_shift {V : Type} [AddCommGroup V] [Module LL V] {m₁ : ℤ} {F F' : ℤ → V}
    (hF : LB m₁ F) (hF' : LB m₁ F') {g : PowerSeries LL} {m : ℕ} (hg : ∀ i < m, PowerSeries.coeff i g = 0)
    (N : ℤ) (h : ∀ k < N, F k = F' k) : ∀ r < N + m, smulS g F r = smulS g F' r := by
  intro r hr
  rw [smulS_eq_sum hF g r ((r - m₁).toNat + 1) (by omega),
    smulS_eq_sum hF' g r ((r - m₁).toNat + 1) (by omega)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j < m
  · rw [hg j hj, zero_smul, zero_smul]
  · rw [h (r - j) (by omega)]

variable (W levB) in

def ExpFrame0 : Prop :=
  ∀ (A : ArcP n), A.OK → ∀ c' ∈ A.cuts, ∀ (T : LocLat G Qp LL O), Win W A T →
    ∀ {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL), IsHor W T c' b sol →
    ∀ (e : ℕ) (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ (M κ : ℕ) (j : Fin d) (Hh : W.DD T),
    IsHorTr W T b sol M κ j Hh → ∀ (m : ℕ)
    (hZ : W.q ^ m • W.φD T (abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) Hh) ∈ W.N T),
    ∀ r : ℤ, r < (((PD.p - 1) * M : ℕ) : ℤ) + m →
      levB T (c' + ((e + 1 : ℕ) : ZMod n)) ζ ⟨_, hZ⟩ r =
        smulS (W.lev (c' + ((e + 1 : ℕ) : ZMod n)) ζ (W.q ^ m * W.φA (abelian₂ W A (c' + (e : ZMod n)) e)))
          (fun k => if k = 0 then ((PD.p : LL) ^ κ) •
            ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ (e + 1)) (cmpD W T (b j)) else 0) r

variable (W levB) in

def ExpNoNeg0 : Prop :=
  ∀ (A : ArcP n), A.OK → ∀ c' ∈ A.cuts, ∀ (T : LocLat G Qp LL O), Win W A T →
    ∀ (e : ℕ) (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ y : W.DD T, Formalism.MainNotions.LiftingTheory.InNΔi W T c' y → ∀ (m : ℕ)
    (hZ : W.q ^ m • W.φD T (abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y) ∈ W.N T),
    ∀ r : ℤ, r < m → levB T (c' + ((e + 1 : ℕ) : ZMod n)) ζ ⟨_, hZ⟩ r = 0

theorem expFrame0_of (Ti : Comparison₂ W levB) (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) : ExpFrame0 W levB := by
  intro A hA c' hc' T hT d b sol hb e ζ hζ M κ j Hh hHh m hZ r hr
  have hHΔ := hor_mem T c' b hb.1 sol hR.1 M κ j hHh
  rw [levB_frame Ti hs hR hp0 h5 A hA c' hc' T hT e ζ hζ Hh hHΔ m hZ]
  obtain ⟨m₀, hm₀⟩ := Ti.hsupp T c' 1 ⟨Hh, hHΔ.1.1⟩
  set F' : ℤ → T.V ⊗[Qp] B := fun k => if k = 0 then ((PD.p : LL) ^ κ) •
      ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ (e + 1)) (cmpD W T (b j)) else 0 with hF'def
  have hLB4 : LB 0 F' := fun k hk => by rw [hF'def]; simp [show k ≠ 0 by omega]
  have hLB3 : LB m₀ (resc ((PD.p : LL) ^ (e + 1)) (fun k => ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ (e + 1))
      (levB T c' 1 ⟨Hh, hHΔ.1.1⟩ k))) := LB_resc (LB_map _ (fun k hk => hm₀ k hk)) _
  have hexp := hor_exp Ti hR hH hCA T hT.1 c' b hb.1 sol hb.2 M κ j hHh hHΔ.1.1
  have hagree : ∀ k < (((PD.p - 1) * M : ℕ) : ℤ), resc ((PD.p : LL) ^ (e + 1))
      (fun k => ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ (e + 1)) (levB T c' 1 ⟨Hh, hHΔ.1.1⟩ k)) k = F' k := by
    intro k hk
    simp only [resc, hF'def]
    rw [hexp k hk]
    by_cases h0 : k = 0
    · subst h0; simp
    · simp [h0]
  exact smulS_congr_shift (LB_mono hLB3 (min_le_left m₀ 0)) (LB_mono hLB4 (min_le_right m₀ 0))
    (fun i hi => by rw [map_mul]; exact coeff_lev_q_pow Ti _ ζ hζ m _ i hi) _ hagree r hr

theorem expNoNeg0_of (Ti : Comparison₂ W levB) (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) : ExpNoNeg0 W levB := by
  intro A hA c' hc' T hT e ζ hζ y hy m hZ r hr
  rw [levB_frame Ti hs hR hp0 h5 A hA c' hc' T hT e ζ hζ y hy m hZ]
  have hyl : (letE c' : LetA O n) • (⟨y, hy.1.1⟩ : ↥(W.N T)) = ⟨y, hy.1.1⟩ :=
    Subtype.ext (Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' hy.2)
  have hLB : LB 0 (resc ((PD.p : LL) ^ (e + 1)) (fun k => ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ (e + 1))
      (levB T c' 1 ⟨y, hy.1.1⟩ k))) :=
    LB_resc (LB_map _ (fun k hk => by rw [← hyl]; exact Ti.hneg T hT.1 c' _ k hk)) _
  exact smulS_vanish hLB (fun i hi => by rw [map_mul]; exact coeff_lev_q_pow Ti _ ζ hζ m _ i hi) r hr

omit [IsDomain O] in

theorem hneg_of (hs : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hEq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levB T i ζ x k))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (x : ↥(W.N T)) (k : ℤ) (hk : k < 0) :
    levB T i 1 ((letE i : LetA O n) • x) k = 0 := by
  have hX : PowerSeries.constantCoeff (W.lev i 1 W.X) = 0 := by
    have hX1 : W.X = letπ := by simp [LocWach.X, hs]
    obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 ⟨0, by simp⟩
    have := congrArg PowerSeries.constantCoeff hE
    rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at this
    rw [hX1]
    linear_combination this
  have hcl := ((h4 T hT).1 i 1 ⟨0, by simp⟩ hX).1 ((letE i : LetA O n) • x) k
  apply Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (LL := LL) (V := T.V)
  rw [← hEq, map_zero]
  exact hcl.2 hk

omit [IsDomain O] in
theorem hΓ_of (hΓ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • levB T i ζ' x k)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T W.gam (x : W.DD T) ∈ W.N T) (k : ℤ) :
    levB T i 1 ⟨W.γD T W.gam (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ W.gam : O)) ^ k • levB T i 1 x k := by
  refine hΓ T hT W.gam i 1 1 0 1 (by simp) ?_ (by simp) x hx k
  rw [Nat.cast_one, W.gam_gen]
  simp

end Formalism.MainNotions.UnusedSlot80.LevE

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem levETie_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4L D.loc HW D.locA F Cm) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) :
    LevE.Comparison₂ ((HW l).W K 1 LL hG) ((Cm l).C K 1 LL hG).tie.levB :=
  ⟨((Cm l).C K 1 LL hG).tie.levN_eq, ((Cm l).C K 1 LL hG).tie.levB_supp, ((Cm l).C K 1 LL hG).tie.cmp_eq,
    LevE.hΓ_of ((Cm l).C K 1 LL hG).tie.levB_Γ, ((Cm l).C K 1 LL hG).tie.levB_φ,
    ((Cm l).C K 1 LL hG).tie.lev_φ,
    LevE.hneg_of ((HW l).W_s K 1 LL hG) (h4 l K 1 LL hG) ((Cm l).C K 1 LL hG).tie.levN_eq⟩

end Formalism.MainNotions.UnusedSlot80
