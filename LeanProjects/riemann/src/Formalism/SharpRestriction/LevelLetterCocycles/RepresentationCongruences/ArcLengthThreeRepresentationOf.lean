import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AlgebraMapMemInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PpLeHLD
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.JumpsLetOfWin

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DFE

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem intpow (hvl : v (PD.p : LL) = 1) (x : LL) :
    ∃ t : ℕ, ∀ t', t ≤ t' → 0 ≤ v ((PD.p : LL) ^ t' * x) := by
  by_cases hx : x = 0
  · exact ⟨0, fun t' _ => by rw [hx, mul_zero, AddValuation.map_zero]; exact le_top⟩
  · have hne : v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
    refine ⟨⌈-q⌉₊, fun t' ht' => ?_⟩
    rw [AddValuation.map_mul, AddValuation.map_pow, hvl, ← hq, ← WithTop.coe_one,
      ← WithTop.coe_nsmul, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
    have h1 := Nat.le_ceil (-q)
    have h2 : (⌈-q⌉₊ : ℚ) ≤ t' := by exact_mod_cast ht'
    rw [nsmul_eq_mul, mul_one]
    linarith

variable [FiniteDimensional Qp LL] (W : LocWach PD LL O v n)

theorem Pp_φ (T : LocLat G Qp LL O) (c : ZMod n) (j : ℕ) :
    ∀ y ∈ Pp W T c j, W.φD T y ∈ Pp W T c (j + 1) := by
  refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T c j _ (by rw [map_zero]; exact (Pp W T c (j + 1)).zero_mem)
    (fun x y hx hy => by rw [map_add]; exact (Pp W T c (j + 1)).add_mem hx hy)
    (fun x hx => by rw [map_neg]; exact (Pp W T c (j + 1)).neg_mem hx) ?_
  intro a ha x hx
  have e : W.φD T (((W.φD T) ^ j) x) = ((W.φD T) ^ (j + 1)) x := by
    rw [pow_succ', Module.End.mul_apply]
  rw [DYB.φD_smulA, e]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c (j + 1) (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_mem_AΔ W ha) hx

theorem φD_lsmul (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    W.φD T (lA W ^ k • x) = lA W ^ k • W.φD T x := by
  rw [← Formalism.MainNotions.UnusedSlot80.Relay2.lsmul_eq, ← Formalism.MainNotions.UnusedSlot80.Relay2.lsmul_eq, map_smul]

end Formalism.MainNotions.N.FrobeniusPowerSeries.DFE

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_representation_of [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (f₂ : W.EE) (hf₂ : InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂)
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh))) :
    (∃ a₀ ∈ W.AΔ, algebraMap (LetA O n) W.EE (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c)) * f₂ = algebraMap (LetA O n) W.EE a₀) ∧
      InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) 1 (W.φD T₂ lam) ∧
      RepVV W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) ((arcOf b w S η up size).M PD.p) (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c)) bb sol (f₂ • W.φD T₂ lam)
        (fun k => if k = k₀ then lE W ((arcOf b w S η up size).σ PD.p) * f₂ else 0) := by
  set A := arcOf b w S η up size with hAdef
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  rw [hlen]
  have hπ : W.π₀ ∈ W.AΔ := (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W hP9 hcase T₂ hW₂.1).1.1
  have hE : (letE (O := O) c : LetA O n) ∈ W.AΔ := Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W c
  have hps : ∀ s k : ℕ, ps W s ^ k ∈ W.AΔ := fun s k => W.AΔ.pow_mem (TypesA.ps_mem W s) k
  have hlA : ∀ k : ℕ, lA W ^ k ∈ W.AΔ := fun k => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.Relay2.lA_mem W) k
  have hj : A.j = 1 := rfl
  have hth : ∀ i, A.ty i ≠ Formalism.MainNotions.LocalTheoryWindows.LT.thin := by
    intro i
    show (if up i = true then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i)) ≠
      Formalism.MainNotions.LocalTheoryWindows.LT.thin
    split <;> intro h <;> cases h
  have h0 : ∀ s, s < 2 → A.Hs c 3 s = A.h := by
    intro s hs
    unfold ArcP.Hs
    rw [if_neg]
    rintro (h | h)
    · exact hth _ h
    · omega
  have h2 : A.Hs c 3 2 = A.G₀ := by
    unfold ArcP.Hs
    rw [if_pos (Or.inr (by omega))]
  have hLam : abelian₂ W A c 3 = ps W 0 ^ A.h * ps W 1 ^ A.h * ps W 2 ^ A.G₀ := by
    unfold abelian₂
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one, h0 0 (by norm_num),
      h0 1 (by norm_num), h2]
  have hb1 : size (c - 1) + S ≤ A.h := by
    have hthk : (A.ty (c - 1)).thick = true := by
      show (if up (c - 1) = true then Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1))
        else Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 1))).thick = true
      split <;> rfl
    have hsz : (A.ty (c - 1)).size = size (c - 1) := by
      show (if up (c - 1) = true then Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1))
        else Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 1))).size = size (c - 1)
      split <;> rfl
    have h8 := hOK.2.2.2.2.2.2.2.1 (c - 1) hthk
    rw [hsz] at h8
    exact h8
  have hp2 : 2 ≤ PD.p := PD.hp.two_le
  have hM2 : 2 * A.h < (PD.p - 1) * A.M PD.p := by
    show 2 * A.h < (PD.p - 1) * (2 * A.h / (PD.p - 1) + 1)
    have e1 := Nat.div_add_mod (2 * A.h) (PD.p - 1)
    have e2 := Nat.mod_lt (2 * A.h) (show PD.p - 1 > 0 by omega)
    rw [mul_add, mul_one]
    generalize (PD.p - 1) * (2 * A.h / (PD.p - 1)) = Z at e1 ⊢
    generalize 2 * A.h % (PD.p - 1) = r at e1 e2
    omega
  obtain ⟨j₁, hj₁⟩ : ∃ j, A.h = size (c - 1) + j := ⟨A.h - size (c - 1), by omega⟩
  obtain ⟨k₁, hk₁⟩ : ∃ k, (PD.p - 1) * A.M PD.p = A.h + size (c - 1) + k := by
    generalize (PD.p - 1) * A.M PD.p = X at hM2 ⊢
    exact ⟨X - (A.h + size (c - 1)), by omega⟩
  obtain ⟨m₁, hm₁⟩ : ∃ m, A.M PD.p = m + 1 := ⟨2 * A.h / (PD.p - 1), rfl⟩

  obtain ⟨uf, huf, hf₂e⟩ := hf₂
  obtain ⟨a₀, ha₀e⟩ : ∃ a, a = ps W 0 ^ A.h * ps W 1 ^ j₁ * ps W 2 ^ A.G₀ *
      ((letE (O := O) c : LetA O n) * ps W 2 ^ (size (c - 2) + S) * uf) := ⟨_, rfl⟩
  have ha₀ : a₀ ∈ W.AΔ := by
    rw [ha₀e]
    exact W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (hps 0 _) (hps 1 _)) (hps 2 _))
      (W.AΔ.mul_mem (W.AΔ.mul_mem hE (hps 2 _)) huf)
  have hΛf : algebraMap (LetA O n) W.EE (abelian₂ W A c 3) * f₂ = algebraMap (LetA O n) W.EE a₀ := by
    have hsp : ps W 1 ^ A.h = ps W 1 ^ j₁ * ps W 1 ^ size (c - 1) := by
      rw [← pow_add, hj₁, add_comm]
    calc algebraMap (LetA O n) W.EE (abelian₂ W A c 3) * f₂
        = algebraMap (LetA O n) W.EE (ps W 0 ^ A.h * ps W 1 ^ j₁ * ps W 2 ^ A.G₀) *
          (algebraMap (LetA O n) W.EE (ps W 1 ^ size (c - 1)) * f₂) := by
          rw [hLam, hsp]; simp only [map_mul]; ring
      _ = algebraMap (LetA O n) W.EE (ps W 0 ^ A.h * ps W 1 ^ j₁ * ps W 2 ^ A.G₀) *
          algebraMap (LetA O n) W.EE ((letE (O := O) c : LetA O n) * ps W 2 ^ (size (c - 2) + S) * uf) := by
          rw [hf₂e]
      _ = algebraMap (LetA O n) W.EE a₀ := by rw [ha₀e]; exact (map_mul _ _ _).symm

  have hc2 : InFP W T₂ c' 3 1 (W.φD T₂ lam) := by
    obtain ⟨y, hy, hly⟩ := hlam
    exact ⟨W.φD T₂ y, DFE.Pp_φ W T₂ c' 2 y hy, by rw [hly, one_smul, one_smul]⟩
  refine ⟨⟨a₀, ha₀, hΛf⟩, hc2, ?_⟩

  obtain ⟨κ', y₂, hy₂P, hy₂e⟩ := h4a
  have e3 : W.φD T₂ (((W.φD T₂) ^ 2) Hh) = ((W.φD T₂) ^ 3) Hh := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ' (W.φD T₂) 2, Module.End.mul_apply]
  have hφ : lA W ^ κ' • (lA W ^ κ • W.φD T₂ lam - lA W ^ A.σ PD.p • ((W.φD T₂) ^ 3) Hh) =
      W.φA (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p))) • W.φD T₂ y₂ := by
    have h := congrArg (W.φD T₂) hy₂e
    rw [DFE.φD_lsmul, map_sub, DFE.φD_lsmul, DFE.φD_lsmul, e3, DYB.φD_smulA] at h
    exact h
  obtain ⟨t, ht⟩ : ∃ t : ℕ, ∀ (k : Fin d) (r : Fin (A.M PD.p)) (mm : Fin d),
      0 ≤ v ((PD.p : LL) ^ (κ + t) * sol k r mm) := by
    choose tf htf using fun (q : Fin d × Fin (A.M PD.p) × Fin d) =>
      DFE.intpow (v := v) (PD := PD) W.v_l (sol q.1 q.2.1 q.2.2)
    refine ⟨∑ q, tf q, fun k r mm => htf (k, r, mm) _ ?_⟩
    exact le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (k, r, mm)))
      (Nat.le_add_left _ _)
  choose yy hyy using fun (k : Fin d) (r : Fin (A.M PD.p)) (mm : Fin d) => hOv _ (ht k r mm)
  let Y : Fin d → ℕ → Fin d → O := fun k r mm => if h : r < A.M PD.p then yy k ⟨r, h⟩ mm else 0
  have hY : ∀ k, ∀ r < A.M PD.p, ∀ mm, algebraMap O LL (Y k r mm) = (PD.p : LL) ^ (κ + t) * sol k r mm := by
    intro k r hr mm
    simp only [Y, dif_pos hr]
    exact hyy k ⟨r, hr⟩ mm
  let Hh' : Fin d → W.DD T₂ := fun k =>
    ∑ r ∈ Finset.range (A.M PD.p), W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T₂ bb (Y k r)
  have hHh' : ∀ k, IsHorTr W T₂ bb sol (A.M PD.p) (κ + t) k (Hh' k) := fun k => ⟨Y k, hY k, rfl⟩
  have hk₀' : Hh' k₀ = lA W ^ t • Hh :=
    TypesA.IsHorTr_unique W (hHh' k₀) (TypesA.IsHorTr_smul W t hHh)

  obtain ⟨u, hu, u', hu', huu', hTr2⟩ := (hTr hcase).2.1 2 (A.M PD.p)
  have hpk : ∀ k, Formalism.MainNotions.LiftingTheory.pk W k = ps W k := fun k => rfl
  have hps2 : W.φA (W.φA (Formalism.MainNotions.LiftingTheory.pk W 0)) = ps W 2 := by
    first
    | rfl
    | (simp only [Formalism.MainNotions.LiftingTheory.pk, ps, pow_zero, AlgHom.one_apply, pow_two, AlgHom.mul_apply] <;> rfl)
  have hJJ : W.φA (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p))) =
      ((W.φA ^ 2) W.π₀) ^ A.M PD.p * ps W 2 ^ (2 * A.G₀) := by
    simp only [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, map_mul, map_pow]
    rw [hps2, pow_two, AlgHom.mul_apply]
  obtain ⟨t₀, ht₀e⟩ : ∃ x, x = u * uf * (letE (O := O) c : LetA O n) * W.π₀ ^ m₁ *
      ps W 0 ^ (size (c - 1) + k₁) * ps W 1 ^ k₁ * ps W 2 ^ (A.G₀ + (size (c - 2) + S)) := ⟨_, rfl⟩
  have ht₀ : t₀ ∈ W.AΔ := by
    rw [ht₀e]
    exact W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem
      (W.AΔ.mul_mem hu huf) hE) (W.AΔ.pow_mem hπ _)) (hps 0 _)) (hps 1 _)) (hps 2 _)
  have hring : a₀ * W.φA (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p))) =
      W.π₀ * abelian₂ W A c 3 ^ 2 * t₀ := by
    rw [hJJ, hTr2, Finset.prod_range_succ, Finset.prod_range_one, hpk, hpk, hLam, ha₀e, ht₀e, hk₁,
      hm₁, hj₁]
    ring
  obtain ⟨aa, haa⟩ : ∃ aa : Fin d → LetA O n,
      aa = fun k => if k = k₀ then lA W ^ A.σ PD.p * a₀ else 0 := ⟨_, rfl⟩
  have hsum : ∑ k, aa k • ((W.φD T₂) ^ 3) (Hh' k) =
      (lA W ^ A.σ PD.p * a₀) • ((W.φD T₂) ^ 3) (lA W ^ t • Hh) := by
    rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [haa]; dsimp only; rw [if_neg hk, zero_smul])
      (fun h => absurd (Finset.mem_univ k₀) h), haa]
    dsimp only
    rw [if_pos rfl, hk₀']
  have hΛx : abelian₂ W A c 3 • (f₂ • W.φD T₂ lam) = a₀ • W.φD T₂ lam := by
    rw [← algebraMap_smul W.EE (abelian₂ W A c 3), smul_smul, hΛf, algebraMap_smul]
  have hφy : W.φD T₂ y₂ ∈ Pp W T₂ c' 3 := DFE.Pp_φ W T₂ c' 2 y₂ hy₂P
  refine ⟨κ + t, κ', Hh', aa, hHh', fun k => ?_, ?_⟩
  · subst haa
    dsimp only
    split_ifs with hk
    · refine ⟨W.AΔ.mul_mem (hlA _) ha₀, ?_⟩
      rw [map_mul, ← hΛf]
      simp only [lE, lA, map_pow, map_natCast]
      ring
    · exact ⟨W.AΔ.zero_mem, by rw [mul_zero, map_zero]⟩
  · refine ⟨(lA W ^ t * t₀) • W.φD T₂ y₂,
      Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T₂ c' 3 (W.AΔ.mul_mem (hlA _) ht₀) _ hφy, ?_⟩
    rw [hsum, hΛx, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul]
    refine (?_ : _ = (lA W ^ t * a₀) • (lA W ^ κ' • (lA W ^ κ • W.φD T₂ lam -
      lA W ^ A.σ PD.p • ((W.φD T₂) ^ 3) Hh))).trans ?_
    · first
      | module
      | (simp only [smul_sub, smul_smul]; congr 1 <;> congr 1 <;> ring)
    · rw [hφ, smul_smul, smul_smul]
      congr 1
      linear_combination lA W ^ t * hring

end Formalism.MainNotions.N.FrobeniusPowerSeries
