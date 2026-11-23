import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.PhiPowers

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem pow_apply_succ (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    ((W.φD T) ^ (k + 1)) x = W.φD T (((W.φD T) ^ k) x) := by
  rw [pow_succ', Module.End.mul_apply]

theorem φD_pow_letter (T : LocLat G Qp LL O) (c : ZMod n) (x : W.DD T)
    (hx : (letE c : LetA O n) • x = x) (k : ℕ) :
    (letE (c + (k : ZMod n)) : LetA O n) • ((W.φD T) ^ k) x = ((W.φD T) ^ k) x := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have h1 := φA_letE W (c + ((k + 1 : ℕ) : ZMod n))
    rw [show c + ((k + 1 : ℕ) : ZMod n) - 1 = c + (k : ZMod n) by push_cast; ring] at h1
    rw [pow_apply_succ, ← h1, ← φD_smulA, ih]

theorem chain (hs : W.s = 1) (T : LocLat G Qp LL O) {M h : ZMod n → ℕ}
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (c : ZMod n) (Gb j : ℕ)
    (hM : ∀ k : ℕ, 1 ≤ k → k ≤ j → M (c + (k : ZMod n)) ≤ Gb) (x : W.DD T) (hx : x ∈ W.N T)
    (hxc : (letE c : LetA O n) • x = x) :
    ∀ k, k ≤ j → (∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ Gb) • ((W.φD T) ^ k) x ∈ W.N T := by
  have hQ : W.Q = W.q := by simp [LocWach.Q, hs]
  intro k
  induction k with
  | zero =>
    intro _
    simpa using hx
  | succ k ih =>
    intro hk
    have hzk := ih (by omega)
    have hlet : (letE (c + (k : ZMod n)) : LetA O n) •
        ((∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ Gb) • ((W.φD T) ^ k) x) =
        (∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ Gb) • ((W.φD T) ^ k) x := by
      rw [smul_comm, φD_pow_letter W T c x hxc k]
    have hNl : (∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ Gb) • ((W.φD T) ^ k) x ∈
        W.Nl T (c + ((k + 1 : ℕ) : ZMod n) - 1) := by
      rw [show c + ((k + 1 : ℕ) : ZMod n) - 1 = c + (k : ZMod n) by push_cast; ring]
      exact Submodule.mem_map.2 ⟨_, hzk, by rw [LinearMap.smul_apply, LinearMap.id_apply, hlet]⟩
    have h1 := h5.1 (c + ((k + 1 : ℕ) : ZMod n)) _ hNl
    have hM' := hM (k + 1) (by omega) hk
    have hφP : W.φA (∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ Gb) =
        ∏ s ∈ Finset.range k, ((W.φA ^ (s + 1)) W.q) ^ Gb := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [map_pow, pow_succ', AlgHom.mul_apply]
    have hP : ∏ s ∈ Finset.range (k + 1), ((W.φA ^ s) W.q) ^ Gb =
        W.q ^ (Gb - M (c + ((k + 1 : ℕ) : ZMod n))) *
          (W.q ^ M (c + ((k + 1 : ℕ) : ZMod n)) *
            W.φA (∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ Gb)) := by
      rw [Finset.prod_range_succ', hφP, pow_zero, AlgHom.one_apply, ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel hM', mul_comm]
    rw [hP, mul_smul, mul_smul, pow_apply_succ, ← φD_smulA]
    rw [hQ] at h1
    exact (W.N T).smul_mem _ h1

def Mw (G₀ S η : ℕ) : Formalism.MainNotions.LocalTheoryWindows.LT → ℕ
  | .thin => G₀
  | .up _ => η
  | .down b => b + S

def Hw (G₀ S η : ℕ) : Formalism.MainNotions.LocalTheoryWindows.LT → ℕ
  | .thin => G₀
  | .up b => b + S
  | .down _ => η

theorem win_sub (G₀ S η : ℕ) (t : Formalism.MainNotions.LocalTheoryWindows.LT) (ht : t.ok η) :
    t.win G₀ S η ⊆ Set.Icc (-(Mw G₀ S η t : ℤ)) (Hw G₀ S η t) := by
  intro x hx
  cases t with
  | thin =>
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_Icc] at hx
    simp only [Mw, Hw, Set.mem_Icc]
    omega
  | up b =>
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at ht
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hx
    simp only [Mw, Hw, Set.mem_Icc]
    push_cast
    omega
  | down b =>
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at ht
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hx
    simp only [Mw, Hw, Set.mem_Icc]
    push_cast
    omega

theorem jumpsLet_of_win (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (T : LocLat G Qp LL O)
    (hT : Formalism.MainNotions.ArcLiftingSetup.Win W A T) :
    Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T (fun i => Mw A.G₀ A.S A.η (A.ty i)) (fun i => Hw A.G₀ A.S A.η (A.ty i)) := by
  intro τ i hτ
  have h1 := hT.2 i τ hτ
  have h2 := win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i)
  unfold JumpsInV at h1 ⊢
  exact fun a ha => h2 (h1 a ha)

theorem mw_le (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) (k : ℕ)
    (hk1 : 1 ≤ k) (hkj : k ≤ A.j) : Mw A.G₀ A.S A.η (A.ty (c + (k : ZMod n))) ≤ A.G₀ := by
  rcases hA.2.2.2.2.2.2.2.2 with h | ⟨hj, hth, hsz⟩
  · simp [h c hc k hk1 hkj, Mw]
  · have hk : k = 1 := by omega
    subst hk
    rw [Nat.cast_one]
    have hok := hA.2.2.2.2.1 (c + 1)
    have hs := hsz c hc
    have ht := hth (c + 1)
    generalize A.ty (c + 1) = t at hok hs ht ⊢
    cases t with
    | thin => simp [Formalism.MainNotions.LocalTheoryWindows.LT.thick] at ht
    | up b =>
      simp only [Mw, Formalism.MainNotions.LocalTheoryWindows.LT.ok, Formalism.MainNotions.LocalTheoryWindows.LT.size] at hok hs ⊢
      omega
    | down b =>
      simp only [Mw, Formalism.MainNotions.LocalTheoryWindows.LT.ok, Formalism.MainNotions.LocalTheoryWindows.LT.size] at hok hs ⊢
      omega

theorem φA_mem_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) : W.φA a ∈ W.AΔ := by
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  show ∀ δ ∈ W.DelF, W.γA δ (W.φA a) = W.φA a
  intro δ hδ
  have h1 : W.γA δ (W.φA a) = W.φA (W.γA δ a) := by
    funext i
    exact (W.γ₀_comm δ (a (i - 1))).symm
  rw [h1, ha' δ hδ]

theorem φA_pow_mem_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) (s : ℕ) : (W.φA ^ s) a ∈ W.AΔ := by
  induction s with
  | zero => simpa using ha
  | succ s ih =>
    rw [pow_succ', AlgHom.mul_apply]
    exact φA_mem_AΔ W ih

theorem ps_mem_AΔ (hπ : W.π₀ ∈ W.AΔ) (s : ℕ) : Formalism.MainNotions.ArcLiftingSetup.ps W s ∈ W.AΔ :=
  φA_pow_mem_AΔ W (show Formalism.MainNotions.ArcLiftingSetup.qA W ∈ W.AΔ from W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)) s

theorem smul_mem_NΔ (T : LocLat G Qp LL O) {a : LetA O n} (ha : a ∈ W.AΔ) {z : W.DD T}
    (hz : z ∈ W.NΔ T) : a • z ∈ W.NΔ T := by
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  have hz' : z ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ z = z := hz
  show a • z ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (a • z) = a • z
  refine ⟨(W.N T).smul_mem a hz'.1, fun δ hδ => ?_⟩
  rw [γD_smulA, ha' δ hδ, hz'.2 δ hδ]

theorem φD_pow_Δ (T : LocLat G Qp LL O) {x : W.DD T} (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) (k : ℕ) :
    ∀ δ ∈ W.DelF, W.γD T δ (((W.φD T) ^ k) x) = ((W.φD T) ^ k) x := by
  induction k with
  | zero =>
    intro δ hδ
    simpa using hx δ hδ
  | succ k ih =>
    intro δ hδ
    rw [pow_apply_succ, ← W.φγ_comm, ih δ hδ]

theorem eat_eq : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
    Formalism.MainNotions.ArcLiftingSetup.qA W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.ArcLiftingSetup.qA, Formalism.MainNotions.ArcLiftingSetup.lA]

theorem prod_q_eq (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (k Gb : ℕ) :
    ∃ u : LetA O n, IsUnit u ∧ ∏ s ∈ Finset.range k, ((W.φA ^ s) W.q) ^ Gb =
      u * ∏ s ∈ Finset.range k, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ Gb := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [eat_eq] at hw
  refine ⟨∏ s ∈ Finset.range k, ((W.φA ^ s) (w : LetA O n)) ^ Gb, ?_, ?_⟩
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun s _ => ((Units.isUnit w).map (W.φA ^ s)).pow Gb)
  · rw [hw, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_mul, mul_pow]
    rfl

private theorem letE_mul_self_level_letter_cocycles (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext k
  simp only [letE, Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

theorem prodPs_mem (hs : W.s = 1) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (T : LocLat G Qp LL O)
    {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (c : ZMod n) (Gb j : ℕ)
    (hM : ∀ k : ℕ, 1 ≤ k → k ≤ j → M (c + (k : ZMod n)) ≤ Gb) (x : W.DD T)
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) :
    (∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ Gb) • ((W.φD T) ^ j) x ∈ W.NΔ T ∧
      (letE (c + (j : ZMod n)) : LetA O n) •
        ((∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ Gb) • ((W.φD T) ^ j) x) =
        (∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ Gb) • ((W.φD T) ^ j) x := by
  have hxN : x ∈ W.N T := hx.1.1
  have hxΔ : ∀ δ ∈ W.DelF, W.γD T δ x = x := hx.1.2
  have hxl : x ∈ W.Nl T c := hx.2
  have hxc : (letE c : LetA O n) • x = x := by
    obtain ⟨y, _, hy⟩ := Submodule.mem_map.1 hxl
    rw [← hy, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, letE_mul_self_level_letter_cocycles]
  have hch := chain W hs T h5 c Gb j hM x hxN hxc j le_rfl
  obtain ⟨u, hu, hueq⟩ := prod_q_eq W hR j Gb
  rw [hueq, mul_smul] at hch
  obtain ⟨u', rfl⟩ := hu
  have hPN : (∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ Gb) • ((W.φD T) ^ j) x ∈ W.N T := by
    have h3 := (W.N T).smul_mem (↑u'⁻¹ : LetA O n) hch
    rwa [smul_smul (↑u'⁻¹ : LetA O n) (↑u' : LetA O n), Units.inv_mul, one_smul] at h3
  have hπ : W.π₀ ∈ W.AΔ := hR.1
  have hPA : (∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ Gb) ∈ W.AΔ :=
    prod_mem fun s _ => pow_mem (ps_mem_AΔ W hπ s) _
  have hPA' : ∀ δ ∈ W.DelF, W.γA δ (∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ Gb) =
      ∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ Gb := hPA
  refine ⟨⟨hPN, fun δ hδ => ?_⟩, ?_⟩
  · rw [γD_smulA, hPA' δ hδ, φD_pow_Δ W T hxΔ j δ hδ]
  · rw [smul_comm, φD_pow_letter W T c x hxc j]

theorem relay_first (hs : W.s = 1) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) (T : LocLat G Qp LL O)
    (hT : Formalism.MainNotions.ArcLiftingSetup.Win W A T) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c A.j,
      Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c + (A.j : ZMod n)) (W.π₀ ^ A.M PD.p)
        (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p) • y) ∧
      Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c + (A.j : ZMod n)) 1
        ((∏ s ∈ Finset.range A.j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ A.G₀) • y) := by
  have h5' := h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  have hM : ∀ k : ℕ, 1 ≤ k → k ≤ A.j →
      Mw A.G₀ A.S A.η (A.ty (c + (k : ZMod n))) ≤ A.G₀ :=
    fun k hk1 hkj => mw_le A hA c hc k hk1 hkj
  have hπ : W.π₀ ∈ W.AΔ := hR.1
  set P := ∏ s ∈ Finset.range A.j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ A.G₀ with hPdef
  have hPA : P ∈ W.AΔ := prod_mem fun s _ => pow_mem (ps_mem_AΔ W hπ s) _
  have key : ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c A.j, P • y ∈ W.NΔ T ∧
      (letE (c + (A.j : ZMod n)) : LetA O n) • (P • y) = P • y := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨h1, h2⟩ := prodPs_mem W hs hR T h5' c A.G₀ A.j hM x hx
      rw [smul_comm P a]
      refine ⟨smul_mem_NΔ W T ha h1, ?_⟩
      rw [smul_comm (letE (c + (A.j : ZMod n)) : LetA O n) a, h2]
    | zero =>
      exact ⟨by rw [smul_zero]; exact (W.NΔ T).zero_mem, by rw [smul_zero, smul_zero]⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      rw [smul_add, smul_add, h₁.2, h₂.2]
      exact ⟨(W.NΔ T).add_mem h₁.1 h₂.1, rfl⟩
    | neg y _ h =>
      rw [smul_neg, smul_neg, h.2]
      exact ⟨(W.NΔ T).neg_mem h.1, rfl⟩
  intro y hy
  obtain ⟨hN, hl⟩ := key y hy
  refine ⟨⟨P • (P • y), smul_mem_NΔ W T hPA hN, ?_, ?_⟩, ⟨P • y, hN, hl, (one_smul (LetA O n) _).symm⟩⟩
  · rw [smul_comm (letE (c + (A.j : ZMod n)) : LetA O n) P, hl]
  · rw [show Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p) = W.π₀ ^ A.M PD.p * (P * P) from ?_,
      mul_smul, mul_smul]
    unfold Formalism.MainNotions.LiftingTheory.JJ
    congr 1
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add, ← two_mul]
    rfl

end Formalism.MainNotions.UnusedSlot80.PhiPowers
