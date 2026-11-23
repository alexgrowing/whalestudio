import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.Mean4O.Deg

section Gen

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem potential_chart_contDiffAt_two (A : FinHolAtlas e X) {P : LocPot X} (hP : IsPotential A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : ContDiffAt ℝ 2 (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
  (contDiffAt_of_isPotential A P hP _ j ⟨hy, P.mem_U _⟩).of_le (by norm_cast)

theorem leviAt_add (A : FinHolAtlas e X) {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) :
    leviAt A (P + Q) j y w = leviAt A P j y w + leviAt A Q j y w := by
  have h := levi_add_smul 1 (potential_chart_contDiffAt_two A hP j hy) (potential_chart_contDiffAt_two A hQ j hy) w
  simp only [one_mul] at h
  exact h

theorem leviAt_rsmul (A : FinHolAtlas e X) (P : LocPot X) (c : ℝ) (j : Fin A.n) (y w : Fin e → ℂ) :
    leviAt A (P.rsmul c) j y w = c * leviAt A P j y w := by
  unfold leviAt
  have he : (P.rsmul c).φ ((A.chart j).symm y) ∘ (A.chart j).symm =
    c • (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) := rfl
  rw [he]
  simp only [levi, fderiv_const_smul_field, Pi.smul_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem leviAt_const (A : FinHolAtlas e X) (c : ℝ) (j : Fin A.n) (y w : Fin e → ℂ) :
    leviAt A (LocPot.ofFun fun _ => c) j y w = 0 := by
  unfold leviAt
  have he : (LocPot.ofFun (X := X) fun _ => c).φ ((A.chart j).symm y) ∘ (A.chart j).symm = fun _ => c := rfl
  rw [he]
  simp [levi]

theorem smooth_const (A : FinHolAtlas e X) (c : ℝ) : A.Smooth fun _ => c := fun _ => contDiffOn_const

theorem psh_pullback {e' : ℕ} {Y : Type} [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (h : Y → X)
    (hh : HoloMap B A h) {P : LocPot X} (hP : IsPotential A P) (hp : IsPsh A P) : IsPsh B (P.pullback h hh.1) := by
  intro y j t ht w
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm t))
  have hO : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hh.1)
  have htO : t ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) := ⟨ht.1, hk⟩
  have han := hh.2 j k t htO
  have hin : (A.chart k ∘ h ∘ (B.chart j).symm) t ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U (h y) := by
    refine ⟨(A.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (A.chart k).left_inv hk]
    exact ht.2
  have h1 : ContDiffAt ℝ 2 (P.φ (h y) ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) t) :=
    (contDiffAt_of_isPotential A P hP (h y) k hin).of_le (by norm_cast)
  have heq : (P.pullback h hh.1).φ y ∘ (B.chart j).symm =ᶠ[𝓝 t]
      (P.φ (h y) ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (B.chart j).symm) := by
    filter_upwards [hO.mem_nhds htO] with t' ht'
    show P.φ (h y) (h ((B.chart j).symm t')) =
      P.φ (h y) ((A.chart k).symm ((A.chart k) (h ((B.chart j).symm t'))))
    rw [(A.chart k).left_inv ht'.2]
  rw [levi_congr heq, levi_comp w han h1]
  exact hp _ k _ hin _

theorem mInt_update {n : ℕ} (A : FinHolAtlas (n + 1) X) (Φ : Fin (n + 1) → LocPot X) (i : Fin (n + 1)) (P : LocPot X)
    (g : X → ℝ) :
    mInt A (Function.update Φ i P) g = mInt A (Fin.cons P fun k => Φ (Equiv.swap 0 i k.succ)) g := by
  rw [← mIntSymm A (Function.update Φ i P) (Equiv.swap 0 i) g]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · have : Equiv.swap 0 i k.succ ≠ i := by
      intro h
      have h2 : Equiv.swap 0 i k.succ = Equiv.swap 0 i 0 := by rw [h]; simp
      exact Fin.succ_ne_zero k ((Equiv.swap 0 i).injective h2)
    simp [Function.update_of_ne this]

theorem pot_cons {n : ℕ} (A : FinHolAtlas e X) {P : LocPot X} {Φ : Fin n → LocPot X} (hP : IsPotential A P)
    (hΦ : ∀ i, IsPotential A (Φ i)) (i : Fin (n + 1)) : IsPotential A ((Fin.cons P Φ : Fin (n + 1) → LocPot X) i) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simpa using hP
  · simpa using hΦ k

theorem pot_update (A : FinHolAtlas e X) {P : LocPot X} {Φ : Fin e → LocPot X} (hP : IsPotential A P)
    (hΦ : ∀ i, IsPotential A (Φ i)) (i k : Fin e) : IsPotential A (Function.update Φ i P k) := by
  by_cases h : k = i
  · subst h; simpa using hP
  · simpa [Function.update_of_ne h] using hΦ k

variable [CompactSpace X] [T2Space X]

theorem eff_nonneg {n : ℕ} (A : FinHolAtlas (n + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X) (hL : IsPotential A L) (hs : IsSection A L s) (hW : IsSNC A L s m W)
    (Φ : Fin n → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hp : ∀ i, IsPsh A (Φ i)) :
    0 ≤ mInt A (Fin.cons L Φ) fun _ => 1 := by
  choose B hB using sncInducedAtlas A L s m W hL hs hW
  have h := poincareLelong A L s m W B hL hs hW hB (fun _ => 1) (smooth_const A 1) Φ hΦ
  have h1 := isPotential_ofFun A _ (smooth_const A 1)
  have h0 : mInt A (Fin.cons (LocPot.ofFun fun _ => 1) Φ) (logNormSec L s) = 0 := by
    have := (GlobalTheory.LeviOnly.mInt_eq_of_leviEq _ X A (Fin.cons (LocPot.ofFun fun _ => 1) Φ)
      (Fin.cons ((LocPot.ofFun fun _ => 1).rsmul 0) Φ) (logNormSec L s) (pot_cons A h1 hΦ)
      (pot_cons A (isPotentialRsmul A 0 _ h1) hΦ) ?_).1
    · rw [this, mIntRsmul A 0 _ Φ h1 hΦ, zero_mul]
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · intro j y _ w
        simp only [Fin.cons_zero]
        rw [leviAt_rsmul, leviAt_const, mul_zero]
      · intro j y _ w
        simp only [Fin.cons_succ]
  rw [h0] at h
  have h2 : 0 ≤ ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
      ((fun _ => (1 : ℝ)) ∘ Subtype.val) := by
    refine Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) ?_
    exact mIntNonneg (B k) _ (fun i => isPotentialPullback A (B k) _ (hB k) _ (hΦ i))
      (fun i => psh_pullback A (B k) _ (hB k) (hΦ i) (hp i)) _ fun _ => zero_le_one
  linarith

variable {V : Type} [AddCommGroup V] [Module ℝ V]

theorem exists_form (A : FinHolAtlas e X) (c : V → LocPot X) (hc : ∀ v, IsPotential A (c v))
    (hadd : ∀ v w, LeviEq A (c (v + w)) (c v + c w)) (hsmul : ∀ (a : ℝ) v, LeviEq A (c (a • v)) ((c v).rsmul a)) :
    ∃ I : MultilinearMap ℝ (fun _ : Fin e => V) ℝ, ∀ x, I x = mInt A (fun i => c (x i)) fun _ => 1 := by
  have key : ∀ (x : Fin e → V) (i : Fin e) (v : V) (P : LocPot X), IsPotential A P → LeviEq A (c v) P →
      mInt A (fun k => c (Function.update x i v k)) (fun _ => 1) =
        mInt A (Function.update (fun k => c (x k)) i P) fun _ => 1 := by
    intro x i v P hP hl
    refine (GlobalTheory.LeviOnly.mInt_eq_of_leviEq _ X A _ _ _ (fun k => hc _) (pot_update A hP (fun k => hc _) i) fun k => ?_).1
    by_cases h : k = i
    · subst h; simpa using hl
    · simp only [Function.update_of_ne h]
      intro _ _ _ _; rfl
  refine ⟨MultilinearMap.mk' (fun x => mInt A (fun i => c (x i)) fun _ => 1) ?_ ?_, fun _ => rfl⟩
  · intro x i v w
    rw [key x i _ _ (isPotentialAdd A _ _ (hc v) (hc w)) (hadd v w), key x i v _ (hc v) (fun _ _ _ _ => rfl),
      key x i w _ (hc w) (fun _ _ _ _ => rfl)]
    cases e with
    | zero => exact i.elim0
    | succ n =>
      simp only [mInt_update]
      exact mIntAdd A _ _ _ (hc v) (hc w) (fun _ => hc _) _
        (mIntegrableCont A _ (pot_cons A (hc v) fun _ => hc _) _ continuous_const)
        (mIntegrableCont A _ (pot_cons A (hc w) fun _ => hc _) _ continuous_const)
  · intro x i a v
    rw [key x i _ _ (isPotentialRsmul A a _ (hc v)) (hsmul a v), key x i v _ (hc v) (fun _ _ _ _ => rfl)]
    cases e with
    | zero => exact i.elim0
    | succ n =>
      simp only [mInt_update]
      exact mIntRsmul A a _ _ (hc v) (fun _ => hc _) _

def Rep (A : FinHolAtlas e X) (Q P : LocPot X) : Prop :=
  IsPotential A P ∧ ∃ g, A.Smooth g ∧ LeviEq A P (Q + LocPot.ofFun g)

theorem mInt_rep (A : FinHolAtlas e X) {Q P : Fin e → LocPot X} (hQ : ∀ i, IsPotential A (Q i))
    (h : ∀ i, Rep A (Q i) (P i)) : mInt A Q (fun _ => 1) = mInt A P fun _ => 1 := by
  choose hP g hg hl using h
  rw [← massIndep A Q g hQ hg]
  exact (GlobalTheory.LeviOnly.mInt_eq_of_leviEq _ X A _ _ _ hP
    (fun i => isPotentialAdd A _ _ (hQ i) (isPotential_ofFun A _ (hg i))) hl).1.symm

end Gen

theorem tele {e : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V] (I : MultilinearMap ℝ (fun _ : Fin e => V) ℝ)
    (N : Set V) (b M : V) (s : ℝ) (hs : 0 ≤ s) (hM : M ∈ N) (hL : M + s • b ∈ N)
    (hb : ∀ (x : Fin e → V) i, (∀ k, x k ∈ N) → 0 ≤ I (Function.update x i b)) :
    I (fun _ => M) ≤ I fun _ => M + s • b := by
  have key : ∀ S : Finset (Fin e), I (fun _ => M) ≤ I (S.piecewise (fun _ => M + s • b) fun _ => M) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      rw [Finset.piecewise_insert, I.map_update_add, I.map_update_smul]
      have h1 : Function.update (S.piecewise (fun _ => M + s • b) fun _ => M) i M =
          S.piecewise (fun _ => M + s • b) fun _ => M := by
        rw [Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hi]
      have h2 := hb (S.piecewise (fun _ => M + s • b) fun _ => M) i fun k => by
        by_cases hk : k ∈ S
        · rw [Finset.piecewise_eq_of_mem _ _ _ hk]; exact hL
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hk]; exact hM
      rw [h1, smul_eq_mul]
      have := mul_nonneg hs h2
      linarith
  simpa using key Finset.univ

theorem cont_line {e : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V] (I : MultilinearMap ℝ (fun _ : Fin e => V) ℝ)
    (x y : Fin e → V) : Continuous fun t : ℝ => I fun i => x i + t • y i := by
  have h : (fun t : ℝ => I fun i => x i + t • y i) =
      fun t : ℝ => ∑ S : Finset (Fin e), (∏ i, if i ∈ S then 1 else t) * I (S.piecewise x y) := by
    funext t
    have h1 := I.map_add_univ x (t • y)
    refine Eq.trans h1 (Finset.sum_congr rfl fun S _ => ?_)
    rw [← smul_eq_mul, ← I.map_smul_univ]
    congr 1
    funext i
    by_cases hi : i ∈ S <;> simp [Finset.piecewise, hi]
  rw [h]
  refine continuous_finset_sum _ fun S _ => Continuous.mul ?_ continuous_const
  refine continuous_finset_prod _ fun i _ => ?_
  by_cases hi : i ∈ S
  · exact (continuous_const (y := (1 : ℝ))).congr fun t => by simp [hi]
  · exact continuous_id.congr fun t => by simp [hi]

theorem nonneg_of_line {e : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V] (I : MultilinearMap ℝ (fun _ : Fin e => V) ℝ)
    (x y : Fin e → V) (h : ∀ t : ℝ, 0 < t → 0 ≤ I fun i => x i + t • y i) : 0 ≤ I x := by
  have h1 : Tendsto (fun t : ℝ => I fun i => x i + t • y i) (𝓝[>] 0) (𝓝 (I x)) := by
    have := ((cont_line I x y).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  exact ge_of_tendsto h1 (eventually_nhdsWithin_of_forall h)

theorem one {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    {W : Type} [AddCommGroup W] [Module ℝ W] (th : W → LocPot X) (a Om : LocPot X) (hth : ∀ u, IsPotential A (th u))
    (ha : IsPotential A a) (hOm : IsPotential A Om) (hadd : ∀ v w, LeviEq A (th (v + w)) (th v + th w))
    (hsmul : ∀ (t : ℝ) v, LeviEq A (th (t • v)) ((th v).rsmul t)) (Dm : W → Prop)
    (hnef : ∀ u, Dm u → ∀ ε : ℝ, 0 < ε → ∃ g, A.Smooth g ∧ IsPsh A (th u + Om.rsmul ε + LocPot.ofFun g))
    (hap : IsPsh A a) (d : W) (k : ℝ) (g : X → ℝ) (L : LocPot X) (sc : X → X → ℂ) (n : ℕ) (m : Fin n → ℕ)
    (Z : Fin n → Set X) (hk : 0 < k) (hg : A.Smooth g) (hL : IsPotential A L) (hs : IsSection A L sc)
    (hZ : IsSNC A L sc m Z) (hl : LeviEq A L ((th d + a.rsmul (-1)).rsmul k + LocPot.ofFun g)) (u : W) :
    (∀ s : ℝ, 0 ≤ s → Dm u → Dm (u - s • d) →
      0 ≤ mInt A (fun _ => th (u - s • d) + a.rsmul s + LocPot.ofFun fun _ => 0) (fun _ => 1) ∧
      mInt A (fun _ => th (u - s • d) + a.rsmul s + LocPot.ofFun fun _ => 0) (fun _ => 1) ≤
        mInt A (fun _ => th u) fun _ => 1) ∧
    Tendsto (fun s : ℝ => mInt A (fun _ => th (u - s • d) + a.rsmul s + LocPot.ofFun fun _ => 0) fun _ => 1) (𝓝 0)
      (𝓝 (mInt A (fun _ => th u) fun _ => 1)) := by
  have pA := fun P Q => isPotentialAdd A P Q
  have pS := fun t P => isPotentialRsmul A t P
  have pF := isPotential_ofFun A
  set c : W × ℝ × ℝ → LocPot X := fun v => th v.1 + a.rsmul v.2.1 + Om.rsmul v.2.2 with hcdef
  have hc : ∀ v, IsPotential A (c v) := fun v => pA _ _ (pA _ _ (hth _) (pS _ _ ha)) (pS _ _ hOm)
  have lc : ∀ v j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A (c v) j y w =
      leviAt A (th v.1) j y w + v.2.1 * leviAt A a j y w + v.2.2 * leviAt A Om j y w := by
    intro v j y hy w
    simp only [hcdef]
    rw [leviAt_add A (pA _ _ (hth _) (pS _ _ ha)) (pS _ _ hOm) j hy, leviAt_add A (hth _) (pS _ _ ha) j hy,
      leviAt_rsmul, leviAt_rsmul]
  obtain ⟨I, hI⟩ := exists_form A c hc
    (fun v w j y hy z => by
      rw [leviAt_add A (hc _) (hc _) j hy, lc _ j y hy, lc _ j y hy, lc _ j y hy, Prod.fst_add, hadd _ _ j y hy,
        leviAt_add A (hth _) (hth _) j hy]
      simp only [Prod.fst_add, Prod.snd_add]
      ring)
    (fun t v j y hy z => by
      rw [leviAt_rsmul, lc _ j y hy, lc _ j y hy, Prod.smul_fst, hsmul _ _ j y hy, leviAt_rsmul]
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring)
  have hrep : ∀ (x : Fin e → W × ℝ × ℝ) (P : Fin e → LocPot X), (∀ i, Rep A (c (x i)) (P i)) →
      I x = mInt A P fun _ => 1 := fun x P h => by rw [hI, mInt_rep A (fun i => hc _) h]
  let o : W × ℝ × ℝ := (0, 0, 1)
  let N : Set (W × ℝ × ℝ) := {v | ∀ ε : ℝ, 0 < ε → ∃ P, Rep A (c (v + ε • o)) P ∧ IsPsh A P}
  have hN : ∀ (v : W) (s : ℝ), 0 ≤ s → Dm v → (v, s, 0) ∈ N := by
    intro v s hs0 hv ε hε
    obtain ⟨f, hf, hp⟩ := hnef v hv ε hε
    have p1 := pA _ _ (pA _ _ (hth v) (pS ε _ hOm)) (pF _ hf)
    refine ⟨_, ⟨pA _ _ p1 (pS s _ ha), f, hf, fun j y hy z => ?_⟩,
      isPshAdd A _ _ p1 (pS s _ ha) hp (isPshRsmul A s _ hs0 ha hap)⟩
    rw [leviAt_add A p1 (pS s _ ha) j hy, leviAt_add A (pA _ _ (hth v) (pS ε _ hOm)) (pF _ hf) j hy,
      leviAt_add A (hth v) (pS ε _ hOm) j hy, leviAt_add A (hc _) (pF _ hf) j hy, lc _ j y hy, leviAt_rsmul, leviAt_rsmul]
    simp only [o, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, smul_eq_mul, mul_one, zero_add, mul_zero]
    ring
  have hpos : ∀ x : Fin e → W × ℝ × ℝ, (∀ i, x i ∈ N) → 0 ≤ I x := by
    intro x hx
    refine nonneg_of_line I x (fun _ => o) fun t ht => ?_
    choose P hP hp using fun i => hx i t ht
    rw [hrep _ P hP]
    exact mIntNonneg A P (fun i => (hP i).1) hp _ fun _ => zero_le_one
  let b : W × ℝ × ℝ := (d, -1, 0)
  have hb : Rep A (c (k • b)) L := by
    refine ⟨hL, g, hg, fun j y hy z => ?_⟩
    rw [hl j y hy, leviAt_add A (pS _ _ (pA _ _ (hth _) (pS _ _ ha))) (pF _ hg) j hy, leviAt_rsmul,
      leviAt_add A (hth _) (pS _ _ ha) j hy, leviAt_rsmul, leviAt_add A (hc _) (pF _ hg) j hy, lc _ j y hy]
    simp only [b, Prod.smul_mk, smul_eq_mul, mul_zero]
    rw [hsmul _ _ j y hy, leviAt_rsmul]
    ring
  have heff : ∀ (x : Fin e → W × ℝ × ℝ) i, (∀ l, x l ∈ N) → 0 ≤ I (Function.update x i b) := by
    intro x i hx
    have h1 : 0 ≤ I (Function.update x i (k • b)) := by
      refine nonneg_of_line I _ (Function.update (fun _ => o) i 0) fun t ht => ?_
      choose P hP hp using fun i => hx i t ht
      rw [hrep _ (Function.update P i L) fun l => ?_]
      · cases e with
        | zero => exact i.elim0
        | succ e =>
          rw [mInt_update]
          exact eff_nonneg A L sc m Z hL hs hZ _ (fun _ => (hP _).1) fun _ => hp _
      · by_cases h : l = i
        · subst h; simpa using hb
        · simpa [Function.update_of_ne h] using hP l
    rw [I.map_update_smul, smul_eq_mul] at h1
    exact nonneg_of_mul_nonneg_right (by linarith [mul_comm k (I (Function.update x i b))]) hk
  have e1 : ∀ s : ℝ, mInt A (fun _ => th (u - s • d) + a.rsmul s + LocPot.ofFun fun _ => 0) (fun _ => 1) =
      I fun _ => (u - s • d, s, 0) := by
    intro s
    have p1 := pA _ _ (hth (u - s • d)) (pS s _ ha)
    have p0 := pF _ (smooth_const A 0)
    refine (hrep _ _ fun _ => ⟨pA _ _ p1 p0, _, smooth_const A 0, fun j y hy z => ?_⟩).symm
    rw [leviAt_add A p1 p0 j hy, leviAt_add A (hc _) p0 j hy, lc _ j y hy, leviAt_add A (hth _) (pS s _ ha) j hy,
      leviAt_rsmul]
    ring
  have e2 : mInt A (fun _ => th u) (fun _ => 1) = I fun _ => (u, 0, 0) := by
    refine (hrep _ _ fun _ => ⟨hth u, _, smooth_const A 0, fun j y hy z => ?_⟩).symm
    rw [leviAt_add A (hc _) (pF _ (smooth_const A 0)) j hy, lc _ j y hy, leviAt_const]
    ring
  simp only [e1, e2]
  refine ⟨fun s hs0 hu hu' => ⟨hpos _ fun _ => hN _ _ hs0 hu', ?_⟩, ?_⟩
  · have e3 : ((u - s • d, s, 0) : W × ℝ × ℝ) + s • b = (u, 0, 0) := by simp [b]
    have := tele I N b (u - s • d, s, 0) s hs0 (hN _ _ hs0 hu') (by rw [e3]; exact hN _ _ le_rfl hu) heff
    rwa [e3] at this
  · have := (cont_line I (fun _ => (u, 0, 0)) fun _ => -b).tendsto 0
    simpa [b, sub_eq_add_neg] using this

theorem degrees (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y) (A : SlopeTestRemainingChoices Y) (_hS : ∀ c, (T.F c).FamS)
    (hN : ∀ c, (T.F c).NefAn) (hQ : ∀ c, (T.F c).QPol A.dir) (hP : ∀ c, (T.F c).Prop4 (A.w c))
    (hv : Y.vol = ∑ c, A.w c) (hM : TieM T A) : Degrees A := by
  have hsh : ∀ (u : Wt Y) (s : ℝ), A.sh u s = u - s • A.dir := fun u s => by
    funext τ i; simp [SlopeTestRemainingChoices.sh]
  have key : ∀ c σ (u : Wt Y),
      (∀ s : ℝ, 0 ≤ s → Dom u → Dom (A.sh u s) →
        0 ≤ mInt ((T.M c).A σ) (fun _ => (T.F c).form (A.sh u s) s 0 σ) (fun _ => 1) ∧
        mInt ((T.M c).A σ) (fun _ => (T.F c).form (A.sh u s) s 0 σ) (fun _ => 1) ≤
          mInt ((T.M c).A σ) (fun _ => (T.F c).th u σ) fun _ => 1) ∧
      Tendsto (fun s : ℝ => mInt ((T.M c).A σ) (fun _ => (T.F c).form (A.sh u s) s 0 σ) fun _ => 1) (𝓝 0)
        (𝓝 (mInt ((T.M c).A σ) (fun _ => (T.F c).th u σ) fun _ => 1)) := by
    intro c σ u
    obtain ⟨hap, k, g, L, sc, n, m, Z, hk, hg, hL, hs, hZ, hl⟩ := hQ c σ
    simp only [hsh]
    refine one ((T.M c).A σ) (fun u => (T.F c).th u σ) ((T.F c).a σ) ((T.M c).Om σ) (fun u => T.th_pot c u σ)
      (T.a_pot c σ) ((T.M c).bd σ).2.2.1 ?_ ?_ Dom (fun u hu ε hε => hN c u hu ε hε σ) hap A.dir k g L sc n m Z
      hk hg hL hs hZ hl u
    · intro v w j y hy z
      rw [← T.c1_L 2 c _ σ j y hy, map_add, (T.K 2 c).isOneCochain_add _ _ σ j y hy,
        leviAt_add _ ((T.K 2 c).firstChern_isPotential _ σ) ((T.K 2 c).firstChern_isPotential _ σ) j hy,
        leviAt_add _ (T.th_pot c _ σ) (T.th_pot c _ σ) j hy, T.c1_L 2 c _ σ j y hy, T.c1_L 2 c _ σ j y hy]
    · intro t v j y hy z
      rw [← T.c1_L 2 c _ σ j y hy, map_smul, (T.K 2 c).firstChern_smul_leviEq _ _ σ j y hy, leviAt_rsmul, leviAt_rsmul,
        T.c1_L 2 c _ σ j y hy]
  refine ⟨fun c => (hP c).1, hv, fun Λ => ⟨1, one_pos, fun B hB u s hr _ hs _ hu hu' c => ?_⟩, fun B hB u hr c => ?_⟩
  · have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
    rw [(hM B hB u s hr hs).1 c, ← (hP c).2 u]
    unfold Man.int
    exact ⟨mul_nonneg (T.M c).κ_pos.le (Finset.sum_nonneg fun σ _ => ((key c σ u).1 s hs' hu hu').1),
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ((key c σ u).1 s hs' hu hu').2) (T.M c).κ_pos.le⟩
  · rw [← (hP c).2 u]
    have hc : Tendsto (fun s : ℚ => (s : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have := (Rat.continuous_coe_real.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have h := ((tendsto_finset_sum Finset.univ fun σ _ => (key c σ u).2).const_mul (T.M c).κ).comp hc
    refine h.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    exact ((hM B hB u s hr hs).1 c).symm

end GlobalTheory.Mean4O.Deg
