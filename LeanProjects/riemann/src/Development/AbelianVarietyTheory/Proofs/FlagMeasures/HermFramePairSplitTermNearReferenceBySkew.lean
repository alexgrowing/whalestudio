import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairIdealKillsDiscriminantModulesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.DegCnt.DualPos

section Generic
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

def Bd {E : Type} [AddCommGroup E] [Module R E] (I : Ideal R) (M : Submodule R E) : Submodule R E where
  carrier := {v | ∀ a ∈ I, a • v ∈ M}
  add_mem' := fun {x y} hx hy a ha => by rw [smul_add]; exact M.add_mem (hx a ha) (hy a ha)
  zero_mem' := fun a _ => by simp
  smul_mem' := fun b x hx a ha => by rw [smul_comm]; exact M.smul_mem b (hx a ha)

theorem bd_add {E : Type} [AddCommGroup E] [Module R E] {c : Ideal R} {M : Submodule R E} {v : E} {n m : ℕ}
    (h : v ∈ Bd (c ^ n) (Bd (c ^ m) M)) : v ∈ Bd (c ^ (n + m)) M := by
  intro a ha
  rw [pow_add] at ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro x hx y hy
    rw [mul_comm, mul_smul]
    exact h x hx y hy
  · intro x y hx hy
    rw [add_smul]; exact M.add_mem hx hy

theorem bd_mono {E : Type} [AddCommGroup E] [Module R E] {c : Ideal R} {M : Submodule R E} {v : E} {n m : ℕ}
    (h : v ∈ Bd (c ^ n) M) (hnm : n ≤ m) : v ∈ Bd (c ^ m) M :=
  fun a ha => h a (Ideal.pow_le_pow_right hnm ha)

theorem bd_self {E : Type} [AddCommGroup E] [Module R E] {c : Ideal R} {M : Submodule R E} {v : E}
    (h : v ∈ M) : v ∈ Bd c M := fun a _ => M.smul_mem a h

theorem smul_le_iff {E : Type} [AddCommGroup E] [Module R E] {c : Ideal R} {M M' : Submodule R E} :
    c • M ≤ M' ↔ ∀ v ∈ M, v ∈ Bd c M' := by
  rw [Submodule.smul_le]
  exact ⟨fun h v hv a ha => h a ha v hv, fun h a ha v hv => h v hv a ha⟩

def StarSt (K : Type) [Field K] [StarRing K] [Algebra R K] (I : Ideal R) : Prop :=
  ∀ x ∈ I, ∃ y ∈ I, algebraMap R K y = star (algebraMap R K x)

theorem starSt_pow {c : Ideal R} (h1 : StarSt K (⊤ : Ideal R)) (hc : StarSt K c) (n : ℕ) : StarSt K (c ^ n) := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    intro a ha
    rw [pow_succ] at ha ⊢
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      obtain ⟨x', hx', ex⟩ := ih x hx
      obtain ⟨y', hy', ey⟩ := hc y hy
      exact ⟨x' * y', Ideal.mul_mem_mul hx' hy', by simp [ex, ey]⟩
    · rintro x y ⟨x', hx', ex⟩ ⟨y', hy', ey⟩
      exact ⟨x' + y', Ideal.add_mem _ hx' hy', by simp [ex, ey]⟩

theorem star_one_mem (h1 : StarSt K (⊤ : Ideal R)) {x : K} (hx : x ∈ (1 : Submodule R K)) :
    star x ∈ (1 : Submodule R K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hx
  obtain ⟨b, -, hb⟩ := h1 a trivial
  exact Submodule.mem_one.2 ⟨b, hb⟩

theorem star_bd {c : Ideal R} (h1 : StarSt K (⊤ : Ideal R)) (hc : StarSt K c) {n : ℕ} {x : K}
    (hx : x ∈ Bd (c ^ n) (1 : Submodule R K)) : star x ∈ Bd (c ^ n) (1 : Submodule R K) := by
  intro a ha
  obtain ⟨b, hb, e⟩ := starSt_pow h1 hc n a ha
  have := star_one_mem h1 (hx b hb)
  rw [Algebra.smul_def, e, star_mul', star_star] at this
  rwa [Algebra.smul_def]

theorem B_smul (H : HermSpace K V) (a : R) (v w : V) : H.B (a • v) w = a • H.B v w := by
  rw [← algebraMap_smul K a v, map_smul, LinearMap.smul_apply, algebraMap_smul]

theorem pair_left (H : HermSpace K V) {c : Ideal R} {M : Submodule R V} {n k : ℕ} {v w : V}
    (hv : v ∈ Bd (c ^ n) M) (h : ∀ x ∈ M, H.B x w ∈ Bd (c ^ k) (1 : Submodule R K)) :
    H.B v w ∈ Bd (c ^ (n + k)) (1 : Submodule R K) := by
  refine bd_add fun a ha => ?_
  rw [← B_smul]
  exact h _ (hv a ha)

theorem pair_both (H : HermSpace K V) {c : Ideal R} (h1 : StarSt K (⊤ : Ideal R)) (hc : StarSt K c)
    {M : Submodule R V} {n m k : ℕ} {v w : V}
    (hv : v ∈ Bd (c ^ n) M) (hw : w ∈ Bd (c ^ m) M)
    (h : ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ Bd (c ^ k) (1 : Submodule R K)) :
    H.B v w ∈ Bd (c ^ (n + (m + k))) (1 : Submodule R K) := by
  refine pair_left H hv fun x hx => ?_
  rw [← H.herm]
  exact star_bd h1 hc (pair_left H hw fun y hy => h y hy x hx)

theorem of_dual (H : HermSpace K V) {c : Ideal R} {M : Submodule R V} (hk : c • dual H M ≤ M) {n : ℕ} {v : V}
    (hv : v ∈ Submodule.span K (M : Set V)) (h : ∀ x ∈ M, H.B v x ∈ Bd (c ^ n) (1 : Submodule R K)) :
    v ∈ Bd (c ^ (n + 1)) M := by
  refine bd_add fun a ha => ?_
  rw [pow_one]
  refine smul_le_iff.1 hk _ ((mem_dual_iff H M _).2 ⟨?_, fun x hx => ?_⟩)
  · rw [← algebraMap_smul K a v]; exact Submodule.smul_mem _ _ hv
  · rw [B_smul]; exact h x hx a ha

def pr (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) : V →ₗ[K] V :=
  ∑ b, (H.B.flip (e b)).smulRight (f b)

omit [Module R V] [IsScalarTower R K V] in
theorem pr_apply (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) (v : V) :
    pr H e f v = ∑ b, H.B v (e b) • f b := by
  simp [pr, LinearMap.sum_apply]

theorem pr_adj (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) (x v : V) :
    H.B (pr H f e x) v = H.B x (pr H e f v) := by
  simp only [pr_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← H.herm v (e b), mul_comm]; rfl

theorem pr_comp (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) (Φ : V →ₗ[K] V) (v : V) :
    pr H e (Φ ∘ f) v = Φ (pr H e f v) := by
  simp [pr_apply]

theorem pr_mem (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) (v : V) :
    pr H e f v ∈ Submodule.span K (Set.range f) := by
  rw [pr_apply]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem pr_zero (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V) {v : V} (hv : ∀ b, H.B v (e b) = 0) :
    pr H e f v = 0 := by
  simp [pr_apply, hv]

theorem span_perp (H : HermSpace K V) {J : Type} {e : J → V} {w : V} (hw : ∀ b, H.B (e b) w = 0) {v : V}
    (hv : v ∈ Submodule.span K (Set.range e)) : H.B v w = 0 := by
  have : Submodule.span K (Set.range e) ≤ LinearMap.ker (H.B.flip w) := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact hw b
  exact this hv

theorem pr_fix (H : HermSpace K V) {J : Type} [Fintype J] [DecidableEq J] {e f : J → V}
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) {v : V}
    (hv : v ∈ Submodule.span K (Set.range f)) : pr H e f v = v := by
  have : Submodule.span K (Set.range f) ≤ LinearMap.eqLocus (pr H e f) LinearMap.id := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩
    show pr H e f (f b) = f b
    rw [pr_apply, Finset.sum_eq_single b]
    · rw [← H.herm, hef]; simp
    · intro a _ hab; rw [← H.herm, hef]; simp [hab]
    · simp
  exact this hv

theorem exists_skew (H : HermSpace K V) {J : Type} [Fintype J] (e f : J → V)
    (hee : ∀ a b, H.B (e a) (e b) = 0) (Φ : V →ₗ[K] V) (t : K) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ (∀ v, v - s v ∈ Submodule.span K (Set.range e)) ∧
      (∀ v, pr H e f v = 0 → s v = v) ∧
      ∀ v w, H.B (v - s v) w =
        star t * H.B (Φ (pr H e f v)) (pr H e f w) - t * H.B (pr H e f v) (Φ (pr H e f w)) := by
  set p := pr H e f with hp
  let N : V →ₗ[K] V := (star t • (pr H f e ∘ₗ Φ) - t • pr H (Φ ∘ f) e) ∘ₗ p
  have hN : ∀ v, N v = star t • pr H f e (Φ (p v)) - t • pr H (Φ ∘ f) e (p v) := fun v => rfl
  have hmem : ∀ v, N v ∈ Submodule.span K (Set.range e) := fun v => by
    rw [hN]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (pr_mem H _ _ _)) (Submodule.smul_mem _ _ (pr_mem H _ _ _))
  have h0 : ∀ v, p v = 0 → N v = 0 := fun v hv => by rw [hN, hv]; simp
  have hpN : ∀ v, p (N v) = 0 := fun v => pr_zero H e f fun b => span_perp H (fun a => hee a b) (hmem v)
  have hB : ∀ v w, H.B (N v) w = star t * H.B (Φ (p v)) (p w) - t * H.B (p v) (Φ (p w)) := fun v w => by
    rw [hN, map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      pr_adj, pr_adj, pr_comp]
    rfl
  refine ⟨LinearEquiv.ofLinear (LinearMap.id - N) (LinearMap.id + N) ?_ ?_, ?_, ?_, ?_, ?_⟩
  · ext v; simp [h0 _ (hpN v)]
  · ext v; simp [h0 _ (hpN v)]
  · intro x y
    have e1 : H.B (N x) (N y) = 0 := by rw [hB, hpN]; simp
    have e2 : H.B x (N y) = - H.B (N x) y := by
      rw [← H.herm, hB, hB]; simp [H.herm]
    simp [e1, e2]
  · intro v; simpa using hmem v
  · intro v hv; simp [h0 v hv]
  · intro v w; simpa using hB v w

theorem core (H : HermSpace K V) {J : Type} [Fintype J] [DecidableEq J] (e f : J → V)
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) (hee : ∀ a b, H.B (e a) (e b) = 0)
    (hff : ∀ a b, H.B (f a) (f b) = 0) (P A M Λ : Submodule R V) (Pi : Submodule K V)
    (hPi : Submodule.span K (P : Set V) = Pi) (c : Ideal R) (h1 : StarSt K (⊤ : Ideal R)) (hc : StarSt K c)
    (n : ℕ) (t : R) (ht : algebraMap R K t + star (algebraMap R K t) = 1)
    (hA : A ≤ P) (hM : M ≤ P) (hdec : ∀ x ∈ P, ∃ a ∈ A, ∃ m ∈ M, x = a + m)
    (hAe : ∀ x ∈ A, ∀ b, H.B x (e b) = 0) (hMf : ∀ y ∈ M, y ∈ Submodule.span K (Set.range f))
    (heP : ∀ b, e b ∈ Pi) (hAΛ : ∀ x ∈ A, x ∈ Bd (c ^ n) Λ)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule R K))
    (hk1 : c • dual H P ≤ P) (hk2 : c • P ≤ dual H P) (Φ : V →ₗ[K] V)
    (hΦ1 : ∀ y ∈ M, Φ y ∈ Pi) (hΦ2 : ∀ y ∈ M, ∀ b, H.B (Φ y - y) (e b) = 0)
    (hΦ3 : ∀ y ∈ M, Φ y ∈ Bd (c ^ 4) Λ) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ (∀ v, v - s v ∈ Submodule.span K (Set.range e)) ∧
      (∀ v, (∀ b, H.B v (e b) = 0) → s v = v) ∧
      (∀ x ∈ P, x ∈ Bd (c ^ (3 * n + 12)) (s • Λ)) ∧
      ∀ x ∈ s • Λ, x ∈ Pi → x ∈ Bd (c ^ (3 * n + 13)) P := by
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := exists_skew H e f hee Φ (algebraMap R K t)
  set p := pr H e f with hp
  set q := pr H f e with hq
  have hsI : ∀ v, (∀ b, H.B v (e b) = 0) → s v = v := fun v hv => hs3 v (pr_zero H e f hv)
  have hPP : ∀ x ∈ P, ∀ y ∈ P, H.B x y ∈ Bd (c ^ 1) (1 : Submodule R K) := by
    intro x hx y hy a ha
    rw [pow_one] at ha
    rw [← B_smul]
    exact ((mem_dual_iff H P _).1 (smul_le_iff.1 hk2 x hx a ha)).2 y hy
  have hLL : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ Bd (c ^ 0) (1 : Submodule R K) := fun x hx y hy =>
    bd_self (hint x hx y hy)
  have hPPi : ∀ x ∈ P, x ∈ Pi := fun x hx => hPi ▸ Submodule.subset_span hx
  have hePi : Submodule.span K (Set.range e) ≤ Pi := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact heP b
  have hpM : ∀ y ∈ M, p y = y := fun y hy => pr_fix H hef (hMf y hy)
  have hpA : ∀ x ∈ A, p x = 0 := fun x hx => pr_zero H e f (hAe x hx)
  have hpw : ∀ y ∈ M, p (Φ y - y) = 0 := fun y hy => pr_zero H e f (hΦ2 y hy)
  have hpe : ∀ v ∈ Submodule.span K (Set.range e), p v = 0 := fun v hv =>
    pr_zero H e f fun b => span_perp H (fun a => hee a b) hv
  have hqB : ∀ v w, H.B (q v) w = H.B v (p w) := pr_adj H e f
  have hMM : ∀ y ∈ M, ∀ x ∈ M, H.B y x = 0 := fun y hy x hx =>
    span_perp H (fun b => by rw [← H.herm, span_perp H (fun a => hff a b) (hMf x hx), star_zero]) (hMf y hy)
  have hwA : ∀ y ∈ M, ∀ x ∈ A, H.B (Φ y - y) x ∈ Bd (c ^ (n + 4)) (1 : Submodule R K) := by
    intro y hy x hx
    rw [map_sub, LinearMap.sub_apply]
    exact Submodule.sub_mem _ (bd_mono (pair_both H h1 hc (hΦ3 y hy) (hAΛ x hx) hLL) (by omega))
      (bd_mono (hPP y (hM hy) x (hA hx)) (by omega))
  have hwPi : ∀ y ∈ M, Φ y - y ∈ Pi := fun y hy => Pi.sub_mem (hΦ1 y hy) (hPPi y (hM hy))
  have hu : ∀ y ∈ M, (Φ y - y) - q (Φ y - y) ∈ Bd (c ^ (n + 4 + 1)) P := by
    intro y hy
    refine of_dual H hk1 (hPi ▸ Pi.sub_mem (hwPi y hy) (hePi (pr_mem H _ _ _))) fun x hx => ?_
    obtain ⟨a, ha, m, hm, rfl⟩ := hdec x hx
    rw [map_sub, LinearMap.sub_apply, hqB, map_add p, hpA a ha, hpM m hm, zero_add, map_add, add_sub_cancel_right]
    exact hwA y hy a ha
  have hww : ∀ y ∈ M, ∀ x ∈ M, H.B (Φ y - y) (Φ x - x) ∈ Bd (c ^ (2 * n + 11)) (1 : Submodule R K) := by
    intro y hy x hx
    have h := pair_both H h1 hc (hu y hy) (hu x hx) hPP
    have e1 : H.B (q (Φ y - y)) (Φ x - x - q (Φ x - x)) = 0 := by
      rw [hqB, map_sub p, hpw x hx, hpe _ (pr_mem H _ _ _)]; simp
    have e2 : H.B (Φ y - y) (q (Φ x - x)) = 0 := by
      rw [← H.herm, hqB, hpw y hy]; simp
    rw [map_sub H.B, LinearMap.sub_apply, e1, sub_zero, map_sub (H.B _), e2, sub_zero] at h
    exact bd_mono h (by omega)
  have hz : ∀ y ∈ M, s (Φ y) - y ∈ Bd (c ^ (2 * n + 11 + 1)) P := by
    intro y hy
    have hpy : p (Φ y) = y := by
      have := hpw y hy
      rwa [map_sub, hpM y hy, sub_eq_zero] at this
    have hz0 : s (Φ y) - y = (Φ y - y) - (Φ y - s (Φ y)) := by abel
    rw [hz0]
    refine of_dual H hk1 (hPi ▸ Pi.sub_mem (hwPi y hy) (hePi (hs2 _))) fun x hx => ?_
    obtain ⟨a, ha, m, hm, rfl⟩ := hdec x hx
    rw [map_sub, LinearMap.sub_apply, hs4, map_add p, hpA a ha, hpM m hm, zero_add, map_add, hpy]
    have e1 : H.B (Φ y - y) a + H.B (Φ y - y) m -
        (star (algebraMap R K t) * H.B (Φ y) m - algebraMap R K t * H.B y (Φ m)) =
        H.B (Φ y - y) a + t • (H.B (Φ y) (Φ m) - H.B (Φ y - y) (Φ m - m)) := by
      have : star (algebraMap R K t) = 1 - algebraMap R K t := by rw [← ht]; ring
      rw [this, Algebra.smul_def]
      simp only [map_sub, LinearMap.sub_apply, hMM y hy m hm]
      ring
    rw [e1]
    exact Submodule.add_mem _ (bd_mono (hwA y hy a ha) (by omega)) (Submodule.smul_mem _ _
      (Submodule.sub_mem _ (bd_mono (pair_both H h1 hc (hΦ3 y hy) (hΦ3 m hm) hLL) (by omega)) (hww y hy m hm)))
  have hmem : ∀ x, x ∈ s • Λ ↔ ∃ l ∈ Λ, s l = x := fun x => Submodule.mem_smul_pointwise_iff_exists _ _ _
  have hsR : ∀ (a : R) v, s (a • v) = a • s v := fun a v => by
    rw [← algebraMap_smul K a v, map_smul, algebraMap_smul]
  have hAs : ∀ x ∈ A, x ∈ Bd (c ^ n) (s • Λ) := by
    intro x hx a ha
    exact (hmem _).2 ⟨_, hAΛ x hx a ha, hs3 _ (hpA _ (A.smul_mem a hx))⟩
  have hMs : ∀ y ∈ M, y ∈ Bd (c ^ (3 * n + 12)) (s • Λ) := by
    intro y hy
    have e1 : y = s (Φ y) - (s (Φ y) - y) := by abel
    rw [e1]
    refine Submodule.sub_mem _ (bd_mono (n := 4) ?_ (by omega)) (bd_mono (n := 2 * n + 11 + 1 + n) ?_ (by omega))
    · intro a ha
      exact (hmem _).2 ⟨_, hΦ3 y hy a ha, hsR _ _⟩
    · refine bd_add fun a ha => hAs _ ?_
      obtain ⟨x, hx, m, hm, h⟩ := hdec _ (hz y hy a ha)
      have hz0 : s (Φ y) - y = (Φ y - y) - (Φ y - s (Φ y)) := by abel
      have h2 : p (x + m) = 0 := by
        rw [← h, ← algebraMap_smul K a, map_smul, hz0, map_sub p, hpw y hy, hpe _ (hs2 _)]; simp
      rw [map_add, hpA x hx, hpM m hm, zero_add] at h2
      rw [h, h2, add_zero]; exact hx
  have hP : ∀ x ∈ P, x ∈ Bd (c ^ (3 * n + 12)) (s • Λ) := by
    intro x hx
    obtain ⟨a, ha, m, hm, rfl⟩ := hdec x hx
    exact Submodule.add_mem _ (bd_mono (hAs a ha) (by omega)) (hMs m hm)
  refine ⟨s, hs1, hs2, hsI, hP, fun x hx hxP => ?_⟩
  refine of_dual H hk1 (n := 3 * n + 12) (hPi ▸ hxP) fun y hy => ?_
  refine bd_mono (pair_both H h1 hc (n := 0) (k := 0) (bd_self hx) (hP y hy) ?_) (by omega)
  intro u hu v hv
  obtain ⟨u', hu', rfl⟩ := (hmem u).1 hu
  obtain ⟨v', hv', rfl⟩ := (hmem v).1 hv
  rw [hs1]
  exact hLL _ hu' _ hv'

end Generic

section Integers
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in

theorem exists_ext (L : Submodule (𝓞 K) V) (σ : L →ₗ[𝓞 K] V) : ∃ Ψ : V →ₗ[K] V, ∀ y : L, Ψ y = σ y := by
  have hB : Module.Baer (𝓞 K) V := by
    intro I g
    by_cases hI : I = ⊥
    · refine ⟨0, fun x hx => ?_⟩
      have : (⟨x, hx⟩ : I) = 0 := Subtype.ext (by simpa [hI] using hx)
      rw [this]; simp
    · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      have ha1 : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha0
      refine ⟨LinearMap.toSpanSingleton (𝓞 K) V ((algebraMap (𝓞 K) K a)⁻¹ • g ⟨a, ha⟩), fun x hx => ?_⟩
      have h : x • g ⟨a, ha⟩ = a • g ⟨x, hx⟩ := by
        rw [← map_smul, ← map_smul]; congr 1; ext; simp [mul_comm]
      rw [LinearMap.toSpanSingleton_apply, smul_comm, h, ← algebraMap_smul K a, inv_smul_smul₀ ha1]
  obtain ⟨h, hh⟩ := hB.extension_property L.subtype L.injective_subtype σ
  exact ⟨LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K h, fun y => LinearMap.congr_fun hh y⟩

theorem exists_lift [FiniteDimensional K V] (H : HermSpace K V) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    {J : Type} [Fintype J] [DecidableEq J] {e f : J → V}
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) (L : Submodule (𝓞 K) V) (hL : L.FG)
    (hLf : ∀ y ∈ L, y ∈ Submodule.span K (Set.range f))
    (hint : ∀ y ∈ L, ∀ x ∈ Λ ⊓ rs (𝓞 K) (Submodule.span K (Set.range e)), H.B x y ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ Ψ : V →ₗ[K] V, ∀ y ∈ L, Ψ y ∈ Λ ∧ ∀ b, H.B (Ψ y - y) (e b) = 0 := by
  have hΛ := (isLatMod_top_bot_iff Λ).1 hU.1
  let p : V →ₗ[𝓞 K] V := (pr H e f).restrictScalars (𝓞 K)
  let N : Submodule (𝓞 K) V := Λ ⊓ L.comap p
  let ρ : N →ₗ[𝓞 K] L := p.restrict fun x hx => hx.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    have hx : ∀ x : ↥(Λ ⊓ rs (𝓞 K) (Submodule.span K (Set.range e))), IsIntegral ℤ (H.B x y) := fun x =>
      (GlobalTheory.UnimodQuot.mem_one_iff _).1 (hint y hy x x.2)
    let φ : ↥(Λ ⊓ rs (𝓞 K) (Submodule.span K (Set.range e))) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x y, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) y = H.B a y + H.B b y
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) y = algebraMap (𝓞 K) K a * H.B b y
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨l, hl, h'⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU _ φ
    have hb : ∀ b, H.B (l - y) (e b) = 0 := by
      intro b
      obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem hΛ (e b)
      have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have hs' : algebraMap (𝓞 K) K s • e b ∈ Λ := by rw [algebraMap_smul]; exact hs
      have h1 : H.B (algebraMap (𝓞 K) K s • e b) l = H.B (algebraMap (𝓞 K) K s • e b) y :=
        h' ⟨_, hs', (Submodule.span K (Set.range e)).smul_mem _ (Submodule.subset_span (Set.mem_range_self b))⟩
      rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at h1
      rw [← H.herm, map_sub, smul_right_injective K hs0 h1, sub_self, star_zero]
    have hpl : pr H e f l = y := by
      have := pr_zero H e f hb
      rwa [map_sub, pr_fix H hef (hLf y hy), sub_eq_zero] at this
    exact ⟨⟨l, hl, show pr H e f l ∈ L from hpl ▸ hy⟩, Subtype.ext hpl⟩
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property ρ LinearMap.id hρ
  obtain ⟨Ψ, hΨ⟩ := exists_ext L (N.subtype ∘ₗ σ)
  refine ⟨Ψ, fun y hy => ?_⟩
  have h1 : Ψ y = σ ⟨y, hy⟩ := hΨ ⟨y, hy⟩
  have h2 : pr H e f (σ ⟨y, hy⟩) = y := congrArg Subtype.val (LinearMap.congr_fun hσ ⟨y, hy⟩)
  refine ⟨h1 ▸ (σ ⟨y, hy⟩).2.1, fun b => ?_⟩
  have h3 : pr H e f (Ψ y - y) = 0 := by rw [map_sub, h1, h2, pr_fix H hef (hLf y hy), sub_self]
  have h4 := pr_adj H e f (e b) (Ψ y - y)
  have h5 := pr_adj H f e (Ψ y - y) (e b)
  rw [h3, pr_fix H (e := f) (f := e) ?_ (Submodule.subset_span ⟨b, rfl⟩)] at h5
  · simpa using h5.symm
  · intro a a'
    rw [← H.herm, hef]
    by_cases h : a = a' <;> simp [h, eq_comm]

theorem mem_line {A : Submodule (𝓞 K) K} {v x : V} : x ∈ line A v ↔ ∃ a ∈ A, a • v = x := by
  simp [line]

theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (hv : v ∈ S) : line A v ≤ rs (𝓞 K) S := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := mem_line.1 hx
  exact S.smul_mem a hv

theorem mem_span_of_line {A : Submodule (𝓞 K) K} (hA : A ≠ ⊥) {v : V} {P : Submodule (𝓞 K) V}
    (h : line A v ≤ P) : v ∈ Submodule.span K (P : Set V) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  rw [← Submodule.smul_mem_iff _ ha0]
  exact Submodule.subset_span (h (mem_line.2 ⟨a, ha, rfl⟩))

theorem ipow_ne_bot {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) : ipow 𝔡 n ≠ ⊥ := by
  unfold ipow
  rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
  exact zpow_ne_zero n (FractionalIdeal.coeIdeal_ne_zero.2 h)

theorem ipow_fg (𝔡 : Ideal (𝓞 K)) (n : ℤ) : (ipow 𝔡 n).FG := by
  unfold ipow
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _

theorem lift_bd {H : HermSpace K V} {r : ℕ} (N : NF H r) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    (hL : IsLift N.F N.F' N.Wt) (hsp : N.Split Λ) {c : Ideal (𝓞 K)}
    (hk : c • dual H (latTh N.F N.F' Λ) ≤ latTh N.F N.F' Λ) {l v : V} (hl : l ∈ Λ) (hv : v ∈ N.Pi)
    (hw : l - v ∈ N.Wt) : v ∈ Bd c Λ := by
  have hΛ := (isLatMod_top_bot_iff Λ).1 hU.1
  have hII : II N.F N.F' ≤ V0 N.F N.F' := inf_le_left.trans (le_sup_left.trans le_sup_left)
  unfold NF.Split at hsp
  rw [hsp] at hk
  have hd : l - v ∈ dual H ((Λ ⊓ rs (𝓞 K) N.Wt) ⊔ rs (𝓞 K) (II N.F N.F')) := by
    rw [mem_dual_iff]
    constructor
    · obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem hΛ (l - v)
      have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have hs' : algebraMap (𝓞 K) K s • (l - v) ∈ Λ := by rw [algebraMap_smul]; exact hs
      rw [← Submodule.smul_mem_iff _ hs0]
      exact Submodule.subset_span (Submodule.mem_sup_left ⟨hs', N.Wt.smul_mem _ hw⟩)
    · intro x hx
      obtain ⟨a, ⟨ha, haW⟩, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
      have e1 : H.B (l - v) i = 0 := by rw [← H.herm, hL.1 _ hw i (hII hi), star_zero]
      have e2 : H.B v a = 0 := (mem_perp_iff H _ v).1 hv a haW
      rw [map_add, e1, add_zero, map_sub, LinearMap.sub_apply, e2, sub_zero]
      rw [← hU.2] at hl
      exact ((mem_dual_iff H Λ l).1 hl).2 a ha
  intro a ha
  obtain ⟨x, ⟨hx, hxW⟩, i, hi, h⟩ := Submodule.mem_sup.1 (smul_le_iff.1 hk _ hd a ha)
  have hiW : i ∈ N.Wt ⊓ II N.F N.F' := by
    refine ⟨?_, hi⟩
    rw [eq_sub_of_add_eq' h]
    exact (rs (𝓞 K) N.Wt).sub_mem ((rs (𝓞 K) N.Wt).smul_mem a hw) hxW
  rw [hL.2.1, Submodule.mem_bot] at hiW
  rw [hiW, add_zero, smul_sub] at h
  have : a • v = a • l - x := by rw [h]; abel
  rw [this]
  exact Λ.sub_mem (Λ.smul_mem a hl) hx

theorem e_mem_X {H : HermSpace K V} {r : ℕ} (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∈ F.X :=
  Submodule.subset_span ⟨a, a.2, rfl⟩

theorem c_ne {H : HermSpace K V} {r : ℕ} (N : NF H r) : N.c ≠ 0 := by
  intro h
  have := N.c_norm
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem e_mem_II {H : HermSpace K V} {r : ℕ} (N : NF H r) (a : Fin r) (ha : N.j ≤ a.val) :
    N.F.e a.castSucc ∈ II N.F N.F' := by
  refine ⟨e_mem_X _ a, ?_⟩
  have := e_mem_X N.F' a
  rw [N.same _ (by simpa using ha)] at this
  exact (Submodule.smul_mem_iff _ (c_ne N)).1 this

def dualPart {H : HermSpace K V} {r : ℕ} (N : NF H r) : Submodule (𝓞 K) V :=
  ⨆ a : Fin r, ⨆ _ : N.j ≤ a.val, line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)

theorem dualPart_fg {H : HermSpace K V} {r : ℕ} (N : NF H r) : (dualPart N).FG :=
  Submodule.fg_iSup _ fun _ => Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _

theorem hermFramePair_lattice_decomposes_dualSpanPart {H : HermSpace K V} {r : ℕ} (N : NF H r) :
    ∀ x ∈ N.P0, ∃ a ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'), ∃ m ∈ dualPart N, x = a + m := by
  intro x hx
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.1 hx
  refine ⟨a, ⟨Submodule.mem_sup_left ha, ?_⟩, m, hm, rfl⟩
  refine (show _ ≤ rs (𝓞 K) (V0 N.F N.F') from sup_le (sup_le (iSup_le fun a => line_le ?_)
    (iSup_le fun a => iSup_le fun _ => line_le ?_)) (line_le ?_)) ha
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a))
  · exact Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem dualPart_le {H : HermSpace K V} {r : ℕ} (N : NF H r) : dualPart N ≤ rs (𝓞 K) N.Ist :=
  iSup_le fun a => iSup_le fun ha => line_le (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem span_hermFramePair_lattice_eq_sup {H : HermSpace K V} {r : ℕ} (N : NF H r) :
    Submodule.span K (N.P0 : Set V) = V0 N.F N.F' ⊔ N.Ist := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨a, ha, m, hm, rfl⟩ := hermFramePair_lattice_decomposes_dualSpanPart N x hx
    exact Submodule.add_mem_sup ha.2 (dualPart_le N hm)
  have he : ∀ a : Fin r, N.F.e a.castSucc ∈ Submodule.span K (N.P0 : Set V) := fun a =>
    mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a))))
  have hz : N.F.z ∈ Submodule.span K (N.P0 : Set V) :=
    mem_span_of_line (A := 1) (fun h => one_ne_zero ((Submodule.mem_bot (𝓞 K)).1
      (h ▸ Submodule.mem_one.2 ⟨1, map_one _⟩ : (1 : K) ∈ (⊥ : Submodule (𝓞 K) K)))) (le_sup_of_le_left le_sup_right)
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, -, rfl⟩
    exact he a
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, -, rfl⟩
    by_cases ha : a.val < N.j
    · exact mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
        (le_iSup₂_of_le (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha le_rfl))))
    · show N.F'.e a.castSucc ∈ _
      rw [N.same _ (by simpa using ha)]
      exact Submodule.smul_mem _ _ (he a)
  · refine Submodule.span_le.2 ?_
    rintro _ (rfl | rfl)
    · exact hz
    · show N.F'.e (Fin.last r) ∈ _
      rw [N.same _ (by simpa using N.j_le)]
      exact Submodule.smul_mem _ _ hz
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact mem_span_of_line (ipow_ne_bot N.𝔡_ne _) (le_sup_of_le_right
      (le_iSup₂_of_le (f := fun (a : Fin r) (_ : N.j ≤ a.val) => line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)) a ha le_rfl))

end Integers

theorem near_of_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∀ e : ℕ, 2 ≤ e → 𝔠 ^ e • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ Λ → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ N.P0 → 𝔠 ^ e • (Λ ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ N.P0 → Λ ⊓ rs (𝓞 K) (II N.F N.F') ≤ N.P0 → ∃ s ∈ N.ZI, N.Near (𝔠 ^ (6 * e + 30)) (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT c hc0 hcs hcT hcD hsp n _ h1 _ _ h4
  obtain ⟨hNF, hL, hC, -, -, -, -, -, -, -, -, hPi⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.T.hermFramePair_ideal_kills_discriminantModules K V H hK r N g Λ hg hT c hc0 hcs hcT hcD
  obtain ⟨t, ht⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram K hK
  have hU : IsUnimod H Λ := hT.1.1
  let J := {b : Fin r // N.j ≤ b.val}
  let e : J → V := fun b => N.F.e b.1.castSucc
  let f : J → V := fun b => N.ist b.1
  have hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0 := fun a b => by
    simp only [e, f, N.ist_e a.1 b.1 b.2]
    exact if_congr Subtype.ext_iff.symm rfl rfl
  have heI : Submodule.span K (Set.range e) ≤ II N.F N.F' := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact e_mem_II N b.1 b.2
  have hII : II N.F N.F' ≤ V0 N.F N.F' := inf_le_left.trans (le_sup_left.trans le_sup_left)
  have hV0 : ∀ x ∈ V0 N.F N.F', ∀ b, H.B x (e b) = 0 := fun x hx b =>
    (hNF.2.2.2.2.2.1 _ (e_mem_X _ b.1)).2 (e_mem_II N b.1 b.2) x hx
  have hWt : ∀ x ∈ N.Wt, ∀ b, H.B x (e b) = 0 := fun x hx b => by
    rw [← H.herm, hL.1 x hx _ (hII (e_mem_II N b.1 b.2)), star_zero]
  have hMf : ∀ y ∈ dualPart N, y ∈ Submodule.span K (Set.range f) := fun y hy => by
    have h : N.Ist ≤ Submodule.span K (Set.range f) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨b, hb, rfl⟩; exact ⟨⟨b, hb⟩, rfl⟩
    exact h (dualPart_le N hy)
  have hMP : dualPart N ≤ N.P0 := le_sup_right
  have hst : StarSt K (⊤ : Ideal (𝓞 K)) := fun x _ => by
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (GlobalTheory.UnimodQuot.star_mem_one (Submodule.mem_one.2 ⟨x, rfl⟩))
    exact ⟨y, trivial, hy⟩
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx => by
    rw [← hU.2] at hx
    exact ((mem_dual_iff H Λ x).1 hx).2
  obtain ⟨Ψ, hΨ⟩ := exists_lift H hU hef (c • dualPart N) ((dualPart_fg N).of_le Submodule.smul_le_right)
    (fun y hy => hMf y (Submodule.smul_le_right hy)) (fun y hy x hx => by
      rw [← H.herm]
      exact star_one_mem hst (((mem_dual_iff H _ y).1 (k3 (Submodule.smul_mono le_rfl hMP hy))).2 x
        (h4 ⟨hx.1, heI hx.2⟩)))
  let π := N.Pi.projection N.Wt hC.symm
  have hlin : ∀ (L : V →ₗ[K] V) (a : 𝓞 K) v, L (a • v) = a • L v := fun L a v => by
    rw [← algebraMap_smul K a v, map_smul, algebraMap_smul]
  obtain ⟨s, hs1, hs2, hs3, hs4, hs5⟩ := core H e f hef (fun a b => N.F.iso _ _)
    (fun a b => N.ist_iso _ _ a.2 b.2) N.P0 (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) (dualPart N) Λ N.Pi
    (by rw [hPi, span_hermFramePair_lattice_eq_sup]) c hst hcs n t ht inf_le_left hMP (hermFramePair_lattice_decomposes_dualSpanPart N) (fun x hx => hV0 x hx.2) hMf
    (fun b => by rw [hPi]; exact Submodule.mem_sup_left (hII (e_mem_II N b.1 b.2))) (smul_le_iff.1 h1) hint k2 k3
    (π ∘ₗ Ψ) (fun y _ => Submodule.projection_apply_mem hC.symm _) (fun y hy b => by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc0
      have h := (hΨ _ (Submodule.smul_mem_smul ha hy)).2 b
      rw [hlin, ← smul_sub, B_smul, Algebra.smul_def, mul_eq_zero] at h
      have h' := h.resolve_left (by simpa using ha0)
      have h2 := hWt _ (Submodule.sub_projection_mem hC.symm (Ψ y)) b
      have e1 : (π ∘ₗ Ψ) y - y = (Ψ y - y) - (Ψ y - π (Ψ y)) := by
        rw [LinearMap.comp_apply]; abel
      rw [e1, map_sub, LinearMap.sub_apply, h', h2, sub_self])
    (fun y hy => by
      refine bd_add (n := 1) (m := 3) fun a ha => ?_
      rw [pow_one] at ha
      rw [← hlin]
      exact lift_bd N hU hL hsp k1 (hΨ _ (Submodule.smul_mem_smul ha hy)).1
        (Submodule.projection_apply_mem hC.symm _) (Submodule.sub_projection_mem hC.symm _))
  have hsI : ∀ v, s v - v ∈ II N.F N.F' := fun v => by
    rw [← neg_sub]; exact Submodule.neg_mem _ (heI (hs2 v))
  refine ⟨s, ⟨⟨Subgroup.subset_closure ⟨⟨hs1, s.bijective, fun a => ?_, fun y _ => (hsI y).1⟩,
    ⟨hs1, s.bijective, fun a => ?_, fun y _ => (hsI y).2⟩⟩, ?_⟩, ?_⟩, ?_, ?_⟩
  · have := hs3 _ (hV0 _ (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X N.F a))))
    simp [this]
  · have := hs3 _ (hV0 _ (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X N.F' a))))
    simp [this]
  · exact (mem_fixingSubgroup_iff _).2 fun y hy => hs3 y (hV0 y hy)
  · exact (mem_fixingSubgroup_iff _).2 fun y hy => hs3 y (hWt y hy)
  · refine le_inf (smul_le_iff.2 fun x hx => bd_mono (hs4 x hx) (by omega)) (Submodule.smul_le_right.trans ?_)
    intro x hx
    show x ∈ N.Pi
    rw [hPi, ← span_hermFramePair_lattice_eq_sup]
    exact Submodule.subset_span hx
  · exact smul_le_iff.2 fun x hx => bd_mono (hs5 x hx.1 hx.2) (by omega)

end GlobalTheory.DegCnt.DualPos
