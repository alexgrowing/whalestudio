import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.MultOne
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH

open Matrix Finset
open scoped Kronecker

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)

structure Lib (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop where
  zg : ZG t
  dec : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (U : URep k r) (h : ℝ) (m : ℕ),
    U.R.IsDS ε μ → GapAtLeast ε μ h → t _ ε + m < h → Decay U m
  uniq : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (h : ℝ),
    R.IsDS ε μ → R'.IsDS ε μ → GapAtLeast ε μ h → t _ ε < h →
    ∃ e : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ GG k r, ∀ x, e (R.σ g x) = R'.σ g (e x)
  exist : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ μ' : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (h : ℝ),
    R.IsDS ε μ → IsHCParam μ' → GapAtLeast ε μ' h → t _ ε < h → ∃ R' : Rep k r, R'.IsDS ε μ'

structure Steps : Prop where
  infChar : PI.DSInfCharCap.DSInfCharCap
  decOfInj : DecOfInj
  decOfTrace : DecOfTrace
  homCat : HomCat
  okTriv : OKTriv
  okVr : OKVr
  okWedge : OKWedge
  okTens : OKTens
  matHom : MatHom
  uIso : UIso
  homLie : HomLie
  casSplit : CasSplit
  casDS : CasDS
  wedgeInt : WedgeInt
  wedgeQ : WedgeQ
  schur : Schur
  adj : Adj
  multOne : MultOne
  inj : InjStep
  occ : OccStep
  zuckH : ZuckH
  decTens : DecTens
  toRaw : ToRaw
  count : Count

section lin

variable {O : Type 1} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}

theorem dec_iso (C : IsLinCat N Hom) {κ : Type} [Fintype κ] {X : O} {T T' : κ → O}
    (h : ∃ io pr, IsDec Hom X T io pr) (e : ∀ s, IsIso Hom (T s) (T' s)) : ∃ io pr, IsDec Hom X T' io pr := by
  obtain ⟨io, pr, h⟩ := h
  choose f g hf hg hgf hfg using e
  have a1 : ∀ s y, g s (f s y) = y := fun s y => LinearMap.congr_fun (hgf s) y
  have a2 : ∀ s y, f s (g s y) = y := fun s y => LinearMap.congr_fun (hfg s) y
  refine ⟨fun s => io s ∘ₗ g s, fun s => f s ∘ₗ pr s, fun s => C.comp _ _ _ _ _ (hg s) (h.io_hom s),
    fun s => C.comp _ _ _ _ _ (h.pr_hom s) (hf s), ?_, fun s => ?_, fun s s' hs => ?_⟩
  · rw [← h.sum]
    exact Finset.sum_congr rfl fun s _ => LinearMap.ext fun x => by simp [a1]
  · refine LinearMap.ext fun y => ?_
    have := LinearMap.congr_fun (h.pr_io s) (g s y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this ⊢
    rw [this, a2]
  · refine LinearMap.ext fun y => ?_
    have := LinearMap.congr_fun (h.pr_io_ne s s' hs) (g s' y)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this ⊢
    rw [this, map_zero]

end lin

section num

variable {n : ℕ}

theorem shift_shift (b : Bool) (μ : Fin n → ℝ) (s : Fin n) : shift (!b) (shift b μ s) s = μ := by
  cases b <;> simp [shift]

theorem shift_apply (b : Bool) (μ : Fin n → ℝ) (s a : Fin n) :
    shift b μ s a = μ a + if a = s then (if b then -1 else 1) else 0 := by
  cases b <;> by_cases h : a = s <;> simp [shift, h, Pi.single_apply, sub_eq_add_neg]

theorem gap_shift {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hg : GapAtLeast ε μ h) (b : Bool) (s : Fin n) :
    GapAtLeast ε (shift b μ s) (h - 1) := by
  intro a c hac
  have h1 := hg a c hac
  have hne : a ≠ c := fun e => hac (by rw [e])
  rw [shift_apply, shift_apply]
  rw [le_abs] at h1 ⊢
  by_cases e1 : a = s <;> by_cases e2 : c = s
  · exact absurd (e1.trans e2.symm) hne
  all_goals cases b <;> simp only [e1, e2, if_true, if_false, Bool.false_eq_true] at h1 ⊢ <;>
    rcases h1 with h1 | h1 <;> first | (left; linarith) | (right; linarith)

theorem casG_shift (b : Bool) (μ : Fin n → ℝ) (s : Fin n) :
    casG (shift b μ s) = casG μ + 2 * (if b then -1 else 1) * μ s + 1 := by
  have : ∑ a, shift b μ s a ^ 2 = ∑ a, (μ a ^ 2 + if a = s then 2 * (if b then -1 else 1) * μ s + 1 else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [shift_apply]
    by_cases h : a = s
    · subst h; cases b <;> simp <;> ring
    · simp [h]
  unfold casG
  rw [this, Finset.sum_add_distrib]
  simp
  ring

theorem cas_ne {μ : Fin n → ℝ} (hμ : StrictAnti μ) (b : Bool) (s t : Fin n) :
    (casG (shift b (shift b μ s) t) : ℂ) ≠ 2 * (casG (shift b μ s) : ℂ) - (casG μ : ℂ) := by
  intro h
  have h' : casG (shift b (shift b μ s) t) = 2 * casG (shift b μ s) - casG μ := by exact_mod_cast h
  rw [casG_shift b (shift b μ s) t, casG_shift b μ s, shift_apply] at h'
  by_cases e : t = s
  · subst e
    cases b <;> simp at h' <;> linarith
  · apply e
    apply hμ.injective
    cases b <;> simp [e] at h' <;> linarith

theorem shift_inj (b : Bool) (μ : Fin n → ℝ) : Function.Injective (shift b μ) := by
  intro s t h
  have := congrFun h s
  rw [shift_apply, shift_apply] at this
  by_contra e
  cases b <;> simp [e] at this

theorem near {ε : Fin n → Bool} {μ : Fin n → ℝ} {h D : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hD : ∀ a c, a < c → D ≤ μ a - μ c) {ν : Fin n → ℝ} (j : ℕ) (hj : (j : ℝ) < D)
    (hx : ∀ a, ∃ x : ℕ, x ≤ j ∧ ν a = μ a + x) :
    IsHCParam ν ∧ GapAtLeast ε ν (h - j) ∧ ∀ a c, a < c → D - j ≤ ν a - ν c := by
  choose x hxj hx using hx
  have hx0 : ∀ a, (0 : ℝ) ≤ x a := fun a => Nat.cast_nonneg _
  have hx1 : ∀ a, (x a : ℝ) ≤ j := fun a => by exact_mod_cast hxj a
  have h3 : ∀ a c, a < c → D - j ≤ ν a - ν c := fun a c hac => by
    have := hD a c hac
    rw [hx, hx]; linarith [hx0 a, hx1 c]
  refine ⟨⟨fun a c hac => by linarith [h3 a c hac], fun a => ?_⟩, fun a c hac => ?_, h3⟩
  · obtain ⟨m, hm⟩ := hμ.2 a
    exact ⟨m + x a, by rw [hx]; push_cast; linarith⟩
  · have h1 := hg a c hac
    rw [le_abs] at h1 ⊢
    rw [hx, hx]
    rcases h1 with h1 | h1
    · left; linarith [hx0 a, hx1 c]
    · right; linarith [hx0 c, hx1 a]

theorem ind_le {m : ℕ} (J : Sub n m) (a : Fin n) : (if a ∈ J.1 then 1 else 0 : ℕ) ≤ m := by
  split_ifs with h
  · rw [← J.2]; exact Finset.card_pos.2 ⟨a, h⟩
  · exact Nat.zero_le _

theorem addSet_inj {l : ℕ} (μ : Fin n → ℝ) : Function.Injective fun I : Sub n l => addSet μ I.1 := by
  intro I J h
  refine Subtype.ext (Finset.ext fun a => ?_)
  have := congrFun h a
  simp only [addSet, add_right_inj] at this
  by_cases h1 : a ∈ I.1 <;> by_cases h2 : a ∈ J.1 <;> simp_all

end num

variable {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

def mkU {μ : Fin (2 * r + k + 1) → ℝ} (R : Rep k r) (h : R.IsDS ε μ) : URep k r :=
  ⟨R, CompanionTheory.LimBd.SchurHpk.isURepOn_of_ds h.2⟩

theorem iso_of (S : Steps) (Lb : Lib t) {μ : Fin (2 * r + k + 1) → ℝ} {U U' : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hU' : U'.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε < h) :
    IsIso (N := M) IsHom (one U) (one U') :=
  S.uIso k r _ U U' (Lb.uniq k r ε μ U.R U'.R h hU hU' hg ht)

theorem injV (S : Steps) (Lb : Lib t) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) < h) :
    ∃ T : {s // IsHCParam (shift b μ s)} → URep k r, (∀ s, (T s).R.IsDS ε (shift b μ s)) ∧
      JInj (N := M) IsHom (vr k r b, U) (fun s => one (T s)) ∧
      ∀ s, ∃ p, IsHom (vr k r b, U) (one (T s)) p ∧ p ≠ 0 := by
  have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  obtain ⟨T, hT, hin, hof⟩ := S.zuckH t Lb.zg k r ε μ U b h hU hg (by linarith)
  have hd := Lb.dec k r ε μ U h _ hU hg ht
  exact ⟨T, hT, S.inj k r _ _ T _ (S.okVr k r b) ⟨_, _, hU⟩ (fun s => ⟨_, _, hT s⟩) hd (by show 1 + _ + 1 ≤ _; omega) hin,
    fun s => S.occ k r _ _ _ (S.okVr k r b) ⟨_, _, hU⟩ ⟨_, _, hT s⟩ hd (by show 1 + _ + 1 ≤ _; omega) (hof s)⟩

theorem decV (S : Steps) (Lb : Lib t) (hk : 1 ≤ k) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 < h)
    (T : Fin (2 * r + k + 1) → URep k r) (hT : ∀ s, (T s).R.IsDS ε (shift b μ s)) :
    ∃ io pr, IsDec (N := M) IsHom (vr k r b, U) (fun s => one (T s)) io pr := by
  have C := S.homCat k r
  have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hsimp := S.schur S.infChar k r ε _ _ T (shift_inj b μ) hT
  have adj' : ∀ U U' : URep k r, ∃ e : (M (vr k r (!b), U) →ₗ[ℂ] M (one U')) ≃ₗ[ℂ] (M (one U) →ₗ[ℂ] M (vr k r b, U')),
      ∀ p, IsHom (vr k r (!b), U) (one U') p ↔ IsHom (one U) (vr k r b, U') (e p) := by
    cases b
    · exact S.adj k r true
    · exact S.adj k r false
  have occ : ∀ s, ∃ i, IsHom (one (T s)) (vr k r b, U) i ∧ i ≠ 0 := by
    intro s
    obtain ⟨T', hT', -, hp⟩ := injV S Lb (!b) (hT s) (gap_shift hg b s) (by linarith)
    have hs : IsHCParam (shift (!b) (shift b μ s) s) := by rw [shift_shift]; exact hU.1
    obtain ⟨p, hp, hp0⟩ := hp ⟨s, hs⟩
    have hd : (T' ⟨s, hs⟩).R.IsDS ε μ := by simpa only [shift_shift] using hT' ⟨s, hs⟩
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb hd hU hg (by linarith)
    obtain ⟨e, he⟩ := adj' (T s) U
    refine ⟨e (f ∘ₗ p), (he _).1 (C.comp _ _ _ _ _ hp hf), fun h0 => hp0 ?_⟩
    have h2 : f ∘ₗ p = 0 := e.map_eq_zero_iff.1 h0
    calc p = (g ∘ₗ f) ∘ₗ p := by rw [hgf, LinearMap.id_comp]
      _ = 0 := by rw [LinearMap.comp_assoc, h2, LinearMap.comp_zero]
  refine S.decOfInj _ _ _ C _ _ _ hsimp ?_ (fun s => ?_) occ
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b hU hg (by linarith)
    intro x hx
    refine hi x fun s p hp => ?_
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb (hT' s) (hT s.1) (gap_shift hg b s.1) (by linarith)
    have h2 := hx s.1 _ (C.comp _ _ _ _ _ hp hf)
    have h3 := LinearMap.congr_fun hgf (p x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2 h3
    rw [← h3, h2, map_zero]
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b (hT s) (gap_shift hg b s) (by linarith)
    have cB := S.casDS S.infChar k r ε _ (T s) hk (hT s)
    have m1 : AtMostOne (N := M) IsHom (one U) (vr k r (!b), T s) := by
      have := fun hi' ho' => S.multOne k r (!b) (T s) U _ T' _ _ _ (fun F => (cB F).1) (cB (triv k r)).2
        (S.casDS S.infChar k r ε _ U hk hU (triv k r)).2
        (fun u => (S.casDS S.infChar k r ε _ (T' u) hk (hT' u) (triv k r)).2)
        (fun u => cas_ne hU.1.1 b s u.1) hi' (hsimp.2.1 s) ⟨_, _, hU⟩ ho'
      cases b
      · exact this hi (occ s)
      · exact this hi (occ s)
    obtain ⟨e, he⟩ := S.adj k r b U (T s)
    intro f g hf hg'
    obtain ⟨α, β, hab, h0⟩ := m1 _ _ ((he f).1 hf) ((he g).1 hg')
    refine ⟨α, β, hab, e.map_eq_zero_iff.1 ?_⟩
    rw [map_add, map_smul, map_smul, h0]

theorem decW (S : Steps) (Lb : Lib t) (hk : 1 ≤ k) : ∀ (l : ℕ) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ},
    U.R.IsDS ε μ → GapAtLeast ε μ h → t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 + l < h →
    (∀ a c, a < c → (l : ℝ) + 1 ≤ μ a - μ c) →
    ∀ T : Sub (2 * r + k + 1) l → URep k r, (∀ I, (T I).R.IsDS ε (addSet μ I.1)) →
    ∃ io pr, IsDec (N := M) IsHom (wedge k r l, U) (fun I => one (T I)) io pr
  | 0, μ, U, h, hU, hg, ht, _, T, hT => by
    have C := S.homCat k r
    have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hI : ∀ I : Sub (2 * r + k + 1) 0, I = ⟨∅, rfl⟩ := fun I => Subtype.ext (Finset.card_eq_zero.1 I.2)
    have : Unique (Sub (2 * r + k + 1) 0) := ⟨⟨⟨∅, rfl⟩⟩, hI⟩
    have hc : ∀ (g : Mx k r) I J, cmp 0 g I J = 1 := fun g I J => Matrix.det_isEmpty
    refine dec_iso C (T := fun _ => one U) ⟨fun _ => mAct (Matrix.of fun _ _ => 1), fun _ => mAct (Matrix.of fun _ _ => 1),
      fun _ => S.matHom k r _ _ U _ fun g _ => ?_, fun _ => S.matHom k r _ _ U _ fun g _ => ?_, ?_, fun _ => ?_,
      fun I J hIJ => absurd (Subsingleton.elim I J) hIJ⟩ fun I => iso_of S Lb hU ?_ hg (by rw [Nat.cast_zero] at ht; linarith)
    · ext I u; simp [Matrix.mul_apply, hc]
    · ext u I; simp [Matrix.mul_apply, hc]
    · refine LinearMap.ext fun x => funext fun I => ?_
      simp [mAct_apply, Subsingleton.elim default I]
    · refine LinearMap.ext fun x => funext fun u => ?_
      simp [mAct_apply]
    · have e : addSet μ I.1 = μ := by rw [hI I]; funext a; simp [addSet]
      simpa only [e] using hT I
  | m + 1, μ, U, h, hU, hg, ht, hD, T, hT => by
    classical
    have C := S.homCat k r
    have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [Nat.cast_succ m] at ht hD
    let P := {ν : Fin (2 * r + k + 1) → ℝ // IsHCParam ν ∧ GapAtLeast ε ν (h - ((m + 1 : ℕ) : ℝ))}
    have hex : ∀ ν : P, ∃ V : URep k r, V.R.IsDS ε ν.1 := fun ν => by
      obtain ⟨R', hR'⟩ := Lb.exist k r ε μ ν.1 U.R _ hU ν.2.1 ν.2.2 (by push_cast; linarith)
      exact ⟨mkU R' hR', hR'⟩
    choose V hV using hex
    have nr : ∀ {ν : Fin (2 * r + k + 1) → ℝ}, (∀ a, ∃ x : ℕ, x ≤ m + 1 ∧ ν a = μ a + x) →
        IsHCParam ν ∧ GapAtLeast ε ν (h - ((m + 1 : ℕ) : ℝ)) := fun hx =>
      have := near hU.1 hg hD (m + 1) (by push_cast; linarith) hx
      ⟨this.1, this.2.1⟩
    have hJ : ∀ (J : Sub (2 * r + k + 1) m) a, ∃ x : ℕ, x ≤ m ∧ addSet μ J.1 a = μ a + x := fun J a =>
      ⟨_, ind_le J a, by simp [addSet]⟩
    have hs : ∀ (s a : Fin (2 * r + k + 1)), ∃ x : ℕ, x ≤ 1 ∧ shift false μ s a = μ a + x := fun s a =>
      ⟨if a = s then 1 else 0, by split_ifs <;> simp, by rw [shift_apply]; simp⟩
    let pJ : Sub (2 * r + k + 1) m → P := fun J => ⟨addSet μ J.1, nr fun a =>
      let ⟨x, h1, h2⟩ := hJ J a; ⟨x, by omega, h2⟩⟩
    let ps : Fin (2 * r + k + 1) → P := fun s => ⟨shift false μ s, nr fun a =>
      let ⟨x, h1, h2⟩ := hs s a; ⟨x, by omega, h2⟩⟩
    let par : Sub (2 * r + k + 1) m × Fin (2 * r + k + 1) → P := fun p =>
      ⟨addSet μ p.1.1 + Pi.single p.2 1, nr fun a =>
        ⟨(if a ∈ p.1.1 then 1 else 0) + (if a = p.2 then 1 else 0),
          add_le_add (ind_le p.1 a) (by split_ifs <;> simp), by simp [addSet, Pi.single_apply, add_assoc]⟩⟩
    let e : Sub (2 * r + k + 1) (m + 1) → P := fun I => ⟨addSet μ I.1, nr fun a => ⟨_, ind_le I a, by simp [addSet]⟩⟩
    have cs := fun ν : P => (S.casDS S.infChar k r ε _ (V ν) hk (hV ν) (triv k r)).2
    obtain ⟨hd1, hd2⟩ := S.decTens k r (wedge k r m) (vr k r false) U (S.okWedge k r m) (S.okVr k r false)
    obtain ⟨io₁, pr₁, D₁, e₁⟩ := hd1 _ _ (fun J => V (pJ J)) (fun p => V (par p)) (fun J => (casG (pJ J).1 : ℂ))
      (decW S Lb hk m hU hg (by linarith) (fun a c hac => by linarith [hD a c hac]) _ fun J => hV (pJ J))
      (fun J => decV S Lb hk false (hV (pJ J)) (near hU.1 hg hD m (by linarith) (hJ J)).2.1 (by linarith) _
        fun s => hV (par (J, s)))
      fun J => cs (pJ J)
    obtain ⟨io₂, pr₂, D₂, e₂⟩ := hd2 _ _ (fun s => V (ps s)) (fun p => V (par p)) (fun s => (casG (ps s).1 : ℂ))
      (decV S Lb hk false hU hg (by linarith) _ fun s => hV (ps s))
      (fun s => decW S Lb hk m (hV (ps s)) (gap_shift hg false s) (by linarith)
        (fun a c hac => by
          have := (near hU.1 hg hD 1 (by push_cast; linarith) (hs s)).2.2 a c hac
          push_cast at this
          show _ ≤ shift false μ s a - shift false μ s c
          linarith) _
        fun J => by
          have e' : addSet (ps s).1 J.1 = (par (J, s)).1 := by
            funext a; simp [ps, par, addSet, shift]; ring
          rw [e']; exact hV (par (J, s)))
      fun s => cs (ps s)
    obtain ⟨hint, hjj⟩ := S.wedgeInt (2 * r + k + 1) m
    have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    obtain ⟨c1, c2⟩ := S.count (2 * r + k + 1) m μ fun a c hac => by linarith [hD a c hac]
    have okX := S.okTens k r _ _ (S.okWedge k r m) (S.okVr k r false)
    refine dec_iso C (S.decOfTrace _ _ _ C P (fun ν => one (V ν))
      (S.schur S.infChar k r ε P (fun ν => ν.1) V Subtype.val_injective hV) _ par
      ((wedge k r m).tens (vr k r false), U) (wedge k r (m + 1), U) io₁ io₂ pr₁ pr₂ D₁ D₂
      (cas _) (cas1 _ _ U) (cas2 _ _ U) _ _ (fun ν => (casG ν.1 : ℂ)) (2 - (casG μ : ℂ)) (2 * ((m : ℂ) + 1)) e₁ e₂
      (fun ν i hi => LinearMap.ext fun x => ?_)
      (mAct (jW _ m)) (mAct (((m : ℂ) + 1)⁻¹ • (jW _ m)ᵀ))
      (S.matHom k r _ _ U _ fun g _ => (hint g).1)
      (S.matHom k r _ _ U _ fun g _ => ?_) ?_ (mul_ne_zero two_ne_zero hm1) ?_ _ e
      (fun I J hIJ => addSet_inj μ (congrArg Subtype.val hIJ)) (fun I => ?_) (fun ν hν => ?_))
      fun I => iso_of S Lb (hV (e I)) (hT I) (e I).2.2 (by push_cast; linarith)
    · rw [LinearMap.comp_apply, ← hom_cas S.homLie (S.okTriv k r) okX hi, cs ν]
      simp
    · rw [Matrix.smul_mul, Matrix.mul_smul]
      exact congrArg _ (hint g).2
    · rw [← mAct_mul, Matrix.smul_mul, hjj, smul_smul, inv_mul_cancel₀ hm1, one_smul, mAct_one]
    · rw [S.casSplit k r _ _ U (S.okWedge k r m) (S.okVr k r false),
        (S.casDS S.infChar k r ε _ U hk hU _).1, S.wedgeQ, mAct_sub, mAct_one, mAct_mul, mAct_smul,
        LinearMap.comp_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hm1, mul_one, sub_smul, smul_sub]
      abel
    · rw [← c1 I]
      refine Finset.sum_congr (Finset.filter_congr fun p _ => Subtype.ext_iff) fun p _ => ?_
      simp [pJ, ps, e, shift]
    · rw [← c2 ν.1 fun I h0 => hν I (Subtype.ext h0)]
      refine Finset.sum_congr (Finset.filter_congr fun p _ => Subtype.ext_iff) fun p _ => ?_
      simp [pJ, ps, shift]

def ZuckSm (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (h : ℝ), 1 ≤ k →
    R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h →
    (∀ (l : ℕ) (RI : Sub (2 * r + k + 1) l → Rep k r), t _ ε + ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 + l < h →
      (∀ a c, a < c → (l : ℝ) + 1 ≤ mu a - mu c) → (∀ I, (RI I).IsDS ε (addSet mu I.1)) →
      ∃ io pr, TensRaw (cmp l) R RI io pr) ∧
    ∀ RI : Fin (2 * r + k + 1) → Rep k r, t _ ε + ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 < h →
      (∀ s, (RI s).IsDS ε (mu - Pi.single s 1)) → ∃ io pr, TensRaw dualM R RI io pr

theorem zuckSm_of (S : Steps) (Lb : Lib t) : ZuckSm t := by
  intro k r ε mu R h hk hR hg
  refine ⟨fun l RI ht hD hI => ?_, fun RI ht hI => ?_⟩
  · exact S.toRaw k r (wedge k r l) (mkU R hR) _ (fun I => mkU (RI I) (hI I))
      (decW S Lb hk l (U := mkU R hR) hR hg (by push_cast at ht ⊢; linarith) hD _ hI)
  · exact S.toRaw k r (vr k r true) (mkU R hR) _ (fun s => mkU (RI s) (hI s))
      (decV S Lb hk true (U := mkU R hR) hR hg (by push_cast at ht ⊢; linarith) _ hI)

end CompanionTheory.Zuck

end
