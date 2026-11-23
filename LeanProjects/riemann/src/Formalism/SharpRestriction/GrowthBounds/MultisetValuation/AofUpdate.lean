import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RamifiedLatticeOfChainEstimates
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

structure LinD : Prop where
  Tt_add : ∀ v i j (F F' : X.Fm j), X.Tt v i j (F + F') = X.Tt v i j F + X.Tt v i j F'
  Tt_smul : ∀ v i j (a : X.G.Kf) (F : X.Fm j), X.Tt v i j (a • F) = a • X.Tt v i j F
  yv_add : ∀ v (F F' : X.Fm 0), X.yv v (F + F') = X.yv v F + X.yv v F'
  yv_smul : ∀ v (a : X.G.Kf) (F : X.Fm 0), X.yv v (a • F) = a • X.yv v F
  yv_comm : ∀ v v' (F : X.Fm 0), X.yv v (X.yv v' F) = X.yv v' (X.yv v F)

variable {X}

theorem Zop_add (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) (F F' : X.Fm j) :
    X.Zop v u m j (F + F') = X.Zop v u m j F + X.Zop v u m j F' := by
  unfold Sys.Zop Sys.Ttu
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL.Tt_add, smul_add, smul_add]

theorem Zop_smul (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) (a : X.G.Kf) (F : X.Fm j) :
    X.Zop v u m j (a • F) = a • X.Zop v u m j F := by
  unfold Sys.Zop Sys.Ttu
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL.Tt_smul]
  simp only [smul_smul]
  congr 1
  ring

theorem Zop_zero (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) : X.Zop v u m j 0 = 0 := by
  have h := Zop_smul hL v u m j 0 0
  simpa using h

variable (X)

def ZL (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (vs : List X.Pl) (F : X.Fm j) : X.Fm j :=
  vs.foldr (fun v F' => X.Zop v (u v) (m v) j F') F

def Aof (i0 : X.Pl → ℕ) (vs : List X.Pl) : ℝ := ∑ v, if v ∈ vs ∧ i0 v = 0 then (X.alEven v : ℝ) else 0

def Gen (j : ℕ) (vs : List X.Pl) : Set (X.Fm (j + 1)) :=
  {T | ∃ (a : X.G.Kf) (i0 : X.Pl → ℕ) (G' : X.Fm j), G' ∈ X.Int j ∧ (∀ v, i0 v ≤ X.G.P.r) ∧
    (∀ v, v ∉ vs → i0 v = 0) ∧ X.vGeK a (Aof X i0 vs) ∧ T = a • TtL X (j + 1) i0 vs (X.Kz j G')}

variable {X}

theorem ZL_smul (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (vs : List X.Pl) (a : X.G.Kf) (F : X.Fm j) :
    ZL X u m j vs (a • F) = a • ZL X u m j vs F := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show X.Zop v (u v) (m v) j (ZL X u m j vs (a • F)) = a • X.Zop v (u v) (m v) j (ZL X u m j vs F)
    rw [ih, Zop_smul hL]

theorem TtL_congr (j : ℕ) (i0 i0' : X.Pl → ℕ) (vs : List X.Pl) (h : ∀ v ∈ vs, i0 v = i0' v) (F : X.Fm j) :
    TtL X j i0 vs F = TtL X j i0' vs F := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show X.Tt v (i0 v) j (TtL X j i0 vs F) = X.Tt v (i0' v) j (TtL X j i0' vs F)
    rw [h v (by simp), ih (fun w hw => h w (by simp [hw]))]

theorem Aof_update (i0 : X.Pl → ℕ) (vs : List X.Pl) (v : X.Pl) (hv : v ∉ vs) (i : ℕ) :
    Aof X (Function.update i0 v i) (v :: vs) = Aof X i0 vs + (if i = 0 then (X.alEven v : ℝ) else 0) := by
  unfold Aof
  have hs : (if i = 0 then (X.alEven v : ℝ) else 0) =
      ∑ w, if w = v ∧ i = 0 then (X.alEven w : ℝ) else 0 := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : w = v
  · subst hw
    simp [hv]
  · simp [hw, Function.update_apply]

theorem Zop_gen (hfr : IsFractionRing X.G.O X.G.Kf) (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ)
    (hj : j < X.mm) (hu : ∀ l ∈ Icc 1 X.mm, X.vEqK (u l) 0)
    (hc0 : ∀ l ≤ X.G.P.r, X.vGeK (X.cl v m (j + 1) l) 0)
    (hcr : X.vGeK (X.cl v m (j + 1) X.G.P.r) (X.alEven v)) (vs : List X.Pl) (hv : v ∉ vs) :
    ∀ T ∈ Submodule.span X.G.O (Gen X j vs), X.Zop v u m (j + 1) T ∈ Submodule.span X.G.O (Gen X j (v :: vs)) := by
  intro T hT
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, i0, G', hG', hr, h0, ha, rfl⟩ := hx
    rw [Zop_smul hL]
    unfold Sys.Zop
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun l hl => ?_
    rw [Finset.mem_range] at hl
    apply Submodule.subset_span
    have hupd : Function.update i0 v (X.G.P.r - l) v = X.G.P.r - l := by simp
    have hTt : TtL X (j + 1) (Function.update i0 v (X.G.P.r - l)) (v :: vs) (X.Kz j G') =
        X.Tt v (X.G.P.r - l) (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G')) := by
      show X.Tt v (Function.update i0 v (X.G.P.r - l) v) (j + 1)
          (TtL X (j + 1) (Function.update i0 v (X.G.P.r - l)) vs (X.Kz j G')) = _
      rw [hupd, TtL_congr (j + 1) _ i0 vs (fun w hw => Function.update_of_ne (ne_of_mem_of_not_mem hw hv) _ _)]
    refine ⟨a * ((-1) ^ l * X.cl v m (j + 1) l * (∏ l' ∈ Icc 1 (j + 1), u l') ^ (-((X.G.P.r - l : ℕ) : ℤ))),
      Function.update i0 v (X.G.P.r - l), G', hG', ?_, ?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = v
      · subst hw
        rw [hupd]
        omega
      · rw [Function.update_of_ne hw]
        exact hr w
    · intro w hw
      rw [List.mem_cons, not_or] at hw
      rw [Function.update_of_ne hw.1]
      exact h0 w hw.2
    · rw [Aof_update i0 vs v hv (X.G.P.r - l)]
      have hU : X.vEqK (∏ l' ∈ Icc 1 (j + 1), u l') 0 :=
        vEqK_prod_units X hfr (eO_pos X v) _ _ fun l' hl' => hu l' (by
          rw [Finset.mem_Icc] at hl' ⊢
          omega)
      have hUk := (vEqK_zpow X hfr hU (-((X.G.P.r - l : ℕ) : ℤ))).1
      have hcl : X.vGeK (X.cl v m (j + 1) l) (if X.G.P.r - l = 0 then (X.alEven v : ℝ) else 0) := by
        split_ifs with h
        · have hlr : l = X.G.P.r := by omega
          rw [hlr]
          exact hcr
        · exact hc0 l (by omega)
      have key := vGeK_mul X hfr ha (vGeK_mul X hfr (vGeK_mul X hfr (vGeK_negOnePow X l) hcl) hUk)
      convert key using 1
      ring
    · rw [hTt]
      simp only [Sys.Ttu, smul_smul]
  | zero =>
    rw [Zop_zero hL]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Zop_add hL]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul X.G.Kf a x, Zop_smul hL, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

theorem ZL_mem (hfr : IsFractionRing X.G.O X.G.Kf) (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (hj : j < X.mm)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v)) (vs : List X.Pl) (hnd : vs.Nodup)
    (G : X.Fm j) (hG : G ∈ X.Int j) :
    ZL X u m (j + 1) vs (X.Kz j G) ∈ Submodule.span X.G.O (Gen X j vs) := by
  induction vs with
  | nil =>
    apply Submodule.subset_span
    refine ⟨1, fun _ => 0, G, hG, fun _ => Nat.zero_le _, fun _ _ => rfl, ?_, ?_⟩
    · have h0 : Aof X (fun _ => 0) [] = 0 := by
        simp [Aof]
      rw [h0]
      exact vGeK_one X
    · rw [one_smul]
      rfl
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    exact Zop_gen hfr hL v (u v) (m v) j hj (hu v) (hc0 v) (hcr v) vs hnd.1 _ (ih hnd.2)

theorem ZL_bound {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hL : LinD X) (hF : FormB X Y) (hE : EntCondition X Y)
    (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (hj : j < X.mm)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v)) (vs : List X.Pl) (hnd : vs.Nodup)
    (gP : X.Pl → ℝ) (h1 : ∀ v ∈ vs, gP v ≤ X.gv v (j + 1)) (h2 : ∀ v, v ∉ vs → Y.LowAt j v (gP v))
    (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (ZL X u m (j + 1) vs (X.Kz j G)) (∑ v, gP v - X.dG j) := by
  have key : ∀ T ∈ Submodule.span X.G.O (Gen X j vs), X.vGe (j + 1) T (∑ v, gP v - X.dG j) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, i0, G', hG', hr, h0, ha, rfl⟩ := hx
      obtain ⟨gQ, hgQ⟩ : ∃ f : X.Pl → ℝ,
          f = fun v => gP v - (if v ∈ vs ∧ i0 v = 0 then (X.alEven v : ℝ) else 0) := ⟨_, rfl⟩
      have hP : ∀ v, PlaceB X Y j v (i0 v) (gQ v) := by
        intro v
        by_cases hv : v ∈ vs
        · by_cases hi : i0 v = 0
          · left
            refine ⟨hi, Or.inr ?_⟩
            simp only [hgQ, hv, hi, and_self, if_true]
            linarith [h1 v hv]
          · right
            refine ⟨by omega, hr v, ?_⟩
            simp only [hgQ, hv, hi, and_false, if_false, sub_zero]
            exact h1 v hv
        · left
          refine ⟨h0 v hv, Or.inl ?_⟩
          simp only [hgQ, hv, false_and, if_false, sub_zero]
          exact h2 v hv
      have hTt := form_of_place hF hE j hj i0 vs gQ hnd hr h0 hP G' hG'
      have hsum : ∑ v, gQ v = ∑ v, gP v - Aof X i0 vs := by
        simp only [hgQ, Aof, Finset.sum_sub_distrib]
      have hs := vGe_smul X hfr ha hTt
      rw [hsum] at hs
      convert hs using 1
      ring
    | zero => exact vGe_zero X _ _
    | add x y _ _ hx hy => exact vGe_add X hx hy
    | smul a x _ hx =>
      have ha : X.vGeK (algebraMap X.G.O X.G.Kf a) 0 := (vGeK_zero_iff X).2 ((mem_intK X).2 ⟨a, rfl⟩)
      have hs := vGe_smul X hfr ha hx
      rw [zero_add, algebraMap_smul] at hs
      exact hs
  exact key _ (ZL_mem hfr hL u m j hj hu hc0 hcr vs hnd G hG)

end Formalism.MainNotions.FormalGroupSystem.Pf
