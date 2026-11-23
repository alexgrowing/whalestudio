import Mathlib
import GroundTheory.PAdicHodge.WABridgeCris
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

variable (p) in

def allRad : Subring (𝓣).RobbaTilde := ⨅ ρ : Set.Ioo (0 : ℝ) 1, ((𝓣).ofRad ρ).range

theorem mem_allRad {x : (𝓣).RobbaTilde} :
    x ∈ allRad p ↔ ∀ ρ : Set.Ioo (0 : ℝ) 1, x ∈ ((𝓣).ofRad ρ).range := by
  rw [allRad, Subring.mem_iInf]

theorem mem_range_ofRad_of_le {ρ ρ' : Set.Ioo (0 : ℝ) 1} (h : (ρ' : ℝ) ≤ ρ) {x : (𝓣).RobbaTilde}
    (hx : x ∈ ((𝓣).ofRad ρ).range) : x ∈ ((𝓣).ofRad ρ').range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(𝓣).res h y, (𝓣).ofRad_res h y⟩

theorem tildeFrobSymm_mem_range {τ : Set.Ioo (0 : ℝ) 1} {x : (𝓣).RobbaTilde}
    (hx : x ∈ ((𝓣).ofRad τ).range) :
    (frob ℂ_[p] p).tildeFrobSymm x ∈ ((𝓣).ofRad ((frob ℂ_[p] p).rootRadius τ)).range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨_, ((frob ℂ_[p] p).tildeFrobSymm_ofRad τ y).symm⟩

theorem tildeFrobSymm_mem_allRad {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) :
    (frob ℂ_[p] p).tildeFrobSymm x ∈ allRad p :=
  mem_allRad.2 fun ρ => mem_range_ofRad_of_le (le_rootRadius ρ)
    (tildeFrobSymm_mem_range (mem_allRad.1 hx ρ))

theorem coe_iterate_rootRadius (τ : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    (((frob ℂ_[p] p).rootRadius^[n] τ : Set.Ioo (0 : ℝ) 1) : ℝ) = (τ : ℝ) ^ ((p : ℝ)⁻¹ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', rootRadius_coe, ih, ← Real.rpow_mul τ.2.1.le, pow_succ]

theorem exists_le_iterate_rootRadius (τ ρ : Set.Ioo (0 : ℝ) 1) :
    ∃ n : ℕ, (ρ : ℝ) ≤ (((frob ℂ_[p] p).rootRadius^[n] τ : Set.Ioo (0 : ℝ) 1) : ℝ) := by
  have hL : 0 < -Real.log τ := neg_pos.2 (Real.log_neg τ.2.1 τ.2.2)
  have hR : 0 < -Real.log ρ := neg_pos.2 (Real.log_neg ρ.2.1 ρ.2.2)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hR hL) (inv_p_lt_one (p := p))
  refine ⟨N, ?_⟩
  rw [coe_iterate_rootRadius, Real.rpow_def_of_pos τ.2.1]
  rw [lt_div_iff₀ hL] at hN
  calc (ρ : ℝ) = Real.exp (Real.log ρ) := (Real.exp_log ρ.2.1).symm
    _ ≤ Real.exp (Real.log τ * (p : ℝ)⁻¹ ^ N) := Real.exp_le_exp.2 (by nlinarith)

theorem ofRad_awayToExt (ρ ρ' : Set.Ioo (0 : ℝ) 1) (a : 𝔸) :
    (𝓣).ofRad ρ (awayToExt p ρ a) = (𝓣).ofRad ρ' (awayToExt p ρ' a) := by
  let ρ3 : Set.Ioo (0 : ℝ) 1 := ⟨min ρ ρ', lt_min ρ.2.1 ρ'.2.1, min_lt_of_left_lt ρ.2.2⟩
  rw [← (𝓣).ofRad_res (ρ1 := ρ3) (min_le_left _ _), res_awayToExt,
    ← (𝓣).ofRad_res (ρ1 := ρ3) (min_le_right _ _) (awayToExt p ρ' a), res_awayToExt]

variable (p) in

def ainfTilde : AInf ℂ_[p] p →+* (𝓣).RobbaTilde :=
  ((𝓣).ofRad (rhoMid p)).comp ((awayToExt p (rhoMid p)).comp (algebraMap (AInf ℂ_[p] p) 𝔸))

theorem ainfTilde_eq (ρ : Set.Ioo (0 : ℝ) 1) (a : AInf ℂ_[p] p) :
    ainfTilde p a = (𝓣).ofRad ρ (awayToExt p ρ (algebraMap _ 𝔸 a)) :=
  ofRad_awayToExt _ _ _

theorem ainfTilde_mem_allRad (a : AInf ℂ_[p] p) : ainfTilde p a ∈ allRad p :=
  mem_allRad.2 fun ρ => ⟨_, (ainfTilde_eq ρ a).symm⟩

theorem mem_allRad_of_tildeFrob_eq {m : ℕ} (C : Matrix (Fin m) (Fin m) (𝓣).RobbaTilde)
    (hC : ∀ i j, C i j ∈ allRad p) (y : Fin m → (𝓣).RobbaTilde)
    (hy : ∀ i, (frob ℂ_[p] p).tildeFrob (y i) = ∑ j, C i j * y j) (i : Fin m) :
    y i ∈ allRad p := by
  obtain ⟨ρ₀, h₀⟩ : ∃ ρ₀ : Set.Ioo (0 : ℝ) 1, ∀ j, y j ∈ ((𝓣).ofRad ρ₀).range := by
    have key : ∀ s : Finset (Fin m), ∃ ρ₀ : Set.Ioo (0 : ℝ) 1,
        ∀ j ∈ s, y j ∈ ((𝓣).ofRad ρ₀).range := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨rhoMid p, by simp⟩
      | insert j s hj ih =>
        obtain ⟨ρ₁, h₁⟩ := ih
        obtain ⟨ρ₂, z, hz⟩ := (𝓣).exists_ofRad (y j)
        refine ⟨⟨min ρ₁ ρ₂, lt_min ρ₁.2.1 ρ₂.2.1, min_lt_of_left_lt ρ₁.2.2⟩, fun k hk => ?_⟩
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact mem_range_ofRad_of_le (min_le_right _ _) ⟨z, hz⟩
        · exact mem_range_ofRad_of_le (min_le_left _ _) (h₁ k hk)
    obtain ⟨ρ₀, h⟩ := key Finset.univ
    exact ⟨ρ₀, fun j => h j (Finset.mem_univ j)⟩
  have hstep : ∀ n : ℕ, ∀ j, y j ∈ ((𝓣).ofRad ((frob ℂ_[p] p).rootRadius^[n] ρ₀)).range := by
    intro n
    induction n with
    | zero => exact h₀
    | succ n ih =>
      intro j
      rw [Function.iterate_succ_apply']
      have e : y j = ∑ k, (frob ℂ_[p] p).tildeFrobSymm (C j k) *
          (frob ℂ_[p] p).tildeFrobSymm (y k) := by
        conv_lhs => rw [← (frob ℂ_[p] p).tildeFrobSymm_tildeFrob (y j), hy j, map_sum]
        simp only [map_mul]
      rw [e]
      refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ ?_ (tildeFrobSymm_mem_range (ih k))
      exact mem_allRad.1 (tildeFrobSymm_mem_allRad (hC j k)) _
  refine mem_allRad.2 fun ρ => ?_
  obtain ⟨n, hn⟩ := exists_le_iterate_rootRadius (p := p) ρ₀ ρ
  exact mem_range_ofRad_of_le hn (hstep n i)

def rep {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (ρ : Set.Ioo (0 : ℝ) 1) : (𝓣).RobbaExt ρ :=
  (mem_allRad.1 hx ρ).choose

theorem ofRad_rep {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (ρ : Set.Ioo (0 : ℝ) 1) :
    (𝓣).ofRad ρ (rep hx ρ) = x :=
  (mem_allRad.1 hx ρ).choose_spec

theorem rep_eq {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) {ρ : Set.Ioo (0 : ℝ) 1}
    {y : (𝓣).RobbaExt ρ} (h : (𝓣).ofRad ρ y = x) : rep hx ρ = y :=
  (𝓣).ofRad_injective ρ (by rw [ofRad_rep, h])

theorem res_rep {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1}
    (h : (ρ1 : ℝ) ≤ ρ0) : (𝓣).res h (rep hx ρ0) = rep hx ρ1 :=
  (rep_eq hx (by rw [(𝓣).ofRad_res, ofRad_rep])).symm

def tn {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (r : Set.Ioo (0 : ℝ) 1) : ℝ :=
  (𝓣).extNorm r (topRad r) (rep hx r)

theorem tn_nonneg {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (r : Set.Ioo (0 : ℝ) 1) :
    0 ≤ tn hx r :=
  (𝓣).extNorm_nonneg _ _

theorem extNorm_rep {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) (σ : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioc (0 : ℝ) σ) :
    (𝓣).extNorm σ r (rep hx σ) = tn hx ⟨r, r.2.1, lt_of_le_of_lt r.2.2 σ.2.2⟩ := by
  rw [tn, ← res_rep hx (ρ0 := σ) (ρ1 := ⟨r, r.2.1, lt_of_le_of_lt r.2.2 σ.2.2⟩) r.2.2,
    (𝓣).extNorm_res]
  rfl

theorem coe_powRadius (σ : Set.Ioo (0 : ℝ) 1) :
    (((frob ℂ_[p] p).powRadius σ : Set.Ioo (0 : ℝ) 1) : ℝ) = (σ : ℝ) ^ p := by
  show (σ : ℝ) ^ p ^ (frob ℂ_[p] p).a = _
  rw [frob_a, pow_one]

theorem coe_iterate_powRadius (σ : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    (((frob ℂ_[p] p).powRadius^[k] σ : Set.Ioo (0 : ℝ) 1) : ℝ) = (σ : ℝ) ^ (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', coe_powRadius, ih, ← pow_mul, pow_succ]

theorem iterate_powRadius_rootRadius (c : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    (frob ℂ_[p] p).powRadius^[k] ((frob ℂ_[p] p).rootRadius^[k] c) = c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply',
      (frob ℂ_[p] p).powRadius_rootRadius, ih]

theorem extNorm_awayToExt (ρ : Set.Ioo (0 : ℝ) 1) (r : Set.Ioc (0 : ℝ) ρ) (a : 𝔸) :
    (𝓣).extNorm ρ r (awayToExt p ρ a) = gn ℂ_[p] p r a := by
  rw [awayToExt_apply, extNorm_coe]
  rfl

theorem exists_extNorm_sum_le {σ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) σ) {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (f : ι → (𝓣).RobbaExt σ) :
    ∃ j ∈ s, (𝓣).extNorm σ r (∑ k ∈ s, f k) ≤ (𝓣).extNorm σ r (f j) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, Finset.mem_singleton_self a, by rw [Finset.sum_singleton]⟩
  | cons a s ha hs ih =>
    obtain ⟨j, hj, hjle⟩ := ih
    rw [Finset.sum_cons]
    rcases le_total ((𝓣).extNorm σ r (f a)) ((𝓣).extNorm σ r (f j)) with h | h
    · exact ⟨j, Finset.mem_cons_of_mem hj, ((𝓣).extNorm_add_le _ _ _).trans (max_le h hjle)⟩
    · exact ⟨a, Finset.mem_cons_self a s,
        ((𝓣).extNorm_add_le _ _ _).trans (max_le le_rfl (hjle.trans h))⟩

section Decay

variable {m : ℕ} (C : Matrix (Fin m) (Fin m) (AInf ℂ_[p] p))
  {y : Fin m → (teichLift ℂ_[p] p).RobbaTilde}
  (hy : ∀ i, (frob ℂ_[p] p).tildeFrob (y i) =
    ∑ j, (p : (teichLift ℂ_[p] p).RobbaTilde) * ainfTilde p (C i j) * y j)
  (ha : ∀ i, y i ∈ allRad p)

include hy in

theorem extFrob_rep (i : Fin m) (σ : Set.Ioo (0 : ℝ) 1) :
    (frob ℂ_[p] p).extFrob σ (rep (ha i) σ) = ∑ j, (p : (𝓣).RobbaExt ((frob ℂ_[p] p).powRadius σ)) *
      awayToExt p ((frob ℂ_[p] p).powRadius σ) (algebraMap _ 𝔸 (C i j)) *
        rep (ha j) ((frob ℂ_[p] p).powRadius σ) := by
  apply (𝓣).ofRad_injective
  rw [← (frob ℂ_[p] p).tildeFrob_ofRad, ofRad_rep, hy i, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, map_natCast, ofRad_rep, ← ainfTilde_eq]

include hy in

theorem exists_tn_pow_le (i : Fin m) (r : Set.Ioo (0 : ℝ) 1) :
    ∃ j, tn (ha i) r ^ p ≤ (r : ℝ) ^ p * tn (ha j) ((frob ℂ_[p] p).powRadius r) := by
  set r' := (frob ℂ_[p] p).powRadius r
  have h1 : tn (ha i) r ^ p = (𝓣).extNorm r' (topRad r') ((frob ℂ_[p] p).extFrob r (rep (ha i) r)) := by
    have := (frob ℂ_[p] p).extNorm_extFrob r (topRad r) (rep (ha i) r)
    rw [frob_a, pow_one] at this
    rw [tn, ← this]
    rfl
  obtain ⟨j, -, hj⟩ := exists_extNorm_sum_le (topRad r') (s := Finset.univ) ⟨i, Finset.mem_univ i⟩
    (fun j => (p : (𝓣).RobbaExt r') * awayToExt p r' (algebraMap _ 𝔸 (C i j)) * rep (ha j) r')
  refine ⟨j, ?_⟩
  rw [h1, extFrob_rep C hy ha i r]
  refine hj.trans ?_
  rw [(𝓣).extNorm_mul, (𝓣).extNorm_mul, ← awayToExt_natCast, extNorm_awayToExt, extNorm_awayToExt,
    map_natCast, gn_natCast_p (K := ℂ_[p]) (topRad r').2.1]
  have hr' : ((topRad r' : Set.Ioc (0 : ℝ) r') : ℝ) = (r : ℝ) ^ p := coe_powRadius r
  have hC1 := gn_algebraMap_le_one (K := ℂ_[p]) (p := p) (topRad r').2.1 (rad_lt_one r' (topRad r')).le (C i j)
  have hg0 := gn_nonneg (K := ℂ_[p]) (p := p) (topRad r').2.1 (algebraMap _ 𝔸 (C i j))
  rw [hr'] at hC1 hg0 ⊢
  have hnn := tn_nonneg (ha j) r'
  calc (r : ℝ) ^ p * gn ℂ_[p] p ((r : ℝ) ^ p) (algebraMap _ 𝔸 (C i j)) *
        (𝓣).extNorm r' (topRad r') (rep (ha j) r')
      ≤ (r : ℝ) ^ p * 1 * tn (ha j) r' := by
        have hr0 : (0 : ℝ) ≤ (r : ℝ) ^ p := pow_nonneg r.2.1.le _
        gcongr
        exact le_rfl
    _ = (r : ℝ) ^ p * tn (ha j) r' := by ring

include hy in

theorem exists_tn_pow_pow_le (k : ℕ) : ∀ (i : Fin m) (r : Set.Ioo (0 : ℝ) 1),
    ∃ j, tn (ha i) r ^ (p ^ k) ≤
      (r : ℝ) ^ (k * p ^ k) * tn (ha j) ((frob ℂ_[p] p).powRadius^[k] r) := by
  induction k with
  | zero => intro i r; exact ⟨i, by simp⟩
  | succ k ih =>
    intro i r
    obtain ⟨j₁, h₁⟩ := exists_tn_pow_le C hy ha i r
    obtain ⟨j₂, h₂⟩ := ih j₁ ((frob ℂ_[p] p).powRadius r)
    refine ⟨j₂, ?_⟩
    rw [Function.iterate_succ_apply]
    have hr0 : (0 : ℝ) ≤ r := r.2.1.le
    calc tn (ha i) r ^ (p ^ (k + 1)) = (tn (ha i) r ^ p) ^ (p ^ k) := by rw [pow_succ', pow_mul]
      _ ≤ ((r : ℝ) ^ p * tn (ha j₁) ((frob ℂ_[p] p).powRadius r)) ^ (p ^ k) :=
          pow_le_pow_left₀ (pow_nonneg (tn_nonneg _ _) _) h₁ _
      _ = (r : ℝ) ^ (p * p ^ k) * tn (ha j₁) ((frob ℂ_[p] p).powRadius r) ^ (p ^ k) := by
          rw [mul_pow, ← pow_mul]
      _ ≤ (r : ℝ) ^ (p * p ^ k) * ((((frob ℂ_[p] p).powRadius r : Set.Ioo (0 : ℝ) 1) : ℝ) ^
            (k * p ^ k) * tn (ha j₂) ((frob ℂ_[p] p).powRadius^[k] ((frob ℂ_[p] p).powRadius r))) :=
          mul_le_mul_of_nonneg_left h₂ (pow_nonneg hr0 _)
      _ = (r : ℝ) ^ ((k + 1) * p ^ (k + 1)) *
            tn (ha j₂) ((frob ℂ_[p] p).powRadius^[k] ((frob ℂ_[p] p).powRadius r)) := by
          rw [coe_powRadius, ← pow_mul, ← mul_assoc, ← pow_add]
          congr 2
          ring

end Decay

end WABridge

end GroundTheory.PAdicHodge
