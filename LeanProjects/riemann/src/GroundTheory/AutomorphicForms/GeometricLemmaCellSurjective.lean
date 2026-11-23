import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter

section Proportional

variable {G : Type*} [Group G] {W E : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup E]
  [Module ℂ E]

theorem exists_nonneg_avgOver (π : W →ₗ[ℂ] E) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f)
    (x : G) (c₀ : E) (hterm : ∀ k ∈ K, ∃ r : ℝ, 0 ≤ r ∧ π (f (x * k)) = (r : ℂ) • c₀) :
    ∃ r : ℝ, 0 ≤ r ∧ π (avgOver K f x) = (r : ℂ) • c₀ ∧
      (∀ r₀ : ℝ, 0 < r₀ → π (f x) = (r₀ : ℂ) • c₀ → c₀ ≠ 0 → 0 < r) := by
  classical
  set S := (rightStab f).subgroupOf K
  have : S.FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  choose rr hrr using fun q : K ⧸ S => hterm _ (Quotient.out q).2
  have hidx : (0 : ℝ) < (S.index : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hf)
  refine ⟨(S.index : ℝ)⁻¹ * ∑ q, rr q, ?_, ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.2 hidx.le) (Finset.sum_nonneg fun q _ => (hrr q).1)
  · rw [avgOver_eq_sum, map_smul, map_sum]
    simp_rw [fun q : K ⧸ S => (hrr q).2]
    rw [← Finset.sum_smul, smul_smul]
    congr 1
    push_cast
    rfl
  · intro r₀ hr₀ hfx hc₀
    set q₀ : K ⧸ S := QuotientGroup.mk 1
    have hq₀ : (Quotient.out q₀ : K) ∈ S := by
      have h := QuotientGroup.out_eq' q₀
      rw [QuotientGroup.eq] at h
      simpa using h
    have hst : ((Quotient.out q₀ : K) : G) ∈ rightStab f := Subgroup.mem_subgroupOf.1 hq₀
    have hval : f (x * ((Quotient.out q₀ : K) : G)) = f x := (mem_rightStab.1 hst) x
    have heq : ((rr q₀ : ℝ) : ℂ) • c₀ = ((r₀ : ℝ) : ℂ) • c₀ := by
      rw [← (hrr q₀).2, hval, hfx]
    have hr : rr q₀ = r₀ := by
      have := smul_left_injective ℂ hc₀ heq
      exact_mod_cast this
    have hsum : 0 < ∑ q, rr q :=
      lt_of_lt_of_le (hr ▸ hr₀) (Finset.single_le_sum (fun q _ => (hrr q).1) (Finset.mem_univ q₀))
    exact mul_pos (inv_pos.2 hidx) hsum

end Proportional

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem permGL_mem_integralGL (w : Equiv.Perm (Fin n)) : permGL F w ∈ integralGL F n := by
  rw [mem_integralGL_iff F n]
  constructor
  · intro i j
    rw [permGL_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro i j
    rw [← map_inv, permGL_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

section Bump

variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

open Classical in

def bumpFun (x : GL (Fin n) F) (K : Subgroup (GL (Fin n) F)) (v : W) : GL (Fin n) F → W :=
  fun g => if h : ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k then
    inflateTwist F n β σ h.choose v else 0

variable {σ}

theorem bumpFun_apply {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)} {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ K.map (MulAut.conj x).toMonoidHom →
      inflateTwist F n β σ p v = v)
    (p : blockUpper F n β) {k : GL (Fin n) F} (hk : k ∈ K) :
    bumpFun σ x K v ((p : GL (Fin n) F) * x * k) = inflateTwist F n β σ p v := by
  unfold bumpFun
  have h : ∃ p' : blockUpper F n β, ∃ k' ∈ K,
      (p : GL (Fin n) F) * x * k = (p' : GL (Fin n) F) * x * k' := ⟨p, k, hk, rfl⟩
  rw [dif_pos h]
  obtain ⟨k', hk', he⟩ := h.choose_spec
  set p' := h.choose
  have hmem : ((p'⁻¹ * p : blockUpper F n β) : GL (Fin n) F) ∈
      K.map (MulAut.conj x).toMonoidHom := by
    refine ⟨k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), ?_⟩
    show x * (k' * k⁻¹) * x⁻¹ = (p' : GL (Fin n) F)⁻¹ * p
    have : (p : GL (Fin n) F) = p' * x * k' * k⁻¹ * x⁻¹ := by
      rw [← he]
      group
    rw [this]
    group
  calc inflateTwist F n β σ p' v
      = inflateTwist F n β σ p' (inflateTwist F n β σ (p'⁻¹ * p) v) := by rw [hv _ hmem]
    _ = inflateTwist F n β σ p v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem bumpFun_eq_zero {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)} {v : W}
    {g : GL (Fin n) F}
    (hg : ¬ ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k) :
    bumpFun σ x K v g = 0 := by
  unfold bumpFun
  rw [dif_neg hg]

theorem exists_of_bumpFun_ne_zero {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)} {v : W}
    {g : GL (Fin n) F} (hg : bumpFun σ x K v g ≠ 0) :
    ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k := by
  by_contra h
  exact hg (bumpFun_eq_zero h)

theorem bumpFun_mem {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)}
    (hK : IsOpen (K : Set (GL (Fin n) F))) {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ K.map (MulAut.conj x).toMonoidHom →
      inflateTwist F n β σ p v = v) :
    bumpFun σ x K v ∈ parabolicIndSpace F n β σ := by
  refine (mem_parabolicIndSpace σ).2 ⟨fun p₀ g => ?_, K, hK, fun k' hk' g => ?_⟩
  · by_cases h : ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k
    · obtain ⟨p, k, hk, rfl⟩ := h
      have e : (p₀ : GL (Fin n) F) * ((p : GL (Fin n) F) * x * k) =
          ((p₀ * p : blockUpper F n β) : GL (Fin n) F) * x * k := by
        simp only [Subgroup.coe_mul]
        group
      rw [e, bumpFun_apply hv _ hk, bumpFun_apply hv _ hk, ← inflateTwist_apply, map_mul,
        Module.End.mul_apply]
    · have h' : ¬ ∃ p : blockUpper F n β, ∃ k ∈ K,
          (p₀ : GL (Fin n) F) * g = (p : GL (Fin n) F) * x * k := by
        rintro ⟨p, k, hk, he⟩
        refine h ⟨p₀⁻¹ * p, k, hk, ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc g = (p₀ : GL (Fin n) F)⁻¹ * ((p₀ : GL (Fin n) F) * g) := by group
          _ = _ := by rw [he]; group
      rw [bumpFun_eq_zero h', bumpFun_eq_zero h, map_zero, smul_zero]
  · by_cases h : ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k
    · obtain ⟨p, k, hk, rfl⟩ := h
      rw [show (p : GL (Fin n) F) * x * k * k' = (p : GL (Fin n) F) * x * (k * k') by group,
        bumpFun_apply hv _ hk, bumpFun_apply hv _ (K.mul_mem hk hk')]
    · have h' : ¬ ∃ p : blockUpper F n β, ∃ k ∈ K,
          g * k' = (p : GL (Fin n) F) * x * k := by
        rintro ⟨p, k, hk, he⟩
        refine h ⟨p, k * k'⁻¹, K.mul_mem hk (K.inv_mem hk'), ?_⟩
        rw [← mul_assoc, ← he]
        group
      rw [bumpFun_eq_zero h', bumpFun_eq_zero h]

end Bump

section LeviProjLemmas

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}

theorem leviProj_mem_blockUpper_comp {x : GL (Fin n) F} (hxQ : x ∈ blockUpper F n γ)
    (hxP : x ∈ blockUpper F n (β ∘ w)) :
    ((leviProj F n γ ⟨x, hxQ⟩ : levi F n γ) : GL (Fin n) F) ∈ blockUpper F n (β ∘ w) := by
  intro i j hij
  show ((leviProj F n γ ⟨x, hxQ⟩ : levi F n γ) : GL (Fin n) F) i j = 0
  rw [leviProj_apply]
  split_ifs
  · exact hxP hij
  · rfl

end LeviProjLemmas

section CellBump

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

theorem permGL_conj_mem_congruenceSubgroup {J : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ congruenceSubgroup F n J) :
    permGL F w * k * (permGL F w)⁻¹ ∈ congruenceSubgroup F n J :=
  conj_mem_congruenceSubgroup F n (permGL_mem_integralGL w) hk

theorem permGL_inv_conj_mem_congruenceSubgroup {J : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ congruenceSubgroup F n J) :
    (permGL F w)⁻¹ * k * permGL F w ∈ congruenceSubgroup F n J := by
  have := conj_mem_congruenceSubgroup F n ((integralGL F n).inv_mem (permGL_mem_integralGL w)) hk
  simpa using this

variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
include hYo hCY

theorem exists_level_near_permGL (J : ℕ) :
    ∃ J' ≥ J, ∀ k ∈ congruenceSubgroup F n J', permGL F w * k ∈ Y ∧
      (permGL F w * k ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ) →
      ∃ p ∈ blockUpper F n β, p ∈ congruenceSubgroup F n J ∧
        ∃ q ∈ blockUpper F n γ, q ∈ congruenceSubgroup F n J ∧ permGL F w * k = p * permGL F w * q) := by
  set C := doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)
  have hCl : IsLocallyClosed C := ⟨Y, closure C, hYo, isClosed_closure, by rw [inter_comm, hCY]⟩
  have hw : permGL F w ∈ C := mem_doubleCoset_self _ _ _
  have hwY : permGL F w ∈ Y := by
    have : permGL F w ∈ closure C ∩ Y := by rw [hCY]; exact hw
    exact this.2
  have hKJ : (congruenceSubgroup F n J : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    (isOpen_congruenceSubgroup F n J).mem_nhds (congruenceSubgroup F n J).one_mem
  obtain ⟨V, hV, hVC⟩ := exists_nhds_inter_doubleCoset_subset (Measures.isClosed_blockUpper F n β)
    (Measures.isClosed_blockUpper F n γ) hCl hw hKJ hKJ
  have hVY : V ∩ Y ∈ 𝓝 (permGL F w) := Filter.inter_mem hV (hYo.mem_nhds hwY)
  have h1 : (fun k => permGL F w * k) ⁻¹' (V ∩ Y) ∈ 𝓝 (1 : GL (Fin n) F) := by
    apply (continuous_const_mul (permGL F w)).continuousAt.preimage_mem_nhds
    simpa using hVY
  obtain ⟨J₁, -, hJ₁⟩ := (hasBasis_nhds_one F n).mem_iff.1 h1
  refine ⟨max J J₁, le_max_left _ _, fun k hk => ?_⟩
  have hk₁ : k ∈ congruenceSubgroup F n J₁ := congruenceSubgroup_antitone F n (le_max_right _ _) hk
  have hkV := hJ₁ hk₁
  refine ⟨hkV.2, fun hkC => ?_⟩
  obtain ⟨p, hp, hpJ, q, hq, hqJ, he⟩ := hVC _ hkV.1 hkC
  exact ⟨p, hp, hpJ, q, hq, hqJ, he⟩

end CellBump

section CellBump2

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
include hYo hCY hYP

theorem exists_bump_permGL (J : ℕ) {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ congruenceSubgroup F n J →
      inflateTwist F n β σ p v = v) :
    ∃ f : parabolicIndSpace F n β σ, f ∈ supportedIn σ Y ∧
      (f : GL (Fin n) F → W) (permGL F w) = v ∧
      ∀ y ∈ blockUpper F n γ, (f : GL (Fin n) F → W) (permGL F w * y) ≠ 0 →
        ∃ x ∈ blockUpper F n γ, ∃ hx : x ∈ blockUpper F n (β ∘ w),
          ∃ q ∈ blockUpper F n γ, q ∈ congruenceSubgroup F n J ∧ y = x * q ∧
            (f : GL (Fin n) F → W) (permGL F w * y) = cellRep β w σ ⟨x, hx⟩ v := by
  obtain ⟨J', hJJ', hnear⟩ := exists_level_near_permGL hYo hCY J
  set KJ' := congruenceSubgroup F n J'
  have hv' : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ KJ'.map (MulAut.conj (permGL F w)).toMonoidHom →
      inflateTwist F n β σ p v = v := by
    rintro p ⟨k, hk, hpk⟩
    apply hv
    rw [← hpk]
    exact congruenceSubgroup_antitone F n hJJ' (permGL_conj_mem_congruenceSubgroup hk)
  have hmem := bumpFun_mem (σ := σ) (isOpen_congruenceSubgroup F n J') hv'
  refine ⟨⟨bumpFun σ (permGL F w) KJ' v, hmem⟩, fun g hg => ?_, ?_, fun y hy hfy => ?_⟩
  · by_contra hne
    obtain ⟨p, k, hk, rfl⟩ := exists_of_bumpFun_ne_zero hne
    apply hg
    rw [mul_assoc]
    exact hYP _ p.2 _ (hnear k hk).1
  · show bumpFun σ (permGL F w) KJ' v (permGL F w) = v
    have := bumpFun_apply (σ := σ) hv' 1 KJ'.one_mem
    simpa using this
  · obtain ⟨p, k, hk, he⟩ := exists_of_bumpFun_ne_zero hfy
    have hkC : permGL F w * k ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ) := by
      refine mem_doubleCoset.2 ⟨(p : GL (Fin n) F)⁻¹, (blockUpper F n β).inv_mem p.2, y, hy, ?_⟩
      calc permGL F w * k = (p : GL (Fin n) F)⁻¹ * ((p : GL (Fin n) F) * permGL F w * k) := by group
        _ = _ := by rw [← he]; group
    obtain ⟨p₁, hp₁, hp₁J, q₁, hq₁, hq₁J, he₁⟩ := (hnear k hk).2 hkC
    have hxw : permGL F w * (y * q₁⁻¹) * (permGL F w)⁻¹ = (p : GL (Fin n) F) * p₁ := by
      calc permGL F w * (y * q₁⁻¹) * (permGL F w)⁻¹
          = (permGL F w * y) * q₁⁻¹ * (permGL F w)⁻¹ := by group
        _ = (p : GL (Fin n) F) * (permGL F w * k) * q₁⁻¹ * (permGL F w)⁻¹ := by rw [he]; group
        _ = _ := by rw [he₁]; group
    have hxP : y * q₁⁻¹ ∈ blockUpper F n (β ∘ w) :=
      (conj_permGL_mem_blockUpper_iff w).1 (by rw [hxw]; exact (blockUpper F n β).mul_mem p.2 hp₁)
    refine ⟨y * q₁⁻¹, (blockUpper F n γ).mul_mem hy ((blockUpper F n γ).inv_mem hq₁), hxP, q₁, hq₁,
      hq₁J, by group, ?_⟩
    show bumpFun σ (permGL F w) KJ' v (permGL F w * y) = _
    rw [he, bumpFun_apply hv' p hk, cellRep_apply]
    have hpc : permConj F β w ⟨y * q₁⁻¹, hxP⟩ = p * ⟨p₁, hp₁⟩ := Subtype.ext (by
      rw [coe_permConj, hxw]
      rfl)
    rw [hpc, map_mul, Module.End.mul_apply, hv ⟨p₁, hp₁⟩ hp₁J]

end CellBump2

section CellBump3

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYP hYQ

theorem exists_cellJacquet_bump (J : ℕ) {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ congruenceSubgroup F n J →
      inflateTwist F n β σ p v = v) :
    ∃ f : parabolicIndSpace F n β σ, ∃ _ : f ∈ supportedIn σ Y,
      (∀ m ∈ levi F n γ, cellJacquet γ w σ f m ≠ 0 →
        ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
          m = b * k) ∧
      (∀ m, ∀ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
        cellJacquet γ w σ f (m * k) = cellJacquet γ w σ f m) ∧
      ∃ c : ℂ, c ≠ 0 ∧ cellJacquet γ w σ f 1 = c • Representation.Coinvariants.mk _ v := by
  obtain ⟨f', hf'Y, hf'w, hcl⟩ := exists_bump_permGL hYo hCY hYP J hv
  set QK := blockUpper F n γ ⊓ congruenceSubgroup F n J
  have hQK : IsCompact (QK : Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_inf]
    exact (isCompact_congruenceSubgroup F n J).inter_left (Measures.isClosed_blockUpper F n γ)
  obtain ⟨-, U, hU, hUf⟩ := (mem_parabolicIndSpace σ).1 f'.2
  have hfin : AvgFinite QK (f' : GL (Fin n) F → W) :=
    avgFinite_of_isOpen hQK hU (fun g hg => mem_rightStab.2 fun x => hUf g hg x)
  have hI : avgOver QK (f' : GL (Fin n) F → W) ∈ parabolicIndSpace F n β σ := by
    refine avgOver_mem hfin fun k _ => ?_
    have := (parabolicInd F n β σ k f').2
    convert this using 1
    funext y
    rw [coe_indRep_apply]
  set F'' : parabolicIndSpace F n β σ := ⟨avgOver QK (f' : GL (Fin n) F → W), hI⟩
  have hY : F'' ∈ supportedIn σ Y := fun g hg => avgOver_eq_zero_of_forall fun k hk =>
    hf'Y _ fun hgk => hg (by
      have := hYQ _ hgk _ ((blockUpper F n γ).inv_mem (Subgroup.mem_inf.1 hk).1)
      simpa using this)
  set mk := Representation.Coinvariants.mk (cellRepA β γ w σ)

  have hterm : ∀ u ∈ unipotentRadical F n γ, ∀ k ∈ QK, ∃ r : ℝ, 0 ≤ r ∧
      mk ((f' : GL (Fin n) F → W) (permGL F w * u * k)) = (r : ℂ) • mk v := by
    intro u hu k hk
    by_cases h0 : (f' : GL (Fin n) F → W) (permGL F w * u * k) = 0
    · exact ⟨0, le_rfl, by rw [h0, map_zero]; simp⟩
    · have hkQ := (Subgroup.mem_inf.1 hk).1
      have hkJ := (Subgroup.mem_inf.1 hk).2
      have huQ := unipotentRadical_le_blockUpper hu
      have hy : u * k ∈ blockUpper F n γ := (blockUpper F n γ).mul_mem huQ hkQ
      rw [mul_assoc] at h0
      obtain ⟨x, hxQ, hxP, q, hqQ, hqJ, hyxq, hval⟩ := hcl (u * k) hy h0
      refine ⟨1, zero_le_one, ?_⟩
      rw [mul_assoc, hval]
      set b := leviProj F n γ ⟨x, hxQ⟩
      have hbP : (b : GL (Fin n) F) ∈ blockUpper F n (β ∘ w) := leviProj_mem_blockUpper_comp hxQ hxP
      have hbeq : (b : GL (Fin n) F) = (leviProj F n γ ⟨k, hkQ⟩ : GL (Fin n) F) *
          (leviProj F n γ ⟨q⁻¹, (blockUpper F n γ).inv_mem hqQ⟩ : GL (Fin n) F) := by
        have hx : x = u * k * q⁻¹ := by rw [hyxq]; group
        have e1 : (⟨x, hxQ⟩ : blockUpper F n γ) =
            ⟨u, huQ⟩ * ⟨k, hkQ⟩ * ⟨q⁻¹, (blockUpper F n γ).inv_mem hqQ⟩ := Subtype.ext hx
        show ((leviProj F n γ ⟨x, hxQ⟩ : levi F n γ) : GL (Fin n) F) = _
        rw [e1, map_mul, map_mul, (mem_unipotentRadical_iff_leviProj (p := ⟨u, huQ⟩)).1 hu,
          one_mul]
        rfl
      have hbJ : (b : GL (Fin n) F) ∈ congruenceSubgroup F n J := by
        rw [hbeq]
        exact (congruenceSubgroup F n J).mul_mem
          (leviProj_mem_congruenceSubgroup' (p := ⟨k, hkQ⟩) hkJ)
          (leviProj_mem_congruenceSubgroup' (p := ⟨q⁻¹, (blockUpper F n γ).inv_mem hqQ⟩)
            ((congruenceSubgroup F n J).inv_mem hqJ))
      have haN : x * (b : GL (Fin n) F)⁻¹ ∈ unipotentRadical F n γ := by
        rw [show x * (b : GL (Fin n) F)⁻¹ = ((⟨x, hxQ⟩ * (leviIncl b)⁻¹ : blockUpper F n γ) :
          GL (Fin n) F) from rfl, mem_unipotentRadical_iff_leviProj, map_mul, map_inv,
          leviProj_leviIncl, mul_inv_cancel]
      have haP : x * (b : GL (Fin n) F)⁻¹ ∈ blockUpper F n (β ∘ w) :=
        (blockUpper F n (β ∘ w)).mul_mem hxP ((blockUpper F n (β ∘ w)).inv_mem hbP)
      have hsplit : (⟨x, hxP⟩ : blockUpper F n (β ∘ w)) = ⟨x * (b : GL (Fin n) F)⁻¹, haP⟩ * ⟨b, hbP⟩ :=
        Subtype.ext (by simp)
      have hbv : cellRep β w σ ⟨b, hbP⟩ v = v := by
        rw [cellRep_apply]
        apply hv
        rw [coe_permConj]
        exact permGL_conj_mem_congruenceSubgroup hbJ
      rw [hsplit, map_mul, Module.End.mul_apply, hbv, Complex.ofReal_one, one_smul]
      exact Representation.Coinvariants.mk_self_apply (cellRepA β γ w σ)
        ⟨x * (b : GL (Fin n) F)⁻¹, haN, haP⟩ v
  have hinner : ∀ u ∈ unipotentRadical F n γ, ∃ r : ℝ, 0 ≤ r ∧
      mk (avgOver QK (f' : GL (Fin n) F → W) (permGL F w * u)) = (r : ℂ) • mk v ∧
        (u = 1 → mk v ≠ 0 → 0 < r) := by
    intro u hu
    obtain ⟨r, hr0, hr, hpos⟩ := exists_nonneg_avgOver mk hfin (permGL F w * u) (mk v)
      (fun k hk => hterm u hu k hk)
    refine ⟨r, hr0, hr, fun hu1 hc => hpos 1 one_pos ?_ hc⟩
    subst hu1
    rw [mul_one, hf'w]
    simp
  refine ⟨F'', hY, ?_, ?_, ?_⟩
  ·
    intro m hm hne
    obtain ⟨e, he⟩ := exists_cellSupp σ hYo hCY hY hm
    have hK := isCellCompact_unipotentCompactG (F := F) (γ := γ) e
    rw [cellJacquet_eq_cellEv σ hYo hCY hY hm hK he] at hne
    unfold cellEv at hne
    obtain ⟨u, hu, hu0⟩ : ∃ u ∈ unipotentCompactG (F := F) γ e, cellFun w σ F'' m (1 * u) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (by rw [avgOver_eq_zero_of_forall hall, map_zero, smul_zero])
    have huN := hK.1 hu
    obtain ⟨k, hk, hk0⟩ : ∃ k ∈ QK, (f' : GL (Fin n) F → W) (permGL F w * (1 * u) * m * k) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu0 (avgOver_eq_zero_of_forall hall)
    have hkQ := (Subgroup.mem_inf.1 hk).1
    have hkJ := (Subgroup.mem_inf.1 hk).2
    have huQ := unipotentRadical_le_blockUpper huN
    have hmQ := levi_le_blockUpper hm
    have hy : u * m * k ∈ blockUpper F n γ :=
      (blockUpper F n γ).mul_mem ((blockUpper F n γ).mul_mem huQ hmQ) hkQ
    obtain ⟨x, hxQ, hxP, q, hqQ, hqJ, hyxq, -⟩ := hcl (u * m * k) hy (by
      rw [show permGL F w * (u * m * k) = permGL F w * (1 * u) * m * k by group]; exact hk0)
    refine ⟨leviProj F n γ ⟨x, hxQ⟩, ⟨(leviProj F n γ ⟨x, hxQ⟩).2,
      leviProj_mem_blockUpper_comp hxQ hxP⟩,
      (leviProj F n γ ⟨q, hqQ⟩ : GL (Fin n) F) * (leviProj F n γ ⟨k, hkQ⟩ : GL (Fin n) F)⁻¹,
      ⟨(levi F n γ).mul_mem (leviProj F n γ ⟨q, hqQ⟩).2
        ((levi F n γ).inv_mem (leviProj F n γ ⟨k, hkQ⟩).2),
      (congruenceSubgroup F n J).mul_mem (leviProj_mem_congruenceSubgroup' (p := ⟨q, hqQ⟩) hqJ)
        ((congruenceSubgroup F n J).inv_mem (leviProj_mem_congruenceSubgroup' (p := ⟨k, hkQ⟩) hkJ))⟩,
      ?_⟩
    have e1 : (⟨u * m * k, hy⟩ : blockUpper F n γ) = ⟨u, huQ⟩ * ⟨m, hmQ⟩ * ⟨k, hkQ⟩ := rfl
    have e2 : (⟨u * m * k, hy⟩ : blockUpper F n γ) = ⟨x, hxQ⟩ * ⟨q, hqQ⟩ := Subtype.ext hyxq
    have h3 := congrArg (fun z => ((leviProj F n γ z : levi F n γ) : GL (Fin n) F)) (e1.symm.trans e2)
    simp only [map_mul, (mem_unipotentRadical_iff_leviProj (p := ⟨u, huQ⟩)).1 huN, one_mul,
      leviProj_of_mem_levi hm, Subgroup.coe_mul] at h3
    calc m = m * (leviProj F n γ ⟨k, hkQ⟩ : GL (Fin n) F) *
          (leviProj F n γ ⟨k, hkQ⟩ : GL (Fin n) F)⁻¹ := by group
      _ = _ := by rw [h3]; group
  ·
    intro m k hk
    have hkQK : k ∈ QK := ⟨levi_le_blockUpper (Subgroup.mem_inf.1 hk).1, (Subgroup.mem_inf.1 hk).2⟩
    have : ∀ K, cellEv γ w σ F'' (m * k) K = cellEv γ w σ F'' m K := by
      intro K
      unfold cellEv cellFun
      congr 3
      funext y
      show avgOver QK (f' : GL (Fin n) F → W) (permGL F w * y * (m * k)) =
        avgOver QK (f' : GL (Fin n) F → W) (permGL F w * y * m)
      rw [← mul_assoc, avgOver_mul_right hfin hkQK]
    unfold cellJacquet
    simp only [this]
  ·
    obtain ⟨e, he⟩ := exists_cellSupp σ hYo hCY hY (levi F n γ).one_mem
    have hK := isCellCompact_unipotentCompactG (F := F) (γ := γ) e
    rw [cellJacquet_eq_cellEv σ hYo hCY hY (levi F n γ).one_mem hK he]
    unfold cellEv
    have hval : ∀ k ∈ unipotentCompactG (F := F) γ e, ∃ r : ℝ, 0 ≤ r ∧
        mk (cellFun w σ F'' 1 (1 * k)) = (r : ℂ) • mk v := by
      intro k hk
      obtain ⟨r, hr0, hr, -⟩ := hinner k (hK.1 hk)
      refine ⟨r, hr0, ?_⟩
      rw [← hr]
      show mk (avgOver QK (f' : GL (Fin n) F → W) (permGL F w * (1 * k) * 1)) = _
      rw [one_mul, mul_one]
    obtain ⟨r', hr'0, hr', hpos'⟩ := exists_nonneg_avgOver mk
      (avgFinite_cellFun σ F'' 1 hK.2.1) 1 (mk v) hval
    rw [hr', smul_smul]
    by_cases hc : mk v = 0
    · exact ⟨1, one_ne_zero, by rw [hc, smul_zero, smul_zero]⟩
    · obtain ⟨r₁, hr₁0, hr₁, hpos₁⟩ := hinner 1 (unipotentRadical F n γ).one_mem
      have hr₁pos := hpos₁ rfl hc
      have hr'pos : 0 < r' := hpos' r₁ hr₁pos (by
        rw [← hr₁]
        show mk (avgOver QK (f' : GL (Fin n) F → W) (permGL F w * 1 * 1)) = _
        rw [mul_one]) hc
      refine ⟨((cellNorm F β γ w (unipotentCompactG γ e) : ℝ) : ℂ) * (r' : ℂ), ?_, rfl⟩
      have h1 : ((cellNorm F β γ w (unipotentCompactG γ e) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (cellNorm_pos (w := w) (β := β) hK).ne'
      have h2 : ((r' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr'pos.ne'
      exact mul_ne_zero h1 h2

end CellBump3

section Range

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYQ

theorem cellJacquetMap_parabolicInd (f : supportedIn σ Y) (m : levi F n γ) :
    cellJacquetMap γ w σ hYo hCY ⟨parabolicInd F n β σ m f,
      supportedIn_le_comap γ hYQ (levi_le_blockUpper m.2) f.2⟩ =
      indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) m (cellJacquetMap γ w σ hYo hCY f) := by
  apply Subtype.ext
  funext x
  rw [coe_indRep_apply, coe_cellJacquetMap_apply, coe_cellJacquetMap_apply]
  exact cellJacquet_parabolicInd σ f m x

theorem indRep_mem_range_cellJacquetMap (m : levi F n γ)
    {ψ : indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ)}
    (hψ : ψ ∈ LinearMap.range (cellJacquetMap γ w σ hYo hCY)) :
    indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) m ψ ∈
      LinearMap.range (cellJacquetMap γ w σ hYo hCY) := by
  obtain ⟨f, rfl⟩ := hψ
  exact ⟨_, cellJacquetMap_parabolicInd hYo hCY hYQ f m⟩

variable (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
include hYP

theorem exists_bump_mem_range (J : ℕ) {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ congruenceSubgroup F n J →
      inflateTwist F n β σ p v = v)
    {s : GL (Fin n) F} (hs : s ∈ levi F n γ ⊓ integralGL F n) :
    ∃ χ ∈ LinearMap.range (cellJacquetMap γ w σ hYo hCY),
      (∀ m : levi F n γ, (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m ≠ 0 →
        ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
          (m : GL (Fin n) F) = b * s * k) ∧
      (∀ k : levi F n γ, (k : GL (Fin n) F) ∈ congruenceSubgroup F n J →
        (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (⟨s, hs.1⟩ * k) = Representation.Coinvariants.mk _ v) := by
  obtain ⟨f, hf, hP1, hP2, c, hc, hP3⟩ := exists_cellJacquet_bump hYo hCY hYP hYQ J hv
  set sM : levi F n γ := ⟨s, hs.1⟩
  refine ⟨c⁻¹ • indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) sM⁻¹
    (cellJacquetMap γ w σ hYo hCY ⟨f, hf⟩), Submodule.smul_mem _ _
      (indRep_mem_range_cellJacquetMap hYo hCY hYQ _ ⟨_, rfl⟩), ?_, ?_⟩
  · intro m hm
    have hm' : cellJacquet γ w σ f ((m : GL (Fin n) F) * s⁻¹) ≠ 0 := by
      intro h0
      apply hm
      show c⁻¹ • (cellJacquetMap γ w σ hYo hCY ⟨f, hf⟩ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (m * sM⁻¹) = 0
      rw [coe_cellJacquetMap_apply]
      show c⁻¹ • cellJacquet γ w σ f ((m : GL (Fin n) F) * s⁻¹) = 0
      rw [h0, smul_zero]
    obtain ⟨b, hb, k, hk, he⟩ := hP1 _ ((levi F n γ).mul_mem m.2 ((levi F n γ).inv_mem hs.1)) hm'
    refine ⟨b, hb, s⁻¹ * k * s, ⟨?_, ?_⟩, ?_⟩
    · exact (levi F n γ).mul_mem ((levi F n γ).mul_mem ((levi F n γ).inv_mem hs.1)
        (Subgroup.mem_inf.1 hk).1) hs.1
    · have := conj_mem_congruenceSubgroup F n ((integralGL F n).inv_mem hs.2)
        (Subgroup.mem_inf.1 hk).2
      simpa using this
    · calc (m : GL (Fin n) F) = ((m : GL (Fin n) F) * s⁻¹) * s := by group
        _ = _ := by rw [he]; group
  · intro k hk
    show c⁻¹ • (cellJacquetMap γ w σ hYo hCY ⟨f, hf⟩ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (sM * k * sM⁻¹) = _
    rw [coe_cellJacquetMap_apply]
    have hkk : s * (k : GL (Fin n) F) * s⁻¹ ∈ levi F n γ ⊓ congruenceSubgroup F n J :=
      ⟨(levi F n γ).mul_mem ((levi F n γ).mul_mem hs.1 k.2) ((levi F n γ).inv_mem hs.1),
        conj_mem_congruenceSubgroup F n hs.2 hk⟩
    have := hP2 1 _ hkk
    rw [one_mul] at this
    show c⁻¹ • cellJacquet γ w σ f (s * (k : GL (Fin n) F) * s⁻¹) = _
    rw [this, hP3, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Range

section Surjective

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

theorem eq_on_cellDoubleCoset {J : ℕ}
    {ψ₁ ψ₂ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)}
    (h₁ : ψ₁ ∈ indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ))
    (h₂ : ψ₂ ∈ indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ))
    {s : levi F n γ}
    (hs : ∀ k : levi F n γ, (k : GL (Fin n) F) ∈ congruenceSubgroup F n J → ψ₁ (s * k) = ψ₂ (s * k))
    {m : levi F n γ}
    (hm : ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
      (m : GL (Fin n) F) = b * s * k) : ψ₁ m = ψ₂ m := by
  obtain ⟨b, hb, k, hk, he⟩ := hm
  set bM : cellLeviSub F β γ w := ⟨⟨b, hb.1⟩, Subgroup.mem_subgroupOf.2 hb⟩
  set kM : levi F n γ := ⟨k, (Subgroup.mem_inf.1 hk).1⟩
  have hm' : m = (bM : levi F n γ) * (s * kM) := Subtype.ext (by
    rw [he]
    simp only [Subgroup.coe_mul, mul_assoc]
    rfl)
  rw [hm', ((mem_indSpace).1 h₁).1 bM, ((mem_indSpace).1 h₂).1 bM, hs kM (Subgroup.mem_inf.1 hk).2]

variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYP hYQ

theorem cellJacquetMap_surjective (hσ : IsSmooth σ) :
    Function.Surjective (cellJacquetMap γ w σ hYo hCY) := by
  classical
  intro φ
  suffices hφ : φ ∈ LinearMap.range (cellJacquetMap γ w σ hYo hCY) by
    obtain ⟨f, hf⟩ := hφ
    exact ⟨f, hf⟩
  set R := LinearMap.range (cellJacquetMap γ w σ hYo hCY)
  set mk := Representation.Coinvariants.mk (cellRepA β γ w σ)
  obtain ⟨-, K, hKo, hKφ⟩ := (mem_indSpace).1 φ.2
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.1 hKo
  have h1U : (1 : GL (Fin n) F) ∈ U' := by
    have : (1 : levi F n γ) ∈ (K : Set (levi F n γ)) := K.one_mem
    rw [← hU'] at this
    exact this
  obtain ⟨j₀, -, hj₀⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hU'o.mem_nhds h1U)
  have hinv : ∀ J ≥ j₀, ∀ g k : levi F n γ, (k : GL (Fin n) F) ∈ congruenceSubgroup F n J →
      (φ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (g * k) =
        (φ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) g := by
    intro J hJ g k hk
    refine hKφ k ?_ g
    have : k ∈ Subtype.val ⁻¹' U' := hj₀ (congruenceSubgroup_antitone F n hJ hk)
    rw [hU'] at this
    exact this
  obtain ⟨T, hT, hTcov⟩ := exists_finset_levi_eq_mul (F := F) (β := β) (γ := γ) (w := w) j₀

  have hlift : ∀ m : levi F n γ, ∃ v : W, ∃ j : ℕ,
      mk v = (φ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m ∧
      ∀ J ≥ j, ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ congruenceSubgroup F n J →
        inflateTwist F n β σ p v = v := by
    intro m
    obtain ⟨v, hv⟩ := Representation.Coinvariants.mk_surjective _
      ((φ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m)
    obtain ⟨j, hj⟩ := exists_congruence_fixed hσ v
    refine ⟨v, j, hv, fun J hJ p hp => ?_⟩
    have hpj : (p : GL (Fin n) F) ∈ congruenceSubgroup F n j := congruenceSubgroup_antitone F n hJ hp
    rw [inflateTwist_apply, sqrtModular_of_mem_integralGL' (congruenceSubgroup_le F n j hpj),
      one_smul]
    exact hj _ (leviProj_mem_congruenceSubgroup' hpj)
  choose lv lj hlv using hlift
  let jj : GL (Fin n) F → ℕ := fun g => if h : g ∈ levi F n γ then lj ⟨g, h⟩ else 0
  set J := max j₀ (T.sup jj)
  have hJj₀ : j₀ ≤ J := le_max_left _ _

  set K₁ := levi F n γ ⊓ congruenceSubgroup F n j₀
  set L := (congruenceSubgroup F n J).subgroupOf K₁
  have hK₁ : IsCompact (K₁ : Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_inf]
    exact (isCompact_congruenceSubgroup F n j₀).inter_left isClosed_levi
  have hLfin : L.index ≠ 0 :=
    relIndex_ne_zero_of_isCompact_of_isOpen hK₁ (isOpen_congruenceSubgroup F n J)
  have : L.FiniteIndex := ⟨hLfin⟩
  let _ := Fintype.ofFinite (K₁ ⧸ L)
  set Rf : Finset (GL (Fin n) F) := Finset.univ.image fun q : K₁ ⧸ L => ((Quotient.out q : K₁) : GL (Fin n) F)
  have hRf : ∀ r ∈ Rf, r ∈ K₁ := by
    intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    exact (Quotient.out q).2
  have hRfcov : ∀ k ∈ K₁, ∃ r ∈ Rf, ∃ k' ∈ levi F n γ ⊓ congruenceSubgroup F n J, k = r * k' := by
    intro k hk
    set q : K₁ ⧸ L := QuotientGroup.mk ⟨k, hk⟩
    have hq : (Quotient.out q : K₁)⁻¹ * ⟨k, hk⟩ ∈ L := by
      rw [← QuotientGroup.eq]
      exact QuotientGroup.out_eq' q
    refine ⟨(Quotient.out q : K₁), Finset.mem_image_of_mem _ (Finset.mem_univ q),
      ((Quotient.out q : K₁) : GL (Fin n) F)⁻¹ * k, ⟨?_, Subgroup.mem_subgroupOf.1 hq⟩, by group⟩
    exact (levi F n γ).mul_mem ((levi F n γ).inv_mem (Quotient.out q).2.1) hk.1

  have hsmem : ∀ x ∈ T ×ˢ Rf, x.1 * x.2 ∈ levi F n γ ⊓ integralGL F n := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hx
    obtain ⟨ht1, ht2⟩ := hT x.1 h1
    obtain ⟨hr1, hr2⟩ := hRf x.2 h2
    exact ⟨(levi F n γ).mul_mem ht1 hr1,
      (integralGL F n).mul_mem ht2 (congruenceSubgroup_le F n j₀ hr2)⟩
  have hlj : ∀ t (ht : t ∈ T), lj ⟨t, (hT t ht).1⟩ ≤ J := by
    intro t ht
    have : jj t = lj ⟨t, (hT t ht).1⟩ := dif_pos (hT t ht).1
    rw [← this]
    exact (Finset.le_sup ht).trans (le_max_right _ _)

  have hbump : ∀ x, ∀ hx : x ∈ T ×ˢ Rf, ∃ χ ∈ R,
      (∀ m : levi F n γ, (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m ≠ 0 →
        ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
          (m : GL (Fin n) F) = b * (x.1 * x.2) * k) ∧
      (∀ k : levi F n γ, (k : GL (Fin n) F) ∈ congruenceSubgroup F n J →
        (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ))
          (⟨x.1 * x.2, (hsmem x hx).1⟩ * k) =
        (φ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ))
          (⟨x.1 * x.2, (hsmem x hx).1⟩ * k)) := by
    intro x hx
    have ht := (Finset.mem_product.1 hx).1
    have hr := (Finset.mem_product.1 hx).2
    obtain ⟨χ, hχR, hχ1, hχ2⟩ := exists_bump_mem_range hYo hCY hYQ hYP J
      ((hlv ⟨x.1, (hT x.1 ht).1⟩).2 J (hlj x.1 ht)) (hsmem x hx)
    refine ⟨χ, hχR, hχ1, fun k hk => ?_⟩
    rw [hχ2 k hk, (hlv ⟨x.1, (hT x.1 ht).1⟩).1, hinv J hJj₀ _ k hk]
    have e : (⟨x.1 * x.2, (hsmem x hx).1⟩ : levi F n γ) =
        ⟨x.1, (hT x.1 ht).1⟩ * ⟨x.2, (hRf x.2 hr).1⟩ := rfl
    rw [e, hinv j₀ le_rfl _ _ (hRf x.2 hr).2]

  have key : ∀ P' : Finset (GL (Fin n) F × GL (Fin n) F), P' ⊆ T ×ˢ Rf →
      ∀ ψ : indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ),
      (∀ g k : levi F n γ, (k : GL (Fin n) F) ∈ congruenceSubgroup F n J →
        (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (g * k) =
          (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) g) →
      (∀ m : levi F n γ, (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m ≠ 0 →
        ∃ x ∈ P', ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
          (m : GL (Fin n) F) = b * (x.1 * x.2) * k) →
      (∀ x ∈ P', ∀ hx : x.1 * x.2 ∈ levi F n γ,
        (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) ⟨x.1 * x.2, hx⟩ = 0 ∨
        (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) ⟨x.1 * x.2, hx⟩ =
          (φ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) ⟨x.1 * x.2, hx⟩) →
      ψ ∈ R := by
    intro P'
    induction P' using Finset.induction_on with
    | empty =>
      intro _ ψ _ hsupp _
      have : ψ = 0 := Subtype.ext (funext fun m => by
        by_contra h
        obtain ⟨x, hx, -⟩ := hsupp m h
        exact Finset.notMem_empty x hx)
      rw [this]
      exact R.zero_mem
    | insert x P₀ hxP₀ ih =>
      intro hsub ψ hψinv hψsupp hψval
      have hxmem : x ∈ T ×ˢ Rf := hsub (Finset.mem_insert_self x P₀)
      have hsub₀ : P₀ ⊆ T ×ˢ Rf := (Finset.subset_insert x P₀).trans hsub
      set sM : levi F n γ := ⟨x.1 * x.2, (hsmem x hxmem).1⟩
      obtain ⟨χ, hχR, hχ1, hχ2⟩ := hbump x hxmem
      rcases hψval x (Finset.mem_insert_self x P₀) (hsmem x hxmem).1 with h0 | hφv
      ·
        apply ih hsub₀ ψ hψinv _ (fun x' hx' => hψval x' (Finset.mem_insert_of_mem hx'))
        intro m hm
        obtain ⟨x', hx', hrest⟩ := hψsupp m hm
        rcases Finset.mem_insert.1 hx' with rfl | hx'₀
        · exfalso
          apply hm
          have := eq_on_cellDoubleCoset (ψ₁ := (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ))) (ψ₂ := 0) ψ.2
            (indSpace _ _).zero_mem (s := sM) (J := J)
            (fun k hk => by rw [hψinv sM k hk, h0]; rfl) hrest
          exact this
        · exact ⟨x', hx'₀, hrest⟩
      ·
        have hψχ : ψ - χ ∈ R → ψ ∈ R := fun h => by
          have := R.add_mem h hχR
          rwa [sub_add_cancel] at this
        apply hψχ
        have hagree : ∀ m : levi F n γ, (∃ b ∈ cellLeviParabolic F β γ w,
            ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
              (m : GL (Fin n) F) = b * (x.1 * x.2) * k) →
            (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m =
              (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m := by
          intro m hm
          exact eq_on_cellDoubleCoset ψ.2 χ.2 (s := sM) (J := J)
            (fun k hk => by rw [hχ2 k hk, hψinv sM k hk, hinv J hJj₀ sM k hk]; exact hφv) hm
        apply ih hsub₀ (ψ - χ)
        · intro g k hk
          show (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (g * k) - (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (g * k) =
            (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) g - (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) g
          have hχinv : (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (g * k) =
              (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) g := by
            by_cases hg : ∃ b ∈ cellLeviParabolic F β γ w,
                ∃ k' ∈ levi F n γ ⊓ congruenceSubgroup F n J,
                  (g : GL (Fin n) F) = b * (x.1 * x.2) * k'
            · obtain ⟨b, hb, k', hk', he⟩ := hg
              have hgk : ∃ b ∈ cellLeviParabolic F β γ w,
                  ∃ k'' ∈ levi F n γ ⊓ congruenceSubgroup F n J,
                    ((g * k : levi F n γ) : GL (Fin n) F) = b * (x.1 * x.2) * k'' :=
                ⟨b, hb, k' * k, (levi F n γ ⊓ congruenceSubgroup F n J).mul_mem hk' ⟨k.2, hk⟩,
                  by rw [Subgroup.coe_mul, he]; group⟩
              rw [← hagree (g * k) hgk, ← hagree g ⟨b, hb, k', hk', he⟩, hψinv g k hk]
            · have hgk : ¬ ∃ b ∈ cellLeviParabolic F β γ w,
                  ∃ k'' ∈ levi F n γ ⊓ congruenceSubgroup F n J,
                    ((g * k : levi F n γ) : GL (Fin n) F) = b * (x.1 * x.2) * k'' := by
                rintro ⟨b, hb, k'', hk'', he⟩
                refine hg ⟨b, hb, k'' * (k : GL (Fin n) F)⁻¹,
                  (levi F n γ ⊓ congruenceSubgroup F n J).mul_mem hk''
                    ((levi F n γ ⊓ congruenceSubgroup F n J).inv_mem ⟨k.2, hk⟩), ?_⟩
                calc (g : GL (Fin n) F) = ((g * k : levi F n γ) : GL (Fin n) F) *
                      (k : GL (Fin n) F)⁻¹ := by simp
                  _ = _ := by rw [he]; group
              have e1 : (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (g * k) = 0 := by
                by_contra h
                exact hgk (hχ1 _ h)
              have e2 : (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) g = 0 := by
                by_contra h
                exact hg (hχ1 _ h)
              rw [e1, e2]
          rw [hψinv g k hk, hχinv]
        · intro m hm
          have hm' : (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m -
              (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m ≠ 0 := hm
          by_cases hD : ∃ b ∈ cellLeviParabolic F β γ w,
              ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J, (m : GL (Fin n) F) = b * (x.1 * x.2) * k
          · exact absurd (by rw [hagree m hD, sub_self]) hm'
          · have hχm : (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m = 0 := by
              by_contra h
              exact hD (hχ1 m h)
            rw [hχm, sub_zero] at hm'
            obtain ⟨x', hx', hrest⟩ := hψsupp m hm'
            rcases Finset.mem_insert.1 hx' with rfl | hx'₀
            · exact absurd hrest hD
            · exact ⟨x', hx'₀, hrest⟩
        · intro x' hx' hx'l
          show (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) ⟨x'.1 * x'.2, hx'l⟩ - (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) ⟨x'.1 * x'.2, hx'l⟩ = 0 ∨
            (ψ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) ⟨x'.1 * x'.2, hx'l⟩ - (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) ⟨x'.1 * x'.2, hx'l⟩ =
              (φ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) ⟨x'.1 * x'.2, hx'l⟩
          by_cases hD : ∃ b ∈ cellLeviParabolic F β γ w,
              ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
                ((⟨x'.1 * x'.2, hx'l⟩ : levi F n γ) : GL (Fin n) F) = b * (x.1 * x.2) * k
          · left
            rw [hagree _ hD, sub_self]
          · have hχm : (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ))
                ⟨x'.1 * x'.2, hx'l⟩ = 0 := by
              by_contra h
              exact hD (hχ1 _ h)
            rw [hχm, sub_zero]
            exact hψval x' (Finset.mem_insert_of_mem hx') hx'l

  apply key (T ×ˢ Rf) subset_rfl φ (fun g k hk => hinv J hJj₀ g k hk)
  · intro m _
    obtain ⟨b, hb, t, ht, k, hk, he⟩ := hTcov m m.2
    have hk₁ : k ∈ K₁ := ⟨(Subgroup.mem_inf.1 hk).1, (Subgroup.mem_inf.1 hk).2⟩
    obtain ⟨r, hr, k', hk', hkr⟩ := hRfcov k hk₁
    refine ⟨(t, r), Finset.mem_product.2 ⟨ht, hr⟩, b, hb, k', hk', ?_⟩
    rw [he, hkr]
    group
  · intro x _ hx
    exact Or.inr rfl

end Surjective

end Parabolic

end GroundTheory.Automorphic
