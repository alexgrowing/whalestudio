import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef.StepCheck

section Fun

variable {O : Type} [CommRing O]

def posMin (O : Type) [CommRing O] : InvFun O where
  toFun n B := max 0 ((InvFun.minVal O).toFun n B)
  inv n m r hr B := by rw [(InvFun.minVal O).inv n m r hr]
  zero B := by rw [(InvFun.minVal O).zero, max_self]

theorem minVal_nat_mul (n k : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    (InvFun.minVal O).toFun n (fun a b => k * B a b) = k * (InvFun.minVal O).toFun n B := by
  change sInf {x | (∃ y, (k : ℝ) * B y y = x) ∧ x ≠ k * B 0 0} = k * sInf {x | (∃ y, B y y = x) ∧ x ≠ B 0 0}
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_mul]
    convert Real.sInf_empty
    exact Set.eq_empty_of_forall_notMem fun x ⟨⟨_, h⟩, h'⟩ => h' h.symm
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [← smul_eq_mul (k : ℝ) (sInf _), ← Real.sInf_smul_of_nonneg hk'.le]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨y, rfl⟩, h⟩
      exact ⟨B y y, ⟨⟨y, rfl⟩, fun e => h (by rw [e])⟩, rfl⟩
    · rintro ⟨z, ⟨⟨y, rfl⟩, h⟩, rfl⟩
      exact ⟨⟨y, rfl⟩, fun e => h (mul_left_cancel₀ hk'.ne' e)⟩

theorem isTame_posMin : IsTame (posMin O) := by
  refine ⟨fun n k B => ?_, fun n B => le_max_left _ _⟩
  change max 0 _ = (k : ℝ) * max 0 _
  rw [minVal_nat_mul, mul_max_of_nonneg _ _ k.cast_nonneg, mul_zero]

theorem not_isTame_minVal : ¬ IsTame (InvFun.minVal ℤ) := fun h => by
  have h1 := h.2 1 (fun a _ => if a = 0 then 0 else -1)
  have : {x : ℝ | (∃ y : Fin 1 → ℤ, (if y = 0 then (0 : ℝ) else -1) = x) ∧
      x ≠ (if (0 : Fin 1 → ℤ) = 0 then (0 : ℝ) else -1)} = {-1} := by
    ext x
    simp only [Set.mem_setOf_eq, if_true, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨y, rfl⟩, h⟩
      by_cases hy : y = 0
      · simp [hy] at h
      · simp [hy]
    · rintro rfl
      exact ⟨⟨1, by simp⟩, by norm_num⟩
  change 0 ≤ sInf _ at h1
  rw [this, csInf_singleton] at h1
  norm_num at h1

theorem comb_eval (a b : ℕ) (ψ φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) :
    (comb a ψ b φ).eval X B = a * ψ.eval X B + b * φ.eval X B := rfl

theorem isTame_comb {ψ φ : InvFun O} (h : IsTame ψ) (h' : IsTame φ) (a b : ℕ) : IsTame (comb a ψ b φ) :=
  ⟨fun n k B => by simp only [comb, h.1, h'.1]; ring,
    fun n B => add_nonneg (mul_nonneg a.cast_nonneg (h.2 n B)) (mul_nonneg b.cast_nonneg (h'.2 n B))⟩

theorem resInt_eval [Module.Finite ℤ O] (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Finite ℤ X] (B : X → X → ℝ) : (resInt O φ).eval X B = φ.eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(resInt O φ).eval_eq hr]
  exact φ.eval_comp (r := r.toAddMonoidHom.toIntLinearMap) hr B

theorem isTame_resInt [Module.Finite ℤ O] {φ : InvFun ℤ} (h : IsTame φ) : IsTame (resInt O φ) :=
  ⟨fun _ _ _ => h.1 _ _ _, fun _ _ => h.2 _ _⟩

variable {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem posMin_eval {B : X → X → ℝ} (hB : ∀ y, 0 ≤ B y y) : (posMin O).eval X B = (InvFun.minVal O).eval X B :=
  max_eq_right (Real.sInf_nonneg fun _ ⟨⟨_, h⟩, _⟩ => h ▸ hB _)

variable {bar : O → O} {φ φ' : InvFun O}

theorem isCone_congr (h : ∀ B : X → X → ℝ, (∀ y, 0 ≤ B y y) → φ.eval X B = φ'.eval X B) {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ) : IsCone bar φ' γ := by
  have hZ : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → φ'.evalZ β = φ.evalZ β := fun β hβ =>
    (h _ fun y => by exact_mod_cast hβ y).symm
  refine ⟨hγ.mem, hγ.nonneg, hγ.basis, fun c hc => ?_, ?_⟩
  · rw [← h _ fun y => Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hγ.nonneg i y), hγ.linear c hc]
    simp only [hZ _ (hγ.nonneg _)]
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
    exact ⟨N, ℓ, hN, fun i => by rw [hZ _ (hγ.nonneg i), h1], fun β hβ hp => by rw [hZ _ hp]; exact h2 β hβ hp,
      fun β hβ hp he => h3 β hβ hp (by rw [← hZ _ hp]; exact he)⟩

theorem isPolFanOn_congr (h : ∀ B : X → X → ℝ, (∀ y, 0 ≤ B y y) → φ.eval X B = φ'.eval X B)
    (hφ : IsPolFanOn bar φ X) : IsPolFanOn bar φ' X := by
  have h' : ∀ B : X → X → ℝ, (∀ y, 0 ≤ B y y) → φ'.eval X B = φ.eval X B := fun B hB => (h B hB).symm
  have hR : ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∀ y, 0 ≤ B y y) → evalR φ' B = evalR φ B := fun B hB => h' _ hB
  have hZ : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → φ'.evalZ β = φ.evalZ β := fun β hβ =>
    h' _ fun y => by exact_mod_cast hβ y
  refine ⟨fun B hB t ht => ?_, fun B hB B' hB' => ?_, fun β hβ hp => ?_, fun β hβ hp h0 => ?_,
    fun m m' γ s hγ => isCone_congr h (hφ.face m m' γ s (isCone_congr h' hγ)), fun B hB => ?_, ?_⟩
  · rw [hR _ (nonneg_of_mem_psdCone hB), hR _ (nonneg_of_mem_psdCone (smul_mem_psdCone hB ht)), hφ.homog B hB t ht]
  · rw [hR _ (nonneg_of_mem_psdCone hB), hR _ (nonneg_of_mem_psdCone hB'),
      hR _ fun y => add_nonneg (nonneg_of_mem_psdCone hB y) (nonneg_of_mem_psdCone hB' y)]
    exact hφ.superadd B hB B' hB'
  · rw [hZ _ hp]; exact hφ.integral β hβ hp
  · rw [hZ _ hp]; exact hφ.pos β hβ hp h0
  · obtain ⟨m, γ, c, h1, h2⟩ := hφ.cover B hB
    exact ⟨m, γ, c, isCone_congr h h1, h2⟩
  · obtain ⟨S, hS, h1⟩ := hφ.finite
    exact ⟨S, hS, fun m γ hγ => h1 m γ (isCone_congr h' hγ)⟩

theorem isPolFan_posMin_one : IsPolFan id 1 (posMin ℤ) ∧ IsTame (posMin ℤ) :=
  ⟨fun X _ _ _ _ hX => isPolFanOn_congr (fun _ hB => (posMin_eval hB).symm) (isPolFan_minVal_one X hX), isTame_posMin⟩

end Fun

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem isTwInv_resInt (φ : InvFun ℤ) : IsTwInv H (resInt (𝓞 E) φ) := fun σ _ n B =>
  φ.eval_comp (r := (AddMonoidHom.compLeft σ.toAddEquiv.toAddMonoidHom (Fin n)).toIntLinearMap)
    (fun a => ⟨fun i => σ.symm (a i), funext fun i => σ.apply_symm_apply (a i)⟩) B

theorem isTwInv_posMin : IsTwInv H (posMin (𝓞 E)) := fun σ _ n B => by
  change max 0 (sInf _) = max 0 (sInf _)
  congr 2
  ext x
  have e : (fun i : Fin n => σ ((0 : Fin n → 𝓞 E) i)) = 0 := funext fun i => map_zero σ
  simp only [Set.mem_setOf_eq, e]
  refine and_congr_left' ⟨fun ⟨y, h⟩ => ⟨_, h⟩, fun ⟨y, h⟩ => ⟨fun i => σ.symm (y i), ?_⟩⟩
  simpa using h

theorem isPosFn_posMin : IsPosFn H (posMin (𝓞 E)) := fun X _ _ _ _ be _ hp => by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  rw [InvFun.evalZ, InvFun.eval_eq _ hr]
  refine lt_max_of_lt_right (lt_of_lt_of_le one_pos (le_csInf ?_ ?_))
  · obtain ⟨y, hy⟩ := exists_ne (0 : X)
    obtain ⟨z, rfl⟩ := hr y
    exact ⟨_, ⟨z, rfl⟩, by simpa using (hp _ hy).ne'⟩
  · rintro x ⟨⟨y, rfl⟩, h⟩
    have h0 : r y ≠ 0 := fun e => h (by simp [e])
    change (1 : ℝ) ≤ (be (r y) (r y) : ℝ)
    exact_mod_cast (show (1 : ℤ) ≤ _ from hp _ h0)

theorem refines_zero (φs : InvFun ℤ) (𝒩 : Finset ℕ) : Refines H 0 φs 𝒩 (posMin (𝓞 E)) := by
  refine ⟨isPolFan_zero, noSelfInt_zero, isTwInv_posMin H, isPosFn_posMin H, isTame_posMin, fun X _ _ _ _ hX m γ hγ => ?_⟩
  have : Subsingleton X := Module.finrank_zero_iff.1 (Nat.le_zero.1 hX)
  have : IsEmpty (Fin m) := ⟨fun i => hγ.linearIndependent.ne_zero i (Subsingleton.elim _ _)⟩
  exact ⟨fun c _ => by simp [InvFun.eval_of_subsingleton], fun N _ y => ⟨0, isEmptyElim⟩⟩

variable {H} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem hasCones_mono {Cn Cn' : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop}
    (h : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] m γ, Cn X m γ → Cn' X m γ)
    {Z : Model Xo c β} (hZ : HasCones Cn Z) : HasCones Cn' Z := fun z => by
  obtain ⟨R, _, _, _, ξ, t, μ, P, m, γ, h1, h2, h3, h4, h5, h6, h7⟩ := hZ z
  exact ⟨R, _, _, _, ξ, t, μ, P, m, γ, h1, h2, h3, h4, h5, h _ _ _ h6, h7⟩

end CM

section Cones

variable {R : Type} [CommRing R] [IsDomain R] {Dg : DegPre R}

theorem formAt_id_of_isMonomial {ϖ : R} {be : LinearMap.BilinForm ℤ Dg.X} (h : IsMonomial Dg ![ϖ] ![be]) :
    FormAt Dg (RingHom.id R) ϖ be := fun y => by
  obtain ⟨u, n, h1, h2⟩ := h y
  refine ⟨_, n 0, h2, h1 0, ?_⟩
  simpa using associated_unit_mul_left _ _ u.isUnit

theorem inCone_of_isMonomial {m : ℕ} {t : Fin m → R} {γ : Fin m → LinearMap.BilinForm ℤ Dg.X}
    (hs : ∀ i y z, γ i y z = γ i z y) (h : IsMonomial Dg t γ) : InCone Dg γ := by
  intro W _ _ _ hW ϖ hϖ f be hbe hf
  have := hW.1
  classical
  let c : Fin m → ℕ := fun i => if h0 : f (t i) = 0 then 0 else
    (IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ).choose
  have hc : ∀ i, f (t i) ≠ 0 → Associated (f (t i)) (ϖ ^ c i) := fun i h0 => by
    simp only [c, dif_neg h0]
    exact (IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ).choose_spec
  have diag : ∀ y, be y y = ∑ i, (c i : ℤ) * γ i y y := fun y => by
    obtain ⟨r, n, hr, hn, ha⟩ := hf y
    obtain ⟨u, k, hk, rfl⟩ := h.coord hr
    have hne : f (u * ∏ i, t i ^ k i) ≠ 0 := ha.ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero)
    rw [map_mul, map_prod] at ha hne
    have h1 : Associated (∏ i, f (t i ^ k i)) (∏ i, ϖ ^ (c i * k i)) := Associated.prod _ _ _ fun i _ => by
      rcases Nat.eq_zero_or_pos (k i) with h0 | h0
      · simp [h0]
      · have : f (t i ^ k i) ≠ 0 := fun e => hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) e, mul_zero])
        rw [map_pow] at this ⊢
        rw [pow_mul]
        exact (hc i fun e => this (by rw [e, zero_pow h0.ne'])).pow_pow
    rw [Finset.prod_pow_eq_pow_sum] at h1
    have h2 : Associated (ϖ ^ n) (ϖ ^ ∑ i, c i * k i) :=
      ha.symm.trans ((associated_unit_mul_left _ _ (u.isUnit.map f)).trans h1)
    have h3 : n = ∑ i, c i * k i := by
      have := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 h2
      rw [hϖ.addVal_pow, hϖ.addVal_pow] at this
      exact_mod_cast this
    rw [hn, h3]
    simp only [hk]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨fun i => c i, fun i => (c i).cast_nonneg, LinearMap.ext₂ fun a b => ?_⟩
  have e : be a b = ∑ i, (c i : ℤ) * γ i a b := by
    have h1 := diag (a + b)
    simp only [map_add, LinearMap.add_apply, diag a, diag b, hbe b a, mul_add, Finset.sum_add_distrib, hs _ b a] at h1
    linarith
  simp [LinearMap.sum_apply, e]

theorem eq_zero_of_inCone_empty [IsLocalRing R] (hR : CDvr R) {ϖ : R} (hϖ : Irreducible ϖ)
    {be : LinearMap.BilinForm ℤ Dg.X} (hs : ∀ y z, be y z = be z y) (h : IsMonomial Dg ![ϖ] ![be])
    (hc : InCone Dg (![] : Fin 0 → _)) : be = 0 := by
  obtain ⟨c, -, e⟩ := hc R hR ϖ hϖ (RingHom.id R) be hs (formAt_id_of_isMonomial h)
  refine LinearMap.ext₂ fun a b => ?_
  have := LinearMap.congr_fun₂ e a b
  simpa using this

end Cones

end GlobalTheory.TorRef.StepCheck
