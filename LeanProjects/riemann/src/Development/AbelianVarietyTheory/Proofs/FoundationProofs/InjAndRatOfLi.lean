import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic

set_option autoImplicit false

noncomputable section

open Formalism.IndefR.Bridge Formalism.L2.DIV NumberField GlobalTheory.PresBasic

namespace GlobalTheory.TraceIncl

section Scalar

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}

theorem exists_int_smul (f : V →ₛₗ[σ] W) (hinj : Function.Injective f)
    (hs : ∀ x y (c : ℂ), f x = c • f y → y = 0 ∨ ∃ a, σ a = c) {x y : V} {c : ℂˣ} (hc : IsOfFinOrder c)
    (h : f x = (c : ℂ) • f y) : ∃ a : 𝓞 K, x = (a : K) • y := by
  rcases hs x y c h with rfl | ⟨a, ha⟩
  · exact ⟨0, hinj (by rw [h]; simp)⟩
  · obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
    have h1 : a ^ n = 1 := σ.injective (by rw [map_pow, ha, ← Units.val_pow_eq_pow_val, e, Units.val_one, map_one])
    refine ⟨⟨a, IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)⟩, hinj ?_⟩
    rw [h, map_smulₛₗ, ← ha]
    rfl

theorem inj_and_rat_of_li (f : V →ₛₗ[σ] W)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent ℂ fun k => f (b k)) :
    Function.Injective f ∧ ∀ x y (c : ℂ), f x = c • f y → y = 0 ∨ ∃ a, σ a = c := by
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    by_contra h0
    have := (hli 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0
    exact this hx
  refine ⟨hinj, fun x y c h => ?_⟩
  by_cases hy : y = 0
  · exact Or.inl hy
  have hy' : f y ≠ 0 := fun h0 => hy (hinj (by rw [h0, map_zero]))
  by_cases hl : LinearIndependent K ![y, x]
  · have h2 : LinearIndependent ℂ ![f y, f x] := by
      convert hli 2 _ hl using 1
      funext k
      fin_cases k <;> rfl
    exact absurd h.symm ((LinearIndependent.pair_iff' hy').1 h2 c)
  · rw [LinearIndependent.pair_iff' hy] at hl
    push Not at hl
    obtain ⟨a, rfl⟩ := hl
    rw [map_smulₛₗ] at h
    exact Or.inr ⟨a, smul_left_injective ℂ hy' h⟩

end Scalar

variable {G Γ W K X : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] [AddCommGroup X] [Module ℂ X] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ) (k : G → W →ₗ[ℂ] X)

theorem coef_rat (x y : S.V) (c : ℂ) (h : P.coef x = c • P.coef y) : y = 0 ∨ ∃ a, σ a = c := by
  by_cases hy : y = 0
  · exact Or.inl hy
  obtain ⟨j, hj⟩ : ∃ j, S.bV.repr y j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hy (S.bV.repr.injective (by ext j; simp [hn j]))
  have e := congrArg (fun w => (bW P).repr w j) h
  simp only [map_smul, Finsupp.smul_apply, repr_coef, smul_eq_mul] at e
  refine Or.inr ⟨S.bV.repr x j / S.bV.repr y j, ?_⟩
  rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero σ).2 hj)]

theorem card_stab (γ : Γ) (y : G) (j : J) : Nat.card (stab ι J (ι γ * y * j)) = Nat.card (stab ι J y) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj γ⁻¹).toEquiv fun δ => ?_)
  rw [mem_stab, mem_stab]
  have e : (ι γ * y * j)⁻¹ * ι δ * (ι γ * y * j) = (j : G)⁻¹ * (y⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * y) * j := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right j.2, J.mul_mem_cancel_left (J.inv_mem j.2)]

theorem sum_translate (κ : G) (h1 : ∀ j ∈ J, κ * j * κ⁻¹ ∈ J) (h2 : ∀ j ∈ J, κ⁻¹ * j * κ ∈ J) (Φ : G → X)
    (hΦ : ∀ γ h (j : J), Φ (ι γ * h * j) = Φ h) :
    ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • Φ (P.y c * κ) = ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • Φ (P.y c) := by
  have hinj : Function.Injective fun c => P.decC (P.y c * κ) := by
    intro c c' e
    have e1 := P.dec_spec (P.y c * κ)
    have e2 := P.dec_spec (P.y c' * κ)
    simp only at e
    rw [← e] at e2
    generalize P.decC (P.y c * κ) = d at e1 e2
    generalize P.decG (P.y c * κ) = γ at e1
    generalize P.decK (P.y c * κ) = j at e1
    generalize P.decG (P.y c' * κ) = γ' at e2
    generalize P.decK (P.y c' * κ) = j' at e2
    refine (P.reps (P.y c')).unique ⟨γ' * γ⁻¹, ⟨_, h1 _ (j⁻¹ * j').2⟩, ?_⟩ ⟨1, 1, by simp⟩
    rw [eq_mul_inv_of_mul_eq e1, eq_mul_inv_of_mul_eq e2]
    simp [mul_assoc]
  refine Fintype.sum_bijective _ (Finite.injective_iff_bijective.1 hinj) _ _ fun c => ?_
  have e1 := P.dec_spec (P.y c * κ)
  have e2 : stab ι J (P.y c * κ) = stab ι J (P.y c) := by
    ext δ
    rw [mem_stab, mem_stab]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · convert h1 _ h using 1
      group
    · convert h2 _ h using 1
      group
  rw [← e2]
  conv_lhs => rw [e1, card_stab, hΦ]

def clSum : S.Forms →ₛₗ[σ] X where
  toFun f := ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • k (P.y c) (P.extL f (P.y c))
  map_add' f f' := by simp [Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [map_smulₛₗ, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _

theorem clSum_apply (f : S.Forms) :
    clSum P k f = ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • k (P.y c) (P.coef ((f : S.Cl → S.V) c)) :=
  Finset.sum_congr rfl fun c _ => by rw [ClassPres.extL_apply, ext_y]

structure KernelLaws (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) {J : Subgroup G} (χ : J →* ℂˣ) (k : G → W →ₗ[ℂ] X) : Prop where
  aut : ∀ γ h w, k (ι γ * h) (ρ γ w) = k h w
  typ : ∀ h (j : J) w, k (h * j) w = (((χ j)⁻¹ : ℂˣ) : ℂ) • k h w

variable {k}

theorem KernelLaws.dec (hk : KernelLaws ι ρ χ k) (γ : Γ) (h : G) (j : J) (w : W) :
    (χ j : ℂ) • k (ι γ * h * j) (ρ γ w) = k h w := by
  rw [hk.typ, hk.aut, smul_smul, Units.mul_inv, one_smul]

theorem KernelLaws.form (hk : KernelLaws ι ρ χ k) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) (γ : Γ) (h : G) (j : J) :
    k (ι γ * h * j) (F (ι γ * h * j)) = k h (F h) := by
  rw [hF γ h j, map_smul, hk.dec]

theorem clSum_avgForm (hk : KernelLaws ι ρ χ k) (c : S.Cl) (x : S.V) :
    clSum P k (avgForm S c x) = k (P.y c) (P.coef x) := by
  classical
  rw [clSum_apply, Finset.sum_eq_single c]
  · have hg : ∀ g : S.Gam c, k (P.y c) (P.coef (S.ρ c g x)) = k (P.y c) (P.coef x) := fun g => by
      have := hk.dec (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g)) (P.coef x)
      rwa [stabK_spec, ← map_smul, ← P.coef_act] at this
    simp only [avgForm, Pi.single_eq_same, map_sum, hg, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_congr (P.stabI c).toEquiv, Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  · intro c' _ hc
    simp [avgForm, Pi.single_eq_of_ne hc]
  · simp

theorem clSum_act (hk : KernelLaws ι ρ χ k) {Q : Subgroup G} {ch : Q →* ℂˣ} {G0 : Type} [Group G0]
    {act : Representation K G0 S.Forms} (T : ActTie ι P Q ch act) (hJ : J ≤ Q) (a : G0 → X →ₗ[ℂ] X)
    (ha : ∀ (q : Q) h w, a (T.red q) (k (h * q) w) = (((ch q)⁻¹ : ℂˣ) : ℂ) • k h w) (g : G0) (f : S.Forms) :
    clSum P k (act g f) = a g (clSum P k f) := by
  obtain ⟨q, rfl⟩ := T.red_surj g
  have hn : ∀ (q : Q), ∀ j ∈ J, (q : G) * j * (q : G)⁻¹ ∈ J := fun q j hj =>
    (T.red_ker (q * ⟨j, hJ hj⟩ * q⁻¹)).1 (by
      rw [map_mul, map_mul, (T.red_ker ⟨j, hJ hj⟩).2 hj, mul_one, ← map_mul, mul_inv_cancel, map_one])
  have key := sum_translate P (q : G) (hn q) (fun j hj => by simpa using hn q⁻¹ j hj)
    (fun h => k h (P.ext f h)) (hk.form (extMem P f))
  change ∑ c, _ • k (P.y c) (P.ext _ (P.y c)) = a _ (∑ c, _ • k (P.y c) (P.ext _ (P.y c)))
  rw [← key, map_sum, T.act_eq _ q rfl]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ha, g0Act, map_smul]

structure LatSys (r : Γ → S.V →ₗ[K] S.V) (L : G → Submodule (𝓞 K) S.V) : Prop where
  coef : ∀ γ x, P.coef (r γ x) = ρ γ (P.coef x)
  move : ∀ γ h (j : J), ∀ x ∈ L h, r γ x ∈ L (ι γ * h * j)
  nab : ∀ c, L (P.y c) = S.Nab c

variable {P} {r : Γ → S.V →ₗ[K] S.V} {L : G → Submodule (𝓞 K) S.V}

theorem LatSys.avg_mem (hL : LatSys P r L) (hχ : ∀ j, IsOfFinOrder (χ j)) {c : S.Cl} {x : S.V} (hx : x ∈ S.Nab c) (c' : S.Cl) :
    (avgForm S c x : S.Cl → S.V) c' ∈ S.Nab c' := by
  classical
  by_cases h : c' = c
  · subst h
    simp only [avgForm, Pi.single_eq_same]
    refine Submodule.sum_mem _ fun g _ => ?_
    have h1 := hL.move (P.stabI c' g : Γ) (P.y c') (stabK ι (P.stabI c' g)) x (hL.nab c' ▸ hx)
    rw [stabK_spec, hL.nab] at h1
    obtain ⟨a, ha⟩ := exists_int_smul P.coef (coef_injective P) (coef_rat P) (hχ _)
      ((P.coef_act c' g x).trans (by rw [← hL.coef]))
    rw [ha]
    have h2 := Submodule.smul_mem _ a h1
    rwa [← algebraMap_smul K a] at h2
  · simp [avgForm, Pi.single_eq_of_ne h]

theorem LatSys.exists_trace (hL : LatSys P r L) (hχ : ∀ j, IsOfFinOrder (χ j)) (hk : KernelLaws ι ρ χ k) {h : G} {x : S.V}
    (hx : x ∈ L h) : ∃ f : S.Forms, (∀ c, (f : S.Cl → S.V) c ∈ S.Nab c) ∧
      ∃ j : J, k h (P.coef x) = (((χ j)⁻¹ : ℂˣ) : ℂ) • clSum P k f := by
  obtain ⟨c, ⟨γ, j, rfl⟩, -⟩ := P.reps h
  have h1 := hL.move γ⁻¹ _ j⁻¹ x hx
  rw [show ι γ⁻¹ * (ι γ * P.y c * j) * (j⁻¹ : J) = P.y c by simp [mul_assoc], hL.nab] at h1
  refine ⟨avgForm S c (r γ⁻¹ x), hL.avg_mem hχ h1, j, ?_⟩
  rw [clSum_avgForm P hk, ← hk.dec γ (P.y c) j, smul_smul, Units.inv_mul, one_smul, hL.coef, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.TraceIncl
