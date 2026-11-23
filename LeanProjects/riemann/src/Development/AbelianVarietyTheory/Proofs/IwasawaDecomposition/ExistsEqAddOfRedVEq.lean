import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Restr

variable (O : Type) [CommRing O] [Module.Finite ℤ O]

def restr (φ : InvFun ℤ) : InvFun O where
  toFun n B := φ.eval (Fin n → O) B
  inv n m r hr B := φ.eval_comp (r := r.restrictScalars ℤ) hr B
  zero B := φ.eval_of_subsingleton B

variable {O} {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem eval_restr [Module.Finite ℤ X] (φ : InvFun ℤ) (B : X → X → ℝ) : (restr O φ).eval X B = φ.eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(restr O φ).eval_eq hr]
  exact φ.eval_comp (r := r.restrictScalars ℤ) hr B

end Restr

section Mean

def redV (M : ℕ) {n : ℕ} (a : Fin n → ℤ) : Fin n → ZMod (M + 1) := fun i => (a i : ZMod (M + 1))

def classMin (M : ℕ) {n : ℕ} (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) (y : Fin n → ZMod (M + 1)) : ℝ :=
  sInf {x | ∃ a : Fin n → ℤ, redV M a = y ∧ B a a = x}

theorem redV_surjective (M n : ℕ) : Function.Surjective (redV M (n := n)) := fun y =>
  ⟨fun i => ((y i).val : ℤ), funext fun i => by simp [redV]⟩

theorem exists_eq_add_of_redV_eq {M n : ℕ} {a a' : Fin n → ℤ} (h : redV M a = redV M a') :
    ∃ d : Fin n → ℤ, a = a' + ((M : ℤ) + 1) • d := by
  have key : ∀ i, ((M : ℤ) + 1) ∣ a i - a' i := fun i => by
    have := congrFun h i
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (a' i) (a i) (M + 1)).1 this.symm
    simpa using h2
  choose d hd using key
  exact ⟨d, funext fun i => by simp [← hd i]⟩

theorem redV_add_smul {M n : ℕ} (a d : Fin n → ℤ) : redV M (a + ((M : ℤ) + 1) • d) = redV M a := by
  funext i
  have h0 : (((M : ℤ) : ZMod (M + 1)) + ((1 : ℤ) : ZMod (M + 1))) = 0 := by
    have := ZMod.natCast_self (M + 1)
    push_cast at this ⊢
    exact this
  simp only [redV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul]
  rw [h0, zero_mul, add_zero]

theorem redV_add {M n : ℕ} (a b : Fin n → ℤ) : redV M (a + b) = redV M a + redV M b := by
  funext i; simp [redV]

def redMap (M : ℕ) {n m : ℕ} (r : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)) :
    (Fin n → ZMod (M + 1)) →+ (Fin m → ZMod (M + 1)) :=
  AddMonoidHom.mk' (fun y => redV M (r (redV_surjective M n y).choose)) fun y y' => by
    have h0 := (redV_surjective M n y).choose_spec
    have h1 := (redV_surjective M n y').choose_spec
    have h2 := (redV_surjective M n (y + y')).choose_spec
    set a := (redV_surjective M n y).choose
    set b := (redV_surjective M n y').choose
    set c := (redV_surjective M n (y + y')).choose
    obtain ⟨d, hd⟩ := exists_eq_add_of_redV_eq (M := M) (a := c) (a' := a + b)
      (by rw [h2, redV_add, h0, h1])
    rw [hd, map_add, map_smul, redV_add_smul, map_add, redV_add]

theorem redMap_redV (M : ℕ) {n m : ℕ} (r : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)) (a : Fin n → ℤ) :
    redMap M r (redV M a) = redV M (r a) := by
  have h0 := (redV_surjective M n (redV M a)).choose_spec
  obtain ⟨d, hd⟩ := exists_eq_add_of_redV_eq h0
  change redV M (r (redV_surjective M n (redV M a)).choose) = _
  rw [hd, map_add, map_smul, redV_add_smul]

theorem redMap_surjective (M : ℕ) {n m : ℕ} {r : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)} (hr : Function.Surjective r) :
    Function.Surjective (redMap M r) := fun y => by
  obtain ⟨b, rfl⟩ := redV_surjective M m y
  obtain ⟨a, rfl⟩ := hr b
  exact ⟨_, redMap_redV M r a⟩

theorem classMin_comp (M : ℕ) {n m : ℕ} {r : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)} (hr : Function.Surjective r)
    (B : (Fin m → ℤ) → (Fin m → ℤ) → ℝ) (y : Fin n → ZMod (M + 1)) :
    classMin M (fun a b => B (r a) (r b)) y = classMin M B (redMap M r y) := by
  unfold classMin
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨r a, (redMap_redV M r a).symm, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := redV_surjective M n y
    rw [redMap_redV] at hb
    obtain ⟨d, hd⟩ := exists_eq_add_of_redV_eq hb
    obtain ⟨e, rfl⟩ := hr d
    refine ⟨a + ((M : ℤ) + 1) • e, redV_add_smul _ _, ?_⟩
    simp only [map_add, map_smul, ← hd]

theorem mean_comp {A A' : Type} [AddCommGroup A] [AddCommGroup A'] [Fintype A] [Fintype A'] (f : A →+ A')
    (hf : Function.Surjective f) (g : A' → ℝ) :
    (Fintype.card A : ℝ)⁻¹ * ∑ y, g (f y) = (Fintype.card A' : ℝ)⁻¹ * ∑ y, g y := by
  classical
  have hfib : ∀ y' : A', (Finset.univ.filter fun y => f y = y').card = (Finset.univ.filter fun y => f y = 0).card := by
    intro y'
    obtain ⟨a, rfl⟩ := hf y'
    refine Finset.card_bij (fun y _ => y - a) (fun y hy => ?_) (fun _ _ _ _ h => sub_left_injective h) fun z hz => ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      simp [hy]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact ⟨z + a, by simp [hz], by simp⟩
  set k := (Finset.univ.filter fun y => f y = 0).card with hk
  have hsum : ∀ g : A' → ℝ, ∑ y, g (f y) = k * ∑ y, g y := fun g => by
    rw [← Finset.sum_fiberwise Finset.univ f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => g y') (fun y hy => by rw [(Finset.mem_filter.1 hy).2]),
      Finset.sum_const, hfib, nsmul_eq_mul]
  have hc : (Fintype.card A : ℝ) = k * Fintype.card A' := by
    simpa using hsum fun _ => 1
  have hA : (Fintype.card A' : ℝ) ≠ 0 := by
    have : Nonempty A' := ⟨0⟩
    exact_mod_cast Fintype.card_ne_zero
  have hA' : (Fintype.card A : ℝ) ≠ 0 := by
    have : Nonempty A := ⟨0⟩
    exact_mod_cast Fintype.card_ne_zero
  have hk0 : (k : ℝ) ≠ 0 := fun h => hA' (by rw [hc, h, zero_mul])
  rw [hsum, hc]
  field_simp

def fineMean (M : ℕ) : InvFun ℤ where
  toFun n B := (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M B y - B 0 0
  inv n m r hr B := by
    have h := mean_comp (redMap M r) (redMap_surjective M hr) (classMin M B)
    have c1 : ∀ k : ℕ, (Fintype.card (Fin k → ZMod (M + 1)) : ℝ) = ((M : ℝ) + 1) ^ k := fun k => by
      simp [ZMod.card]
    rw [c1, c1] at h
    simp only [classMin_comp M hr, map_zero]
    rw [h]
  zero B := by
    have : classMin M B 0 = B 0 0 := by
      unfold classMin
      have : {x | ∃ a : Fin 0 → ℤ, redV M a = 0 ∧ B a a = x} = {B 0 0} := by
        ext x
        constructor
        · rintro ⟨a, -, rfl⟩
          rw [Subsingleton.elim a 0]; rfl
        · rintro rfl
          exact ⟨0, Subsingleton.elim _ _, rfl⟩
      rw [this, csInf_singleton]
    have e : ∀ y : Fin 0 → ZMod (M + 1), classMin M B y = B 0 0 := fun y => by
      rw [Subsingleton.elim y 0]; exact this
    rw [Fintype.sum_unique, e]
    simp

example : (fineMean 1).toFun 1 (fun a b => ((a 0 * b 0 : ℤ) : ℝ)) = 1 / 2 := by
  have h0 : classMin 1 (fun a b : Fin 1 → ℤ => ((a 0 * b 0 : ℤ) : ℝ)) (fun _ => 0) = 0 := by
    refine IsLeast.csInf_eq ⟨⟨0, funext fun i => by simp [redV], by simp⟩, ?_⟩
    rintro x ⟨a, -, rfl⟩
    show (0 : ℝ) ≤ ((a 0 * a 0 : ℤ) : ℝ)
    exact_mod_cast mul_self_nonneg (a 0)
  have h1 : classMin 1 (fun a b : Fin 1 → ℤ => ((a 0 * b 0 : ℤ) : ℝ)) (fun _ => 1) = 1 := by
    refine IsLeast.csInf_eq ⟨⟨1, funext fun i => by simp [redV], by simp⟩, ?_⟩
    rintro x ⟨a, ha, rfl⟩
    have h2 : a 0 ≠ 0 := fun h => by
      have := congrFun ha 0
      simp [redV, h] at this
    have : (1 : ℤ) ≤ a 0 * a 0 := mul_self_pos.2 h2
    show (1 : ℝ) ≤ ((a 0 * a 0 : ℤ) : ℝ)
    exact_mod_cast this
  have hs : ∀ f : (Fin 1 → ZMod (1 + 1)) → ℝ, ∑ y, f y = f (fun _ => 0) + f (fun _ => 1) := fun f => by
    rw [← (Equiv.funUnique (Fin 1) (ZMod (1 + 1))).symm.sum_comp f]
    exact Fin.sum_univ_two _
  show ((((1 : ℕ) : ℝ) + 1) ^ 1)⁻¹ * ∑ y, classMin 1 _ y - _ = _
  rw [hs, h0, h1]
  norm_num

end Mean

section Base

def fineDen (g : ℕ) (𝓜 : Finset ℕ) : ℕ := ∏ M ∈ 𝓜, (M + 1) ^ g

theorem fineDen_pos (g : ℕ) (𝓜 : Finset ℕ) : 0 < fineDen g 𝓜 := Finset.prod_pos fun _ _ => by positivity

variable (O : Type) [CommRing O] [Module.Finite ℤ O]

def baseFun (D : ℕ) (φ : InvFun ℤ) (𝓜 : Finset ℕ) : InvFun O where
  toFun n B := D * ((restr O φ).toFun n B + ∑ M ∈ 𝓜, (restr O (fineMean M)).toFun n B)
  inv n m r hr B := by simp only [InvFun.inv _ _ _ r hr]
  zero B := by simp only [InvFun.zero, Finset.sum_const_zero, add_zero, mul_zero]

variable {O}

theorem eval_baseFun {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Finite ℤ X] (D : ℕ) (φ : InvFun ℤ)
    (𝓜 : Finset ℕ) (B : X → X → ℝ) :
    (baseFun O D φ 𝓜).eval X B = D * (φ.eval X B + ∑ M ∈ 𝓜, (fineMean M).eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(baseFun O D φ 𝓜).eval_eq hr]
  have h : ∀ ψ : InvFun ℤ, (restr O ψ).toFun n (fun a b => B (r a) (r b)) = ψ.eval X B := fun ψ =>
    ψ.eval_comp (r := r.restrictScalars ℤ) hr B
  simp only [baseFun, h]

theorem restr_twist (φ : InvFun ℤ) (σ : O ≃+* O) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    (restr O φ).toFun n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) = (restr O φ).toFun n B := by
  let e : (Fin n → O) ≃ₗ[ℤ] (Fin n → O) :=
    AddEquiv.toIntLinearEquiv (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)
  exact φ.eval_equiv e B

theorem baseFun_twist (D : ℕ) (φ : InvFun ℤ) (𝓜 : Finset ℕ) (σ : O ≃+* O) (n : ℕ)
    (B : (Fin n → O) → (Fin n → O) → ℝ) :
    (baseFun O D φ 𝓜).toFun n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) = (baseFun O D φ 𝓜).toFun n B := by
  simp only [baseFun, restr_twist]

end Base

section Poly

variable {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X]
  {m : ℕ}

variable {X} in

structure IsCell (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop where

  mem : ∀ i, γ i ∈ balForms bar X

  nonneg : ∀ i y, 0 ≤ γ i y y

  linear : φ.LinearOn γ

  strict : IsStrict bar φ γ

structure IsPolyFanOn : Prop where

  homog : ∀ B ∈ psdCone bar X, ∀ t : ℝ, 0 ≤ t → evalR φ (t • B) = t * evalR φ B

  superadd : ∀ B ∈ psdCone bar X, ∀ B' ∈ psdCone bar X, evalR φ B + evalR φ B' ≤ evalR φ (B + B')

  integral : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, φ.evalZ β = n

  pos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < φ.evalZ β

  finite : ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar φ γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧
      pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)

def IsPolyFan (bar : O → O) (q : ℕ) (φ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    IsPolyFanOn bar φ X

variable {bar φ X}

theorem IsCone.isCell {γ : Fin m → LinearMap.BilinForm ℤ X} (h : IsCone bar φ γ) : IsCell bar φ γ :=
  ⟨h.mem, h.nonneg, h.linear, h.strict⟩

theorem IsPolFanOn.isPolyFanOn (h : IsPolFanOn bar φ X) : IsPolyFanOn bar φ X where
  homog := h.homog
  superadd := h.superadd
  integral := h.integral
  pos := h.pos
  finite := by
    obtain ⟨S, hS, h1⟩ := h.finite
    refine ⟨S, hS, fun B hB => ?_⟩
    obtain ⟨m, γ, c, hγ, hc, rfl⟩ := h.cover B hB
    obtain ⟨e, he⟩ := h1 m γ hγ
    refine ⟨e, m, _, c, (hγ.pull_equiv e).isCell, he, hc, LinearMap.ext₂ fun a b => ?_⟩
    simp [LinearMap.sum_apply]

theorem isPolyFanOn_minVal_int : IsPolyFanOn id (InvFun.minVal ℤ) ℤ := isPolFanOn_minVal_int.isPolyFanOn

theorem isPolyFan_minVal_one : IsPolyFan id 1 (InvFun.minVal ℤ) := fun X _ _ _ _ hX => (isPolFan_minVal_one X hX).isPolyFanOn

example : IsCell id (InvFun.minVal ℤ) ![mulForm] := isCone_mulForm.isCell

end Poly

section Cover

variable {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]

def HasRedCover : Prop :=
  ∃ (k : ℕ) (n : Fin k → ℕ) (P : ∀ j, Fin (n j) → LinearMap.BilinForm ℤ X),
    (∀ j i y z, P j i y z = P j i z y) ∧ (∀ j i y, 0 ≤ P j i y y) ∧
    ∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (j : Fin k) (c : Fin (n j) → ℝ), (∀ i, 0 ≤ c i) ∧
      pullR e.toLinearMap B = ∑ i, c i • toReal (P j i)

def Dominates : Prop :=
  ∀ ℓ m : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β) →
    ∃ C : ℕ, ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → m β ≤ C * ℓ β

end Cover

end GlobalTheory.PolFan
