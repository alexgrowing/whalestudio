import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace OrbMark

section Twist

variable {O : Type} [CommRing O]

def twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : Fin n → O := fun i => σ (a i)

@[simp] theorem twv_apply (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) (i : Fin n) : twv σ a i = σ (a i) := rfl

theorem twv_zero (σ : O ≃+* O) (n : ℕ) : twv σ (0 : Fin n → O) = 0 := funext fun _ => map_zero σ

theorem twv_smul (σ : O ≃+* O) {n : ℕ} (c : O) (a : Fin n → O) : twv σ (c • a) = σ c • twv σ a :=
  funext fun _ => by simp [twv]

theorem twv_twv (σ τ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv τ (twv σ a) = twv (σ.trans τ) a := rfl

theorem twv_symm_twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ.symm (twv σ a) = a :=
  funext fun _ => σ.symm_apply_apply _

theorem twv_twv_symm (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ (twv σ.symm a) = a :=
  funext fun _ => σ.apply_symm_apply _

def conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) : (Fin n → O) →ₗ[O] (Fin m → O) where
  toFun a := twv σ.symm (r (twv σ a))
  map_add' a b := by
    have e : twv σ (a + b) = twv σ a + twv σ b := funext fun _ => map_add σ _ _
    rw [e, map_add]
    exact funext fun _ => map_add σ.symm _ _
  map_smul' c a := by
    rw [twv_smul, map_smul, twv_smul, RingHom.id_apply, σ.symm_apply_apply]

theorem twv_conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) (a : Fin n → O) :
    twv σ (conjLin σ r a) = r (twv σ a) := twv_twv_symm σ _

theorem conjLin_surjective (σ : O ≃+* O) {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) :
    Function.Surjective (conjLin σ r) := fun b => by
  obtain ⟨a, ha⟩ := hr (twv σ b)
  refine ⟨twv σ.symm a, ?_⟩
  show twv σ.symm (r (twv σ (twv σ.symm a))) = b
  rw [twv_twv_symm, ha, twv_symm_twv]

end Twist

section Mark

variable {O : Type} [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]

def IsOrbForm (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Prop :=
  ∃ s : (Fin n → O) →ₗ[O] (X₀ ⧸ (CarDim.orad v : Submodule O X₀)), Function.Surjective s ∧
    ∀ (a b : Fin n → O) (x y : X₀), Submodule.Quotient.mk x = s a → Submodule.Quotient.mk y = s b →
      B (twv σ a) (twv σ b) = v x y

theorem isOrbForm_comp_iff (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) {n m : ℕ}
    {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) (B : (Fin m → O) → (Fin m → O) → ℝ) :
    IsOrbForm v σ n (fun a b => B (r a) (r b)) ↔ IsOrbForm v σ m B := by
  set r' := conjLin σ r
  have hr' : Function.Surjective r' := conjLin_surjective σ hr
  constructor
  · rintro ⟨s, hs, H⟩
    obtain ⟨t, ht⟩ := Module.projective_lifting_property r' LinearMap.id hr'
    have hrt : ∀ a, r' (t a) = a := fun a => LinearMap.congr_fun ht a
    have hker : ∀ z, r' z = 0 → s z = 0 := by
      intro z hz
      obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (s z)
      rw [← hx]
      refine (Submodule.Quotient.mk_eq_zero _).2 fun c y => ?_
      obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
      have h1 := H (c • z) b (c • x) y (by rw [Submodule.Quotient.mk_smul, map_smul]; exact congrArg _ hx) hb.symm
      have h2 := H 0 b 0 y (by rw [map_zero]; rfl) hb.symm
      have e : r (twv σ (c • z)) = 0 := by
        rw [← twv_conjLin, map_smul, hz, smul_zero, twv_zero]
      have e0 : r (twv σ 0) = 0 := by rw [twv_zero, map_zero]
      dsimp only at h1 h2
      rw [e] at h1
      rw [e0, map_zero, LinearMap.zero_apply] at h2
      exact_mod_cast h1.symm.trans h2
    refine ⟨s ∘ₗ t, fun y => ?_, fun a b x y hx hy => ?_⟩
    · obtain ⟨a, rfl⟩ := hs y
      refine ⟨r' a, ?_⟩
      have : s (a - t (r' a)) = 0 := hker _ (by rw [map_sub, hrt, sub_self])
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    · have h := H (t a) (t b) x y hx hy
      dsimp only at h
      rwa [← twv_conjLin, ← twv_conjLin, hrt, hrt] at h
  · rintro ⟨s, hs, H⟩
    refine ⟨s ∘ₗ r', hs.comp hr', fun a b x y hx hy => ?_⟩
    have h := H (r' a) (r' b) x y hx hy
    show B (r (twv σ a)) (r (twv σ b)) = _
    rwa [twv_conjLin, twv_conjLin] at h

theorem eq_zero_of_isOrbForm_zero {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {B : (Fin 0 → O) → (Fin 0 → O) → ℝ}
    (h : IsOrbForm v σ 0 B) : v = 0 := by
  obtain ⟨s, hs, -⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  have hx : x ∈ (CarDim.orad v : Submodule O X₀) := by
    obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
    rw [Subsingleton.elim a 0, map_zero] at ha
    exact (Submodule.Quotient.mk_eq_zero _).1 ha.symm
  simpa using hx 1 y

end Mark

section Fun

variable (O : Type) [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]

open Classical in

def orbFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) : InvFun O where
  toFun n B := if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0
  inv n m r hr B := by
    simp only [isOrbForm_comp_iff v _ hr]
  zero B := by
    rw [if_neg]
    rintro ⟨hv, σ, -, h⟩
    exact hv (eq_zero_of_isOrbForm_zero h)

variable {O}

open Classical in
theorem orbFun_toFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    (orbFun O w0 v).toFun n B = if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0 := rfl

theorem orbFun_eval_eq_zero_or_one (w0 : O) (v : LinearMap.BilinForm ℤ X₀) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] (B : X → X → ℝ) : (orbFun O w0 v).eval X B = 0 ∨ (orbFun O w0 v).eval X B = 1 := by
  unfold InvFun.eval
  rw [orbFun_toFun]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem eq_zero_of_isOrbForm_const {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {n : ℕ}
    (h : IsOrbForm v σ n fun _ _ => 0) : v = 0 := by
  obtain ⟨s, hs, H⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
  obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
  have := H a b x y ha.symm hb.symm
  simp only [LinearMap.zero_apply]
  have h0 : ((v x y : ℤ) : ℝ) = 0 := this.symm
  exact_mod_cast h0

theorem orbFun_evalZ_zero (w0 : O) {v : LinearMap.BilinForm ℤ X₀} (hv : v ≠ 0) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] : (orbFun O w0 v).evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_neg]
  rintro ⟨-, σ, -, h⟩
  refine hv (eq_zero_of_isOrbForm_const (σ := σ) (n := n) ?_)
  simpa using h

theorem orbFun_evalZ_self (w0 : O) {v : LinearMap.BilinForm ℤ X₀} [Module.Finite O X₀] (hv : v ≠ 0)
    (hsym : ∀ y z, v y z = v z y) : (orbFun O w0 v).evalZ v = 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X₀
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_pos]
  refine ⟨hv, RingEquiv.refl O, rfl, (CarDim.orad v).mkQ ∘ₗ r, (Submodule.mkQ_surjective _).comp hr,
    fun a b x y hx hy => ?_⟩
  have hx' : x - r a ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hx
  have hy' : y - r b ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hy
  have e1 : v x y = v (r a) y := by
    have := hx' 1 y
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have e2 : v (r a) y = v (r a) (r b) := by
    have := hy' 1 (r a)
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero, hsym, hsym (r b)] at this
    exact this
  show ((v (r a) (r b) : ℤ) : ℝ) = (v x y : ℝ)
  rw [e1, e2]

end Fun

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]

theorem isTwInv_orbFun (H : Host E) (v : LinearMap.BilinForm ℤ X₀) : IsTwInv H (orbFun (𝓞 E) H.w0 v) := by
  intro τ hτ n B
  rw [orbFun_toFun, orbFun_toFun]
  congr 2
  apply propext
  constructor
  · rintro ⟨σ, hσ, s, hs, h⟩
    exact ⟨σ.trans τ, by simp [hσ, hτ], s, hs, fun a b x y hx hy => h a b x y hx hy⟩
  · rintro ⟨σ, hσ, s, hs, h⟩
    refine ⟨σ.trans τ.symm, by simp [hσ, RingEquiv.symm_apply_eq, hτ], s, hs, fun a b x y hx hy => ?_⟩
    have := h a b x y hx hy
    show B (twv τ (twv (σ.trans τ.symm) a)) (twv τ (twv (σ.trans τ.symm) b)) = _
    rw [twv_twv, twv_twv]
    convert this using 3 <;> ext i <;> simp

end Host

example : (orbFun ℤ 0 mulForm).evalZ mulForm = 1 ∧ (orbFun ℤ 0 mulForm).evalZ (0 : LinearMap.BilinForm ℤ ℤ) = 0 := by
  refine ⟨orbFun_evalZ_self 0 (fun h => by simpa using LinearMap.congr_fun₂ h 1 1) fun y z => by simp [mul_comm], ?_⟩
  exact orbFun_evalZ_zero 0 fun h => by simpa using LinearMap.congr_fun₂ h 1 1

end OrbMark

end GlobalTheory.PolFan
