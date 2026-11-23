import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExtensionConeTransfer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc

noncomputable section

namespace GlobalTheory.PolFan.TameZ

def IsDom (g n : ℕ) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) : Prop :=
  ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Projective ℤ X₁) (r : (Fin n → ℤ) →ₗ[ℤ] X₁)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧ Module.finrank ℤ X₁ ≤ g ∧
    B₁ ∈ realForms (id : ℤ → ℤ) X₁ ∧ IsPosDef B₁ ∧ ∀ a b, B a b = B₁ (r a) (r b)

variable {g n m : ℕ}

theorem isDom_comp_iff {r : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)} (hr : Function.Surjective r)
    (B : (Fin m → ℤ) → (Fin m → ℤ) → ℝ) :
    IsDom g n (fun a b => B (r a) (r b)) ↔ IsDom g m B := by
  constructor
  · rintro ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩
    have he' : ∀ a b, B (r a) (r b) = B₁ (s a) (s b) := he
    have : Module.Finite ℤ X₁ := Module.Finite.of_surjective s hs
    have : Module.IsTorsionFree ℤ X₁ := inferInstance
    have hk : LinearMap.ker r ≤ LinearMap.ker s := fun a ha => by
      rw [LinearMap.mem_ker] at ha ⊢
      refine OffDom.eq_zero_of_posDef hd ?_
      calc B₁ (s a) (s a) = B (r a) (r a) := (he' a a).symm
        _ = B (r 0) (r 0) := by rw [ha, map_zero]
        _ = B₁ (s 0) (s 0) := he' 0 0
        _ = 0 := by simp
    let s' := (LinearMap.ker r).liftQ s hk ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
    have hs' : ∀ a, s' (r a) = s a := fun a => by
      have e : (r.quotKerEquivOfSurjective hr).symm (r a) = Submodule.Quotient.mk a :=
        (LinearEquiv.symm_apply_eq _).2 (by simp)
      simp only [s', LinearMap.comp_apply, LinearEquiv.coe_coe, e]
      rfl
    refine ⟨X₁, _, inferInstance, s', B₁, fun y => ?_, hq, hB, hd, fun x y => ?_⟩
    · obtain ⟨a, rfl⟩ := hs y
      exact ⟨r a, hs' a⟩
    · obtain ⟨a, rfl⟩ := hr x
      obtain ⟨b, rfl⟩ := hr y
      rw [hs', hs']
      exact he' a b
  · rintro ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩
    exact ⟨X₁, _, inferInstance, s ∘ₗ r, B₁, hs.comp hr, hq, hB, hd, fun a b => he _ _⟩

theorem isDom_smul {t : ℝ} (ht : 0 < t) {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (h : IsDom g n B) :
    IsDom g n (fun a b => t * B a b) := by
  obtain ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩ := h
  refine ⟨X₁, _, inferInstance, s, t • B₁, hs, hq, Submodule.smul_mem _ _ hB, fun k x hx c hc => ?_,
    fun a b => by simp [he a b]⟩
  refine (mul_pos ht (hd k x hx c hc)).trans_eq ?_
  simp only [Finset.mul_sum, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem isDom_smul_iff {t : ℝ} (ht : 0 < t) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) :
    IsDom g n (fun a b => t * B a b) ↔ IsDom g n B := by
  constructor
  · intro h
    have := isDom_smul (inv_pos.2 ht) h
    simpa only [inv_mul_cancel_left₀ ht.ne'] using this
  · exact isDom_smul ht

theorem toFun_zeroForm (φ : InvFun ℤ) (n : ℕ) : φ.toFun n (fun _ _ => 0) = 0 := by
  have := φ.inv n 0 0 (fun y => ⟨0, Subsingleton.elim _ _⟩) (fun _ _ => 0)
  rw [φ.zero] at this
  exact this

variable (g) in
open Classical in

def cutFun (φ : InvFun ℤ) : InvFun ℤ where
  toFun n B := if IsDom g n B then φ.toFun n B else 0
  inv n m r hr B := by
    by_cases h : IsDom g m B
    · rw [if_pos ((isDom_comp_iff hr B).2 h), if_pos h]
      exact φ.inv n m r hr B
    · rw [if_neg (mt (isDom_comp_iff hr B).1 h), if_neg h]
  zero B := by
    split_ifs
    · exact φ.zero B
    · rfl

variable {φ : InvFun ℤ}

theorem cutFun_of {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (h : IsDom g n B) :
    (cutFun g φ).toFun n B = φ.toFun n B := if_pos h

theorem cutFun_of_not {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (h : ¬ IsDom g n B) :
    (cutFun g φ).toFun n B = 0 := if_neg h

theorem cutFun_homog (hpol : IsPolFan id g φ) (n k : ℕ) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) :
    (cutFun g φ).toFun n (fun a b => k * B a b) = k * (cutFun g φ).toFun n B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_mul]
    by_cases h : IsDom g n (fun _ _ => (0 : ℝ))
    · rw [cutFun_of h, toFun_zeroForm]
    · rw [cutFun_of_not h]
  have ht : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases h : IsDom g n B
  · rw [cutFun_of ((isDom_smul_iff ht B).2 h), cutFun_of h]
    obtain ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩ := h
    obtain rfl : B = fun a b => B₁ (s a) (s b) := funext fun a => funext fun b => he a b
    have : Module.Finite ℤ X₁ := Module.Finite.of_surjective s hs
    have e1 := φ.eval_eq hs (fun x y => (k : ℝ) * B₁ x y)
    have e2 := φ.eval_eq hs (fun x y => B₁ x y)
    rw [← e1, ← e2]
    have := (hpol X₁ hq).homog B₁ (hd.mem_psdCone hB) k ht.le
    simpa [evalR] using this
  · rw [cutFun_of_not (mt (isDom_smul_iff ht B).1 h), cutFun_of_not h, mul_zero]

theorem cutFun_nonneg (hpol : IsPolFan id g φ) (n : ℕ) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) :
    0 ≤ (cutFun g φ).toFun n B := by
  by_cases h : IsDom g n B
  · rw [cutFun_of h]
    obtain ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩ := h
    obtain rfl : B = fun a b => B₁ (s a) (s b) := funext fun a => funext fun b => he a b
    have : Module.Finite ℤ X₁ := Module.Finite.of_surjective s hs
    have e : φ.toFun n (fun a b => B₁ (s a) (s b)) = evalR φ B₁ := by
      rw [evalR, φ.eval_eq hs]
    rw [e]
    exact (hpol X₁ hq).evalR_nonneg (hd.mem_psdCone hB)
  · rw [cutFun_of_not h]

theorem evalR_cutFun {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (hX : Module.finrank ℤ X ≤ g)
    {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (id : ℤ → ℤ) X) : evalR (cutFun g φ) B = evalR φ B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' ℤ X
  unfold evalR
  rw [(cutFun g φ).eval_eq hr, φ.eval_eq hr]
  refine cutFun_of ?_
  obtain ⟨X₁, _, i₁, _, s, B₁, hs, hB₁, hd, he⟩ := hB
  obtain rfl : i₁ = AddCommGroup.toIntModule X₁ := Subsingleton.elim _ _
  have : Module.Finite ℤ X₁ := Module.Finite.of_surjective s hs
  have hrk : Module.finrank ℤ X₁ ≤ g := by
    have := LinearMap.finrank_range_le s
    rw [LinearMap.range_eq_top.2 hs, finrank_top] at this
    exact this.trans hX
  exact ⟨X₁, _, inferInstance, s ∘ₗ r, B₁, hs.comp hr, hrk, hB₁, hd, fun a b => he _ _⟩

theorem toReal_mem_psdCone_int {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms (id : ℤ → ℤ) X) (hp : ∀ y, 0 ≤ β y y) : toReal β ∈ psdCone (id : ℤ → ℤ) X := by
  have := ConeSub.sum_smul_toReal_mem_psdCone ℤ id X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)
  simpa using this

theorem isCone_of_agree {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {φ₁ φ₂ : InvFun ℤ}
    (h : ∀ B ∈ psdCone (id : ℤ → ℤ) X, evalR φ₁ B = evalR φ₂ B) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (hc : IsCone id φ₁ γ) : IsCone id φ₂ γ := by
  have hz : ∀ β ∈ balForms (id : ℤ → ℤ) X, (∀ y, 0 ≤ β y y) → φ₁.evalZ β = φ₂.evalZ β := fun β hβ hp => by
    rw [← evalR_toReal, ← evalR_toReal]
    exact h _ (toReal_mem_psdCone_int hβ hp)
  refine ⟨hc.mem, hc.nonneg, hc.basis, (linearOn_iff φ₂ γ).2 fun c hcn => ?_, ?_⟩
  · rw [← h _ (ConeSub.sum_smul_toReal_mem_psdCone ℤ id X m γ c hc.mem hc.nonneg hcn),
      (linearOn_iff φ₁ γ).1 hc.linear c hcn]
    exact Finset.sum_congr rfl fun i _ => by rw [hz _ (hc.mem i) (hc.nonneg i)]
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hc.strict
    exact ⟨N, ℓ, hN, fun i => by rw [← hz _ (hc.mem i) (hc.nonneg i)]; exact h1 i,
      fun β hβ hp => by rw [← hz β hβ hp]; exact h2 β hβ hp,
      fun β hβ hp he => h3 β hβ hp (by rw [hz β hβ hp]; exact he)⟩

theorem isPolFanOn_of_agree {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {φ₁ φ₂ : InvFun ℤ}
    (agree : ∀ B ∈ psdCone (id : ℤ → ℤ) X, evalR φ₂ B = evalR φ₁ B) (h : IsPolFanOn id φ₁ X) :
    IsPolFanOn id φ₂ X := by
  have hz : ∀ β ∈ balForms (id : ℤ → ℤ) X, (∀ y, 0 ≤ β y y) → φ₂.evalZ β = φ₁.evalZ β := fun β hβ hp => by
    rw [← evalR_toReal, ← evalR_toReal]
    exact agree _ (toReal_mem_psdCone_int hβ hp)
  have hc : ∀ {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone id φ₂ γ ↔ IsCone id φ₁ γ := fun γ =>
    ⟨isCone_of_agree agree, isCone_of_agree fun B hB => (agree B hB).symm⟩
  refine ⟨fun B hB t ht => ?_, fun B hB B' hB' => ?_, fun β hβ hp => ?_, fun β hβ hp h0 => ?_,
    fun m m' γ s hγ => ?_, fun B hB => ?_, ?_⟩
  · rw [agree _ (smul_mem_psdCone hB ht), agree _ hB]
    exact h.homog B hB t ht
  · have hsum : B + B' ∈ psdCone (id : ℤ → ℤ) X := by
      obtain ⟨m, γ, c, hγ, hc, rfl⟩ := h.cover B hB
      obtain ⟨m', γ', c', hγ', hc', rfl⟩ := h.cover B' hB'
      have := ConeSub.sum_smul_toReal_mem_psdCone ℤ id X (m + m') (Fin.append γ γ') (Fin.append c c')
        (fun i => by refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hγ.mem, hγ'.mem])
        (fun i => by refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hγ.nonneg, hγ'.nonneg])
        (fun i => by refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hc, hc'])
      simpa [Fin.sum_univ_add] using this
    rw [agree _ hB, agree _ hB', agree _ hsum]
    exact h.superadd B hB B' hB'
  · rw [hz β hβ hp]
    exact h.integral β hβ hp
  · rw [hz β hβ hp]
    exact h.pos β hβ hp h0
  · exact (hc _).2 (h.face m m' γ s ((hc _).1 hγ))
  · obtain ⟨m, γ, c, hγ, hc', e⟩ := h.cover B hB
    exact ⟨m, γ, c, (hc _).2 hγ, hc', e⟩
  · obtain ⟨S, hS, h1⟩ := h.finite
    exact ⟨S, hS, fun m γ hγ => h1 m γ ((hc _).1 hγ)⟩

theorem exists_tame : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ →
    ∃ φs : InvFun ℤ, IsPolFan id g φs ∧ IsTame φs ∧ AgreesPsd g φs φ := by
  intro g φ hpol
  refine ⟨cutFun g φ, fun X _ i _ _ hX => ?_, ⟨cutFun_homog hpol, cutFun_nonneg hpol⟩,
    fun X _ _ _ hX B hB => evalR_cutFun hX hB⟩
  obtain rfl : i = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  exact isPolFanOn_of_agree (fun B hB => evalR_cutFun hX hB) (hpol X hX)

end GlobalTheory.PolFan.TameZ
