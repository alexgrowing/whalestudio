import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.OffDom

section General

open scoped Pointwise

variable {E : Type} [Field E] [NumberField E]

theorem isTorsionFree_int (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.IsTorsionFree (𝓞 E) X] :
    Module.IsTorsionFree ℤ X := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have h0 : r ≠ 0 := hr.ne_zero
  have h1 : IsRegular (r : 𝓞 E) := isRegular_of_ne_zero (by exact_mod_cast h0)
  refine Module.IsTorsionFree.isSMulRegular h1 ?_
  have hxy' : r • x = r • y := hxy
  simp only [Int.cast_smul_eq_zsmul]
  exact hxy'

theorem eq_zero_of_posDef {X : Type} [AddCommGroup X] [Module.IsTorsionFree ℤ X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}
    (h : IsPosDef B) {y : X} (hy : B y y = 0) : y = 0 := by
  by_contra hne
  have hl : LinearIndependent ℤ ![y] := linearIndependent_unique_iff.2 (by simpa using hne)
  have := h 1 ![y] hl ![1] (by simp)
  simp [hy] at this

def tw (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} (a : Fin n → 𝓞 E) : Fin n → 𝓞 E := fun i => σ (a i)

variable {n m : ℕ}

theorem tw_add (σ : 𝓞 E ≃+* 𝓞 E) (a b : Fin n → 𝓞 E) : tw σ (a + b) = tw σ a + tw σ b :=
  funext fun i => by simp [tw]

theorem tw_sub (σ : 𝓞 E ≃+* 𝓞 E) (a b : Fin n → 𝓞 E) : tw σ (a - b) = tw σ a - tw σ b :=
  funext fun i => by simp [tw]

theorem tw_smul (σ : 𝓞 E ≃+* 𝓞 E) (c : 𝓞 E) (a : Fin n → 𝓞 E) : tw σ (c • a) = σ c • tw σ a :=
  funext fun i => by simp [tw]

theorem tw_zero (σ : 𝓞 E ≃+* 𝓞 E) : tw σ (0 : Fin n → 𝓞 E) = 0 := funext fun i => by simp [tw]

theorem tw_symm (σ : 𝓞 E ≃+* 𝓞 E) (a : Fin n → 𝓞 E) : tw σ (tw σ.symm a) = a := funext fun i => by simp [tw]

theorem tw_symm' (σ : 𝓞 E ≃+* 𝓞 E) (a : Fin n → 𝓞 E) : tw σ.symm (tw σ a) = a := funext fun i => by simp [tw]

def conj (σ : 𝓞 E ≃+* 𝓞 E) (r : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin m → 𝓞 E)) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin m → 𝓞 E) where
  toFun a := tw σ.symm (r (tw σ a))
  map_add' a b := by simp only [tw_add, map_add]
  map_smul' c a := by
    simp only [tw_smul, map_smul, RingHom.id_apply]
    rw [σ.symm_apply_apply]

theorem tw_conj (σ : 𝓞 E ≃+* 𝓞 E) (r : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin m → 𝓞 E)) (a : Fin n → 𝓞 E) :
    tw σ (conj σ r a) = r (tw σ a) := tw_symm σ _

theorem conj_surjective (σ : 𝓞 E ≃+* 𝓞 E) {r : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin m → 𝓞 E)} (hr : Function.Surjective r) :
    Function.Surjective (conj σ r) := fun b => by
  obtain ⟨a, ha⟩ := hr (tw σ b)
  exact ⟨tw σ.symm a, by simp only [conj, LinearMap.coe_mk, AddHom.coe_mk, tw_symm, ha, tw_symm']⟩

theorem minVal_twist (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    (InvFun.minVal (𝓞 E)).toFun n (fun a b => B (tw σ a) (tw σ b)) = (InvFun.minVal (𝓞 E)).toFun n B := by
  simp only [InvFun.minVal]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, tw_zero]
  constructor
  · rintro ⟨⟨y, h⟩, h'⟩
    exact ⟨⟨tw σ y, h⟩, h'⟩
  · rintro ⟨⟨y, h⟩, h'⟩
    exact ⟨⟨tw σ.symm y, by rw [tw_symm]; exact h⟩, h'⟩

theorem minVal_smul {t : ℝ} (ht : 0 < t) (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    (InvFun.minVal (𝓞 E)).toFun n (fun a b => t * B a b) = t * (InvFun.minVal (𝓞 E)).toFun n B := by
  simp only [InvFun.minVal]
  have : {x | (∃ y, t * B y y = x) ∧ x ≠ t * B 0 0} = t • {x | (∃ y, B y y = x) ∧ x ≠ B 0 0} := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨⟨y, rfl⟩, h⟩
      exact ⟨B y y, ⟨⟨y, rfl⟩, fun e => h (by rw [e])⟩, rfl⟩
    · rintro ⟨x', ⟨⟨y, rfl⟩, h⟩, rfl⟩
      exact ⟨⟨y, rfl⟩, fun e => h (mul_left_cancel₀ ht.ne' e)⟩
  rw [this, Real.sInf_smul_of_nonneg ht.le, smul_eq_mul]

theorem toFun_zeroForm (φ : InvFun (𝓞 E)) (n : ℕ) : φ.toFun n (fun _ _ => 0) = 0 := by
  have := φ.inv n 0 0 (fun y => ⟨0, Subsingleton.elim _ _⟩) (fun _ _ => 0)
  rw [φ.zero] at this
  exact this

end General

section Dom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) {n m : ℕ}

def IsDom (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) : Prop :=
  ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module (𝓞 E) X₁) (_ : Module.Projective (𝓞 E) X₁)
    (r : (Fin n → 𝓞 E) →ₗ[𝓞 E] X₁) (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧
    Module.finrank (𝓞 E) X₁ ≤ q ∧ B₁ ∈ realForms H.bar X₁ ∧ IsPosDef B₁ ∧ ∀ a b, B a b = B₁ (r a) (r b)

def IsDomT (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) : Prop :=
  ∃ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 ∧ IsDom H q n fun a b => B (tw σ a) (tw σ b)

variable {H q}

theorem isDom_comp_iff {r : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin m → 𝓞 E)} (hr : Function.Surjective r)
    (B : (Fin m → 𝓞 E) → (Fin m → 𝓞 E) → ℝ) :
    IsDom H q n (fun a b => B (r a) (r b)) ↔ IsDom H q m B := by
  constructor
  · rintro ⟨X₁, _, _, _, s, B₁, hs, hq, hB, hd, he⟩
    have he' : ∀ a b, B (r a) (r b) = B₁ (s a) (s b) := he
    have : Module.IsTorsionFree ℤ X₁ := isTorsionFree_int (E := E) X₁
    have hk : LinearMap.ker r ≤ LinearMap.ker s := fun a ha => by
      rw [LinearMap.mem_ker] at ha ⊢
      refine eq_zero_of_posDef hd ?_
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
    refine ⟨X₁, _, _, inferInstance, s', B₁, fun y => ?_, hq, hB, hd, fun x y => ?_⟩
    · obtain ⟨a, rfl⟩ := hs y
      exact ⟨r a, hs' a⟩
    · obtain ⟨a, rfl⟩ := hr x
      obtain ⟨b, rfl⟩ := hr y
      rw [hs', hs']
      exact he' a b
  · rintro ⟨X₁, _, _, _, s, B₁, hs, hq, hB, hd, he⟩
    exact ⟨X₁, _, _, inferInstance, s ∘ₗ r, B₁, hs.comp hr, hq, hB, hd, fun a b => he _ _⟩

theorem isDomT_comp_iff {r : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin m → 𝓞 E)} (hr : Function.Surjective r)
    (B : (Fin m → 𝓞 E) → (Fin m → 𝓞 E) → ℝ) :
    IsDomT H q n (fun a b => B (r a) (r b)) ↔ IsDomT H q m B :=
  exists_congr fun σ => and_congr_right fun _ => by
    have := isDom_comp_iff (H := H) (q := q) (conj_surjective σ hr) (fun a b => B (tw σ a) (tw σ b))
    simpa only [tw_conj] using this

theorem isDomT_twist_iff {σ : 𝓞 E ≃+* 𝓞 E} (hσ : σ H.w0 = H.w0) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    IsDomT H q n (fun a b => B (tw σ a) (tw σ b)) ↔ IsDomT H q n B := by
  constructor
  · rintro ⟨ρ, hρ, h⟩
    exact ⟨ρ.trans σ, by simp [hρ, hσ], h⟩
  · rintro ⟨ρ, hρ, h⟩
    have hσ' : σ.symm H.w0 = H.w0 := (RingEquiv.symm_apply_eq σ).2 hσ.symm
    refine ⟨ρ.trans σ.symm, by simp [hρ, hσ'], ?_⟩
    have e1 : ∀ c : Fin n → 𝓞 E, tw σ (tw (ρ.trans σ.symm) c) = tw ρ c := fun c => funext fun i => by simp [tw]
    simp only [e1]
    exact h

theorem isDom_smul {t : ℝ} (ht : 0 < t) {B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ} (h : IsDom H q n B) :
    IsDom H q n (fun a b => t * B a b) := by
  obtain ⟨X₁, _, _, _, s, B₁, hs, hq, hB, hd, he⟩ := h
  refine ⟨X₁, _, _, inferInstance, s, t • B₁, hs, hq, Submodule.smul_mem _ _ hB, fun k x hx c hc => ?_,
    fun a b => by simp [he a b]⟩
  refine (mul_pos ht (hd k x hx c hc)).trans_eq ?_
  simp only [Finset.mul_sum, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem isDomT_smul_iff {t : ℝ} (ht : 0 < t) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    IsDomT H q n (fun a b => t * B a b) ↔ IsDomT H q n B := by
  constructor
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ, hσ, ?_⟩
    have := isDom_smul (inv_pos.2 ht) h
    simpa only [inv_mul_cancel_left₀ ht.ne'] using this
  · rintro ⟨σ, hσ, h⟩
    exact ⟨σ, hσ, isDom_smul ht h⟩

theorem isDomT_zero : IsDomT H q n (fun _ _ => 0) := by
  refine ⟨RingEquiv.refl _, rfl, PUnit, _, _, inferInstance, 0, 0, fun _ => ⟨0, rfl⟩,
    Module.finrank_zero_of_subsingleton.trans_le (Nat.zero_le _), zero_mem _,
    fun k x hx c hc => ?_, fun _ _ => by simp⟩
  obtain ⟨i, -⟩ := Function.ne_iff.1 hc
  exact (hx.ne_zero i (Subsingleton.elim _ _)).elim

variable (H q) in
open Classical in

def extFun (φ : InvFun (𝓞 E)) : InvFun (𝓞 E) where
  toFun n B := if IsDomT H q n B then φ.toFun n B else (InvFun.minVal (𝓞 E)).toFun n B
  inv n m r hr B := by
    by_cases h : IsDomT H q m B
    · rw [if_pos ((isDomT_comp_iff hr B).2 h), if_pos h]
      exact φ.inv n m r hr B
    · rw [if_neg (mt (isDomT_comp_iff hr B).1 h), if_neg h]
      exact (InvFun.minVal _).inv n m r hr B
  zero B := by
    split_ifs
    · exact φ.zero B
    · exact (InvFun.minVal _).zero B

variable {φ : InvFun (𝓞 E)}

theorem extFun_of {B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ} (h : IsDomT H q n B) :
    (extFun H q φ).toFun n B = φ.toFun n B := if_pos h

theorem extFun_of_not {B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ} (h : ¬ IsDomT H q n B) :
    (extFun H q φ).toFun n B = (InvFun.minVal (𝓞 E)).toFun n B := if_neg h

end Dom

section Props

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {q : ℕ} {φ : InvFun (𝓞 E)}

theorem isTwInv_extFun (htw : IsTwInv H φ) : IsTwInv H (extFun H q φ) := by
  intro σ hσ n B
  show (extFun H q φ).toFun n (fun a b => B (tw σ a) (tw σ b)) = _
  have hiff := isDomT_twist_iff (q := q) hσ B
  by_cases h : IsDomT H q n B
  · rw [extFun_of (hiff.2 h), extFun_of h]
    exact htw σ hσ n B
  · rw [extFun_of_not (mt hiff.1 h), extFun_of_not h]
    exact minVal_twist σ n B

theorem extFun_homog (hpol : IsPolFan H.bar q φ) (htw : IsTwInv H φ) (n k : ℕ)
    (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    (extFun H q φ).toFun n (fun a b => k * B a b) = k * (extFun H q φ).toFun n B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_mul]
    rw [extFun_of isDomT_zero, toFun_zeroForm]
  have ht : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases h : IsDomT H q n B
  · rw [extFun_of ((isDomT_smul_iff ht B).2 h), extFun_of h]
    obtain ⟨σ, hσ, X₁, _, _, _, s, B₁, hs, hq, hB, hd, he⟩ := h
    have he' : ∀ a b, B (tw σ a) (tw σ b) = B₁ (s a) (s b) := he
    have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective s hs
    have htw' : ∀ B' : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ,
        φ.toFun n (fun a b => B' (tw σ a) (tw σ b)) = φ.toFun n B' := htw σ hσ n
    rw [← htw' B, ← htw' (fun a b => k * B a b)]
    simp only [he']
    have e1 := φ.eval_eq hs (fun x y => (k : ℝ) * B₁ x y)
    have e2 := φ.eval_eq hs (fun x y => B₁ x y)
    rw [← e1, ← e2]
    have := (hpol X₁ hq).homog B₁ (hd.mem_psdCone hB) k ht.le
    simpa [evalR] using this
  · rw [extFun_of_not (mt (isDomT_smul_iff ht B).1 h), extFun_of_not h]
    exact minVal_smul ht n B

variable (H q φ) in

theorem evalR_extFun {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone H.bar X) :
    evalR (extFun H q φ) B = evalR φ B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  unfold evalR
  rw [(extFun H q φ).eval_eq hr, φ.eval_eq hr]
  refine extFun_of ⟨RingEquiv.refl _, rfl, ?_⟩
  obtain ⟨X₁, _, _, _, s, B₁, hs, hB₁, hd, he⟩ := hB
  have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective s hs
  have hrk : Module.finrank (𝓞 E) X₁ ≤ q := by
    have := LinearMap.finrank_range_le s
    rw [LinearMap.range_eq_top.2 hs, finrank_top] at this
    exact this.trans hX
  exact ⟨X₁, _, _, inferInstance, s ∘ₗ r, B₁, hs.comp hr, hrk, hB₁, hd, fun a b => he _ _⟩

theorem toReal_mem_psdCone {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms H.bar X) (hp : ∀ y, 0 ≤ β y y) : toReal β ∈ psdCone H.bar X := by
  have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)
  simpa using this

theorem isCone_of_agree {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {φ₁ φ₂ : InvFun (𝓞 E)}
    (h : ∀ B ∈ psdCone H.bar X, evalR φ₁ B = evalR φ₂ B) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (hc : IsCone H.bar φ₁ γ) : IsCone H.bar φ₂ γ := by
  have hz : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → φ₁.evalZ β = φ₂.evalZ β := fun β hβ hp => by
    rw [← evalR_toReal, ← evalR_toReal]
    exact h _ (toReal_mem_psdCone hβ hp)
  refine ⟨hc.mem, hc.nonneg, hc.basis, (linearOn_iff φ₂ γ).2 fun c hcn => ?_, ?_⟩
  · rw [← h _ (GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone (𝓞 E) H.bar X m γ c hc.mem hc.nonneg hcn), (linearOn_iff φ₁ γ).1 hc.linear c hcn]
    exact Finset.sum_congr rfl fun i _ => by rw [hz _ (hc.mem i) (hc.nonneg i)]
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hc.strict
    exact ⟨N, ℓ, hN, fun i => by rw [← hz _ (hc.mem i) (hc.nonneg i)]; exact h1 i,
      fun β hβ hp => by rw [← hz β hβ hp]; exact h2 β hβ hp,
      fun β hβ hp he => h3 β hβ hp (by rw [hz β hβ hp]; exact he)⟩

theorem isCone_extFun_iff {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) :
    IsCone H.bar (extFun H q φ) γ ↔ IsCone H.bar φ γ :=
  ⟨isCone_of_agree fun B hB => evalR_extFun H q φ hX hB,
    isCone_of_agree fun B hB => (evalR_extFun H q φ hX hB).symm⟩

theorem isPolFanOn_extFun {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) (h : IsPolFanOn H.bar φ X) : IsPolFanOn H.bar (extFun H q φ) X := by
  have agree := fun B (hB : B ∈ psdCone H.bar X) => evalR_extFun H q φ hX hB
  have hz : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (extFun H q φ).evalZ β = φ.evalZ β := fun β hβ hp => by
    rw [← evalR_toReal, ← evalR_toReal]
    exact agree _ (toReal_mem_psdCone hβ hp)
  refine ⟨fun B hB t ht => ?_, fun B hB B' hB' => ?_, fun β hβ hp => ?_, fun β hβ hp h0 => ?_,
    fun m m' γ s hγ => ?_, fun B hB => ?_, ?_⟩
  · rw [agree _ (smul_mem_psdCone hB ht), agree _ hB]
    exact h.homog B hB t ht
  · have hsum : B + B' ∈ psdCone H.bar X := by
      obtain ⟨m, γ, c, hγ, hc, rfl⟩ := h.cover B hB
      obtain ⟨m', γ', c', hγ', hc', rfl⟩ := h.cover B' hB'
      have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone (𝓞 E) H.bar X (m + m') (Fin.append γ γ') (Fin.append c c')
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
  · exact (isCone_extFun_iff hX _).2 (h.face m m' γ s ((isCone_extFun_iff hX _).1 hγ))
  · obtain ⟨m, γ, c, hγ, hc, e⟩ := h.cover B hB
    exact ⟨m, γ, c, (isCone_extFun_iff hX _).2 hγ, hc, e⟩
  · obtain ⟨S, hS, h1⟩ := h.finite
    exact ⟨S, hS, fun m γ hγ => h1 m γ ((isCone_extFun_iff hX _).1 hγ)⟩

end Props

section Pos

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {q : ℕ} {φ : InvFun (𝓞 E)}

theorem isTorsionFree_of_pos {X : Type} [AddCommGroup X] {be : LinearMap.BilinForm ℤ X}
    (hpos : ∀ y, y ≠ 0 → 0 < be y y) : Module.IsTorsionFree ℤ X := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have hxy' : r • x = r • y := hxy
  have hr0 : r ≠ 0 := hr.ne_zero
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero.2 hne
  have h1 : r • (x - y) = 0 := by rw [smul_sub, hxy', sub_self]
  have h3 : be (r • (x - y)) (r • (x - y)) = r * r * be (x - y) (x - y) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [h1] at h3
  have h4 : r * r * be (x - y) (x - y) = 0 := by rw [← h3]; simp
  rcases mul_eq_zero.1 h4 with h | h
  · exact hr0 (mul_self_eq_zero.1 h)
  · exact (hpos _ hd).ne' h

theorem finrank_le_of_isDomT {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {be : LinearMap.BilinForm ℤ X}
    (hpos : ∀ y, y ≠ 0 → 0 < be y y) {n : ℕ} {r : (Fin n → 𝓞 E) →ₗ[𝓞 E] X} (hr : Function.Surjective r)
    (h : IsDomT H q n fun a b => (be (r a) (r b) : ℝ)) : Module.finrank (𝓞 E) X ≤ q := by
  obtain ⟨σ, -, X₁, _, _, _, s, B₁, hs, hq, -, hd, he⟩ := h
  have he' : ∀ a b, (be (r (tw σ a)) (r (tw σ b)) : ℝ) = B₁ (s a) (s b) := he
  have : Module.IsTorsionFree ℤ X₁ := isTorsionFree_int (E := E) X₁
  have key : ∀ a, s a = 0 ↔ r (tw σ a) = 0 := fun a => by
    constructor
    · intro h0
      by_contra hne
      have e := he' a a
      simp only [h0, map_zero, LinearMap.zero_apply] at e
      exact (hpos _ hne).ne' (by exact_mod_cast e)
    · intro h0
      refine eq_zero_of_posDef hd ?_
      rw [← he' a a, h0]
      simp
  have key2 : ∀ a b, s a = s b ↔ r (tw σ a) = r (tw σ b) := fun a b => by
    rw [← sub_eq_zero, ← map_sub, key, tw_sub, map_sub, sub_eq_zero]
  let g : X₁ → X := fun y => r (tw σ (Function.surjInv hs y))
  have hg : ∀ a, g (s a) = r (tw σ a) := fun a => (key2 _ _).1 (Function.surjInv_eq hs (s a))
  have hadd : ∀ y y', g (y + y') = g y + g y' := fun y y' => by
    obtain ⟨a, rfl⟩ := hs y
    obtain ⟨b, rfl⟩ := hs y'
    rw [← map_add, hg, hg, hg, tw_add, map_add]
  let j : X₁ ≃+ X := AddEquiv.ofBijective (AddMonoidHom.mk' g hadd) ⟨fun y y' e => by
      obtain ⟨a, rfl⟩ := hs y
      obtain ⟨b, rfl⟩ := hs y'
      have e' : g (s a) = g (s b) := e
      rw [hg, hg] at e'
      exact (key2 a b).2 e', fun x => by
      obtain ⟨a, rfl⟩ := hr x
      refine ⟨s (tw σ.symm a), ?_⟩
      show g _ = _
      rw [hg, tw_symm]⟩
  have hj : ∀ (c : 𝓞 E) (y : X₁), j (c • y) = σ c • j y := fun c y => by
    obtain ⟨a, rfl⟩ := hs y
    show g (c • s a) = σ c • g (s a)
    rw [← map_smul, hg, hg, tw_smul, map_smul]
  have hrk := rank_eq_of_equiv_equiv σ j σ.bijective hj
  have : Module.finrank (𝓞 E) X₁ = Module.finrank (𝓞 E) X := by
    unfold Module.finrank
    rw [hrk]
  omega

theorem isPosFn_extFun (hpol : IsPolFan H.bar q φ) : IsPosFn H (extFun H q φ) := by
  intro X _ _ _ _ be hbe hpos
  have hz0 : ∀ y, 0 ≤ be y y := fun y => by
    by_cases hy : y = 0
    · simp [hy]
    · exact (hpos y hy).le
  have hbal : be ∈ balForms H.bar X := by rw [balForms_eq_levelForms]; exact hbe
  obtain ⟨y0, hy0⟩ := exists_ne (0 : X)
  by_cases hX : Module.finrank (𝓞 E) X ≤ q
  · have : Module.IsTorsionFree ℤ X := isTorsionFree_of_pos hpos
    have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
    have : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int (𝓞 E) X
    rw [← evalR_toReal, evalR_extFun H q φ hX (toReal_mem_psdCone hbal hz0), evalR_toReal]
    exact (hpol X hX).pos be hbal hz0 fun h0 => (hpos y0 hy0).ne' (by simp [h0])
  · obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
    rw [InvFun.evalZ, (extFun H q φ).eval_eq hr,
      extFun_of_not fun h => hX (finrank_le_of_isDomT hpos hr h)]
    simp only [InvFun.minVal]
    obtain ⟨a0, ha0⟩ := hr y0
    refine lt_of_lt_of_le one_pos (le_csInf ⟨_, ⟨⟨a0, rfl⟩, ?_⟩⟩ ?_)
    · rw [ha0, map_zero]
      simpa using (hpos y0 hy0).ne'
    · rintro x ⟨⟨a, rfl⟩, hx⟩
      have h1 : r a ≠ 0 := fun h0 => hx (by rw [h0, map_zero r])
      have h2 := hpos _ h1
      have h3 : (1 : ℤ) ≤ be (r a) (r a) := h2
      exact_mod_cast h3

end Pos

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ' : InvFun (𝓞 E)), IsPolFan H.bar q φ' → NoSelfInt H.bar q φ' → IsTwInv H φ' →
    ∃ φ'' : InvFun (𝓞 E), IsPolFan H.bar q φ'' ∧ NoSelfInt H.bar q φ'' ∧ IsTwInv H φ'' ∧ IsPosFn H φ'' ∧
      (∀ (n k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ''.toFun n (fun a b => k * B a b) = k * φ''.toFun n B) ∧
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
          IsCone H.bar φ'' γ → IsCone H.bar φ' γ := by
  intro E _ _ _ H q φ hpol hns htw
  refine ⟨extFun H q φ, fun X _ _ _ _ hX => isPolFanOn_extFun hX (hpol X hX), fun X _ _ _ _ hX m γ hγ => ?_,
    isTwInv_extFun htw, isPosFn_extFun hpol, extFun_homog hpol htw, fun X _ _ _ _ hX m γ hγ => ?_⟩
  · exact hns X hX m γ ((isCone_extFun_iff hX γ).1 hγ)
  · exact (isCone_extFun_iff hX γ).1 hγ

end GlobalTheory.PolFan.OffDom
