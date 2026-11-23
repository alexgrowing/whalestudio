import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
open NumberField GlobalTheory.RealMult
open scoped nonZeroDivisors

namespace GlobalTheory.RealMult.SpanDual

theorem exists_im_ne_zero {n : ℕ} (hn : 0 < n) (Λ : Submodule ℤ (Fin n → ℂ))
    (hspan : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤) (h : Fin n → ℝ) (hpos : ∀ j, 0 < h j) :
    ∃ l ∈ Λ, ∃ l' ∈ Λ, (∑ j, (h j : ℂ) * (l j * starRingEnd ℂ (l' j))).im ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun z w ↦ (∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j))).im)
      (fun z z' w ↦ by simp [add_mul, mul_add, Finset.sum_add_distrib])
      (fun r z w ↦ by
        have : (∑ j, (h j : ℂ) * ((r • z) j * starRingEnd ℂ (w j))) =
            (r : ℂ) * ∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [Pi.smul_apply, Complex.real_smul]; ring
        rw [this, Complex.im_ofReal_mul, smul_eq_mul])
      (fun z w w' ↦ by simp [add_mul, mul_add, Finset.sum_add_distrib])
      (fun r z w ↦ by
        have : (∑ j, (h j : ℂ) * (z j * starRingEnd ℂ ((r • w) j))) =
            (r : ℂ) * ∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring
        rw [this, Complex.im_ofReal_mul, smul_eq_mul])
  have h1 : ∀ l ∈ Λ, B l = 0 := fun l hl ↦
    LinearMap.ext_on hspan (fun w hw ↦ by simpa [B] using hcon l hl w hw)
  have h2 : B = 0 := LinearMap.ext_on hspan (fun z hz ↦ by rw [h1 z hz]; rfl)
  have h3 := congrArg (fun B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ ↦
    B (Pi.single ⟨0, hn⟩ 1) (Pi.single ⟨0, hn⟩ Complex.I)) h2
  simp only [B, LinearMap.mk₂_apply] at h3
  rw [Finset.sum_eq_single ⟨0, hn⟩ (fun b _ hb ↦ by simp [Pi.single_apply, hb]) (by simp)] at h3
  simp at h3
  exact (hpos ⟨0, hn⟩).ne' h3

theorem isIntegral_of_stab {F : Type} [Field F] {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (Fin n → ℂ)) (e : Fin n → (F →+* ℝ))
    [DiscreteTopology Λ] (hspan : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤) (s : F)
    (hs : ∀ l ∈ Λ, (fun j ↦ (e j s : ℂ) * l j) ∈ Λ) : IsIntegral ℤ s := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let φ : F →+* (Fin n → ℂ) := Pi.ringHom fun j ↦ Complex.ofRealHom.comp (e j)
  letI : Module F (Fin n → ℂ) := Module.compHom _ φ
  have hsmul : ∀ (t : F) (z : Fin n → ℂ), t • z = fun j ↦ (e j t : ℂ) * z j := fun _ _ ↦ rfl
  haveI : IsScalarTower ℤ F (Fin n → ℂ) := ⟨fun k x y ↦ by
    funext j
    simp only [hsmul, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast]
    push_cast; ring⟩
  haveI : Module.IsTorsionFree F (Fin n → ℂ) := ⟨fun r hr z w hzw ↦ by
    have hr0 : r ≠ 0 := hr.ne_zero
    funext j
    have := congrFun hzw j
    simp only [hsmul] at this
    exact mul_left_cancel₀ (by simpa using (e j).injective.ne hr0 |>.trans_eq (map_zero _)) this⟩
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  haveI := ZLattice.module_finite ℝ Λ
  have hfg : Λ.FG := Module.Finite.iff_fg.mp inferInstance
  have hne : Λ ≠ ⊥ := by
    intro h0
    rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
    exact bot_ne_top hspan
  exact isIntegral_of_smul_mem_submodule Λ hne hfg s hs

theorem dualLat_le {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) (c : 𝔠.elt) (hc0 : (c : F) ≠ 0)
    (N : Submodule (𝓞 F) F) (hN0 : N ≠ ⊥) (hN : N ≤ dualLat 𝔠)
    (H : ∀ t : F, (∀ y ∈ N, ∃ m : ℤ, Algebra.trace ℚ F ((c : F) * t * y) = m) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → IsIntegral ℤ ((a : F) * t)) :
    (dualLat 𝔠 : Submodule (𝓞 F) F) ≤ N := by
  set C : FractionalIdeal (𝓞 F)⁰ F := (𝔠 : FractionalIdeal (𝓞 F)⁰ F) with hCdef
  have hC : C ≠ 0 := 𝔠.ne_zero
  have hcC : (c : F) ∈ C := c.2
  let Nf : FractionalIdeal (𝓞 F)⁰ F := ⟨N, FractionalIdeal.isFractional_of_le hN⟩
  have hNf : Nf ≠ 0 := by
    intro h0
    apply hN0
    have := congrArg (fun I : FractionalIdeal (𝓞 F)⁰ F ↦ (I : Submodule (𝓞 F) F)) h0
    simpa [Nf] using this
  set cs := FractionalIdeal.spanSingleton (𝓞 F)⁰ (c : F)
  have hcs : cs ≠ 0 := by simpa [cs, FractionalIdeal.spanSingleton_eq_zero_iff] using hc0
  have key : FractionalIdeal.dual ℤ ℚ (cs * Nf) * (cs * C⁻¹) ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro t ht u hu
    obtain ⟨v, hv, rfl⟩ := (FractionalIdeal.mem_singleton_mul).mp hu
    have hcv : (c : F) * v ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      have := FractionalIdeal.mul_mem_mul hcC hv
      rwa [mul_inv_cancel₀ hC] at this
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hcv
    have hint : IsIntegral ℤ ((a : F) * t) := by
      refine H t (fun y hy ↦ ?_) a (fun d ↦ ?_)
      · have hy' : (c : F) * y ∈ cs * Nf :=
          FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hy
        obtain ⟨m, hm⟩ := (FractionalIdeal.mem_dual (mul_ne_zero hcs hNf)).mp ht _ hy'
        refine ⟨m, ?_⟩
        rw [Algebra.traceForm_apply] at hm
        rw [show (c : F) * t * y = t * ((c : F) * y) by ring, ← hm]; simp
      · have hvd : v * d ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
          have := FractionalIdeal.mul_mem_mul hv d.2
          rwa [inv_mul_cancel₀ hC] at this
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp hvd
        refine ⟨b, Subtype.ext ?_⟩
        simp only [Submodule.coe_smul, Algebra.smul_def]
        change (a : F) * d = (b : F) * c
        change algebraMap (𝓞 F) F a = _ at ha
        change algebraMap (𝓞 F) F b = _ at hb
        change algebraMap (𝓞 F) F a * d = algebraMap (𝓞 F) F b * c
        rw [ha, hb]; ring
    rw [mul_comm, ← ha]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨_, hint⟩, rfl⟩
  rw [FractionalIdeal.dual_eq_mul_inv, mul_inv] at key
  have key2 : FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹ ≤ 1 := by
    convert key using 1
    calc FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹
        = FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹ * (cs⁻¹ * cs) := by rw [inv_mul_cancel₀ hcs, mul_one]
      _ = _ := by ring
  have key3 : FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹ * Nf ≤ 1 * Nf :=
    FractionalIdeal.mul_le.mpr fun i hi j hj ↦ FractionalIdeal.mul_mem_mul (key2 hi) hj
  simp only [mul_assoc, inv_mul_cancel₀ hNf, mul_one, one_mul] at key3
  have : dualLat 𝔠 ≤ Nf := by
    unfold dualLat
    rw [FractionalIdeal.dual_eq_mul_inv]
    exact key3
  exact (FractionalIdeal.coe_le_coe.mpr this)

theorem dualLat_le_span_values : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (h : Fin (Module.finrank ℚ F) → ℝ),
    (∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ Λ → (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin (Module.finrank ℚ F) → ℂ)) = ⊤ → (∀ j, 0 < h j) →
    ∀ P : Λ → Λ → F, (∀ l l' : Λ, P l l' = -P l' l) → (∀ l₁ l₂ l' : Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') →
      (∀ (a : 𝓞 F) (l l' al : Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') →
      (∀ l l' : Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) →
      (∀ l l' : Λ, P l l' ∈ dualLat 𝔠) →
    (∀ x : Fin (Module.finrank ℚ F) → ℂ, (∀ l : Λ, ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (x j * starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im = 2 * n) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → (fun j ↦ (e j (a : F) : ℂ) * x j) ∈ Λ) →
    ∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : Λ, t = P l l'} := by
  intro F _ _ _ 𝔠 c hc Λ e h hΛa hdisc hspan hpos P _hanti _hadd hlin htr hdual hker
  have hn : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hc0 : (c : F) ≠ 0 := fun h0 ↦ by
    have := hc (e ⟨0, hn⟩); rw [h0, map_zero] at this; exact lt_irrefl _ this

  have hb : ∀ (s : F) (l₀ l : Λ),
      (∑ j, (h j : ℂ) * (((e j s : ℂ) * (l₀ : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * s * P l₀ l) : ℚ) : ℝ) := by
    intro s l₀ l
    obtain ⟨m, hm0, hmint⟩ :=
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic s)).exists_integral_multiple
    let a : 𝓞 F := ⟨m • s, hmint⟩
    have ha : (a : F) = (m : F) * s := by simp [a, zsmul_eq_mul]
    have hal : (fun j ↦ (e j (a : F) : ℂ) * (l₀ : Fin (Module.finrank ℚ F) → ℂ) j) ∈ Λ := hΛa a l₀ l₀.2
    have h1 := htr ⟨_, hal⟩ l
    rw [hlin a l₀ l ⟨_, hal⟩ rfl] at h1
    have e1 : (∑ j, (h j : ℂ) * (((⟨_, hal⟩ : Λ) : Fin (Module.finrank ℚ F) → ℂ) j *
          starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))) =
        ((m : ℝ) : ℂ) * ∑ j, (h j : ℂ) * (((e j s : ℂ) * (l₀ : Fin (Module.finrank ℚ F) → ℂ) j) *
          starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [ha, map_mul, map_intCast]; push_cast; ring
    have e2 : Algebra.trace ℚ F ((c : F) * ((a : F) * P l₀ l)) =
        (m : ℚ) * Algebra.trace ℚ F ((c : F) * s * P l₀ l) := by
      rw [ha, show (c : F) * ((m : F) * s * P l₀ l) = (m : ℚ) • ((c : F) * s * P l₀ l) by
        rw [Algebra.smul_def, map_intCast]; ring, map_smul, smul_eq_mul]
    rw [e1, e2, Complex.im_ofReal_mul] at h1
    push_cast at h1
    have hm : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm0
    apply mul_left_cancel₀ hm
    rw [h1]; ring
  set N := Submodule.span (𝓞 F) {t | ∃ l l' : Λ, t = P l l'} with hNdef
  have hN : N ≤ dualLat 𝔠 := Submodule.span_le.mpr (by rintro _ ⟨l, l', rfl⟩; exact hdual l l')
  have hN0 : N ≠ ⊥ := by
    obtain ⟨l, hl, l', hl', hne⟩ := exists_im_ne_zero hn Λ hspan h hpos
    intro hbot
    have hmem : P ⟨l, hl⟩ ⟨l', hl'⟩ ∈ N := Submodule.subset_span ⟨_, _, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    apply hne
    have := htr ⟨l, hl⟩ ⟨l', hl'⟩
    rw [hmem] at this
    simpa using this
  intro t ht
  refine dualLat_le 𝔠 c hc0 N hN0 hN (fun s hs a ha ↦ ?_) ht
  refine isIntegral_of_stab hn Λ e hspan _ (fun l₀ hl₀ ↦ ?_)
  have hx := hker (fun j ↦ (e j s : ℂ) * l₀ j) (fun l ↦ ?_) a ha
  · convert hx using 1
    funext j
    simp only [map_mul]; push_cast; ring
  · obtain ⟨m, hm⟩ := hs (P ⟨l₀, hl₀⟩ l) (Submodule.subset_span ⟨_, _, rfl⟩)
    refine ⟨m, ?_⟩
    rw [hb s ⟨l₀, hl₀⟩ l, hm]
    push_cast; ring

end GlobalTheory.RealMult.SpanDual
