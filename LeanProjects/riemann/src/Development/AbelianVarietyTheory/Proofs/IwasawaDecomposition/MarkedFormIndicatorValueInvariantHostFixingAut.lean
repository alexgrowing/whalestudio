import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  {T : X ≃ X} {e : LinearMap.BilinForm ℤ X ≃+ LinearMap.BilinForm ℤ X}
  (he : ∀ β y z, e β y z = β (T y) (T z))
  (hbal : ∀ β, e β ∈ balForms bar X ↔ β ∈ balForms bar X)
  (hψ : ∀ β, ψ.evalZ (e β) = ψ.evalZ β) (hlab : ∀ β, lab.evalZ (e β) = lab.evalZ β)
include he hbal hψ hlab

theorem inFace_transport (β x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab (e β) (e x) ↔ InFace bar ψ lab β x := by
  unfold InFace
  simp only [he]
  rw [hbal, ← map_add, hψ, hψ, hψ, hlab, hlab]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ Iff.rfl))
  · exact ⟨fun h y => by simpa using h (T.symm y), fun h y => h (T y)⟩
  · exact ⟨fun h y => by simpa using h (T.symm y), fun h y => h (T y)⟩

theorem isIndec_transport (β x : LinearMap.BilinForm ℤ X) :
    IsIndec bar ψ lab (e β) (e x) ↔ IsIndec bar ψ lab β x := by
  unfold IsIndec
  rw [inFace_transport he hbal hψ hlab, e.map_ne_zero_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h y z hy hz hy0 hz0 hs => ?_, fun h y z hy hz hy0 hz0 hs => ?_⟩)
  · refine h (e y) (e z) ((inFace_transport he hbal hψ hlab β y).2 hy) ((inFace_transport he hbal hψ hlab β z).2 hz)
      (e.map_ne_zero_iff.2 hy0) (e.map_ne_zero_iff.2 hz0) ?_
    rw [← map_add, hs]
  · refine h (e.symm y) (e.symm z) ?_ ?_ ?_ ?_ ?_
    · rw [← inFace_transport he hbal hψ hlab, e.apply_symm_apply]; exact hy
    · rw [← inFace_transport he hbal hψ hlab, e.apply_symm_apply]; exact hz
    · exact fun h0 => hy0 (by rw [← e.apply_symm_apply y, h0, map_zero])
    · exact fun h0 => hz0 (by rw [← e.apply_symm_apply z, h0, map_zero])
    · apply e.injective; rw [map_add, e.apply_symm_apply, e.apply_symm_apply, hs]

theorem isMarked_transport_of (β : LinearMap.BilinForm ℤ X) (h : IsMarked bar ψ lab i X β) :
    IsMarked bar ψ lab i X (e β) := by
  obtain ⟨hb, hn, hp, hl, S, hS, k, hk, hsum⟩ := h
  refine ⟨(hbal β).2 hb, fun y => by rw [he]; exact hn _, fun k' β' h' => hp k' (e.symm β') ?_, by rw [hlab]; exact hl,
    S.map e.toEquiv.toEmbedding, fun x => ?_, k, hk, ?_⟩
  · apply e.injective; rw [map_zsmul, e.apply_symm_apply, h']
  · rw [Finset.mem_map_equiv, hS, ← isIndec_transport he hbal hψ hlab]
    show IsIndec bar ψ lab (e β) (e (e.symm x)) ↔ _
    rw [e.apply_symm_apply]
  · rw [Finset.sum_map, ← map_zsmul, hsum, map_sum]; rfl

theorem isMarked_transport (β : LinearMap.BilinForm ℤ X) :
    IsMarked bar ψ lab i X (e β) ↔ IsMarked bar ψ lab i X β := by
  refine ⟨fun h => ?_, isMarked_transport_of he hbal hψ hlab β⟩
  have := isMarked_transport_of (T := T.symm) (e := e.symm) (fun β y z => ?_) (fun β => ?_) (fun β => ?_)
    (fun β => ?_) (e β) h
  · simpa using this
  · have := he (e.symm β) (T.symm y) (T.symm z); simp only [AddEquiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  · rw [← hbal, e.apply_symm_apply]
  · rw [← hψ, e.apply_symm_apply]
  · rw [← hlab, e.apply_symm_apply]

end Transport

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def twPi (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) : (Fin n → 𝓞 E) ≃+ (Fin n → 𝓞 E) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

@[simp] theorem twPi_apply (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) (a : Fin n → 𝓞 E) : twPi σ n a = fun j => σ (a j) := rfl

def twForm (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → 𝓞 E) ≃+ LinearMap.BilinForm ℤ (Fin n → 𝓞 E) where
  toFun β := β.compl₁₂ (twPi σ n).toIntLinearEquiv.toLinearMap (twPi σ n).toIntLinearEquiv.toLinearMap
  invFun β := β.compl₁₂ (twPi σ.symm n).toIntLinearEquiv.toLinearMap (twPi σ.symm n).toIntLinearEquiv.toLinearMap
  left_inv β := LinearMap.ext₂ fun a b => by simp
  right_inv β := LinearMap.ext₂ fun a b => by simp
  map_add' _ _ := LinearMap.ext₂ fun a b => by simp

@[simp] theorem twForm_apply (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) (a b : Fin n → 𝓞 E) :
    twForm σ n β a b = β (fun j => σ (a j)) (fun j => σ (b j)) := rfl

end Twist

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem twForm_mem_balForms (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} {β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)}
    (h : β ∈ balForms H.bar (Fin n → 𝓞 E)) : twForm σ n β ∈ balForms H.bar (Fin n → 𝓞 E) := by
  refine ⟨fun y z => by simp only [twForm_apply]; exact h.1 _ _, fun a y z => ?_⟩
  simp only [twForm_apply]
  have e1 : (fun j => σ ((a • y) j)) = σ a • fun j => σ (y j) := funext fun j => by simp
  have e2 : (fun j => σ ((H.bar a • z) j)) = H.bar (σ a) • fun j => σ (z j) := funext fun j => by
    simp [host_bar_map_comm]
  rw [e1, e2]
  exact h.2 _ _ _

theorem twForm_symm_twForm (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) :
    twForm σ.symm n (twForm σ n β) = β := LinearMap.ext₂ fun a b => by simp

theorem twForm_mem_balForms_iff (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) :
    twForm σ n β ∈ balForms H.bar (Fin n → 𝓞 E) ↔ β ∈ balForms H.bar (Fin n → 𝓞 E) :=
  ⟨fun h => by simpa [twForm_symm_twForm] using twForm_mem_balForms H σ.symm h, twForm_mem_balForms H σ⟩

theorem evalZ_twForm {H : Host E} {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) {σ : 𝓞 E ≃+* 𝓞 E} (hσ : σ H.w0 = H.w0)
    {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) : φ.evalZ (twForm σ n β) = φ.evalZ β := by
  unfold InvFun.evalZ
  rw [InvFun.eval_pi, InvFun.eval_pi]
  exact hφ σ hσ n fun a b => (β a b : ℝ)

theorem markVal_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ lab : InvFun (𝓞 E))
    (i : ℕ), IsTwInv H ψ → IsTwInv H lab → ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 →
    ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
      markVal H.bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal H.bar ψ lab i n B := by
  intro E _ _ _ H ψ lab i hψ hlab σ hσ n B
  classical
  unfold markVal
  by_cases h2 : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b, B a b = β a b
  · have h1 : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b, B (fun j => σ (a j)) (fun j => σ (b j)) = β a b :=
      ⟨twForm σ n h2.choose, fun a b => h2.choose_spec _ _⟩
    rw [dif_pos h1, dif_pos h2]
    have e : h1.choose = twForm σ n h2.choose := LinearMap.ext₂ fun a b => by
      have := (h1.choose_spec a b).symm.trans (h2.choose_spec _ _)
      exact_mod_cast this
    rw [e, isMarked_transport (T := (twPi σ n).toEquiv) (fun _ _ _ => rfl) (twForm_mem_balForms_iff H σ)
      (evalZ_twForm hψ hσ) (evalZ_twForm hlab hσ)]
  · have h1 : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b,
        B (fun j => σ (a j)) (fun j => σ (b j)) = β a b := fun ⟨β, hβ⟩ =>
      h2 ⟨twForm σ.symm n β, fun a b => by
        have := hβ (fun j => σ.symm (a j)) (fun j => σ.symm (b j))
        simpa using this⟩
    rw [dif_neg h1, dif_neg h2]

example (H : Host E) (i n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    markVal H.bar (zeroFun (𝓞 E)) (zeroFun (𝓞 E)) i n (fun a b => B (fun j => (RingEquiv.refl _) (a j))
      (fun j => (RingEquiv.refl _) (b j))) = markVal H.bar (zeroFun (𝓞 E)) (zeroFun (𝓞 E)) i n B :=
  markVal_twist E H _ _ i (fun _ _ _ _ => by simp [zeroFun]) (fun _ _ _ _ => by simp [zeroFun]) _ rfl n B

end Main

end GlobalTheory.PolFan.Mark
