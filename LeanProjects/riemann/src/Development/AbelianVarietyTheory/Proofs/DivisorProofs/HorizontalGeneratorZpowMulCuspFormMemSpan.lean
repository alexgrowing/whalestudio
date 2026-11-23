import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizGenZpowMulMemSS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpanned

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.MulSpan

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem zero_mem_SS' (X : Data E r) (la : Wt X.Ψ r) : (0 : Frame X.Ψ r → ℂ) ∈ X.SS la := by
  refine ⟨⟨⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩, 0, fun x _ => by
    simp [Data.pnorm]⟩, fun ξ _ x _ => ?_⟩
  unfold Data.fj
  split_ifs <;> simp

open Classical in

def mulAt {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) : FDSec X →ₗ[ℂ] FDSec X :=
  (LinearMap.single ℂ (fun k => Frame (X k).Ψ r → ℂ) k0) ∘ₗ (LinearMap.mulLeft ℂ h) ∘ₗ
    (LinearMap.proj (R := ℂ) (φ := fun k => Frame (X k).Ψ r → ℂ) k0)

theorem mulAt_same {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) (P : FDSec X) :
    mulAt X k0 h P k0 = fun y => h y * P k0 y := by
  simp only [mulAt, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_same, LinearMap.mulLeft_apply,
    LinearMap.proj_apply]
  rfl

open Classical in
theorem mulAt_ne {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) (P : FDSec X) {k : Comp}
    (hk : k ≠ k0) : mulAt X k0 h P k = 0 := by
  simp only [mulAt, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_of_ne hk]

theorem mulAt_mem_holSub {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ)
    (la la' : ∀ k, Wt (X k).Ψ r) (hh : ∀ Q ∈ (X k0).SS (la k0), (fun y => h y * Q y) ∈ (X k0).SS (la' k0))
    {P : FDSec X} (hP : P ∈ holSub X la) : mulAt X k0 h P ∈ holSub X la' := by
  have hle : holSub X la ≤ (holSub X la').comap (mulAt X k0 h) := by
    refine Submodule.span_le.2 fun Q hQ => ?_
    refine Submodule.subset_span (s := {P | IsHolCusp X la' P}) fun k => ?_
    by_cases hk : k = k0
    · subst hk
      rw [mulAt_same]
      exact hh _ (hQ k)
    · rw [mulAt_ne X k0 h Q hk]
      exact zero_mem_SS' _ _
  exact hle hP

theorem horizGen_zpow_mul_rdU_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (k0 : (U σ).Comp), framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} → ∀ (τ' : ((U σ).X k0).Ψ) (m : ℤ) (b b' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom b n → Dom b' n → (∀ ρ i, i < Dw.mult ρ → 1 ≤ b' (ρ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → modelWt (U σ) (wtZ b' n) k0 = modelWt (U σ) (wtZ b n) k0 + m • modelFlat r τ' → ∀ f ∈ cuspOn U Z (wtZ b n), (fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1) ∈ Submodule.span ℂ ((fun g : Rul Xo c => fun y : ↥((U σ).X k0).dom => rdU (U σ) g k0 y.1) '' (cuspOn U Z (wtZ b' n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z σ hσ k0 hk τ' m b b' n hb hb' hpos hn hw f hf
  have hP : rdU (U σ) f ∈ holSub (U σ).X (modelWt (U σ) (wtZ b n)) := (mem_cuspW.1 (cuspOn_le U Z _ hf)).2 σ hσ
  have hLP : mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) ∈
      holSub (U σ).X (modelWt (U σ) (wtZ b' n)) := by
    refine mulAt_mem_holSub _ k0 _ _ _ (fun Q hQ => ?_) hP
    rw [hw]
    refine HorizMul.horizGen_zpow_mul_mem_SS E r _ τ' _ m (hL.det σ hσ k0) (fun γ hγ => ?_) Q hQ
    rw [← hw, modelWt_wtZ, modelWt_wtZ, hL.chi σ hσ b n hb k0 γ hγ, hL.chi σ hσ b' n hb' k0 γ hγ]
  have hoff : ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k y = 0 := by
    intro k y hy
    by_cases hkk : k = k0
    · subst hkk
      have hd : y ∉ ((U σ).X k).dom := fun hd => hy (by rw [hk]; exact ⟨rfl, hd⟩)
      have h0 : rdU (U σ) f k y = 0 := by
        simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_neg, not_false_eq_true]
      rw [mulAt_same]
      simp only [h0, mul_zero]
    · rw [mulAt_ne _ _ _ _ hkk]
      rfl
  have hsp := (cuspOn_fd_and_span_rdU E H Dw l Xo c r U x hL Z σ hσ b' n hb' hpos hn).2 _ hLP hoff
  let R : FDSec (U σ).X →ₗ[ℂ] (↥((U σ).X k0).dom → ℂ) :=
    { toFun := fun Q y => Q k0 y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmap := Submodule.mem_map_of_mem (f := R) hsp
  rw [Submodule.map_span, Set.image_image] at hmap
  have e : R (mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f)) =
      fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1 := by
    funext y
    show mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k0 y.1 = _
    rw [mulAt_same]
  rw [e] at hmap
  exact hmap

end GlobalTheory.FlatCore.MulSpan
