import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section

namespace GlobalTheory.HeckeEx

theorem frame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  intro E _ _ _ H Dw l Xo yx zx p ψp b g Λ Λ' e e' h hΛ hhe hhe' hadd hker hψ hΛΛ' hbn hbc hb0 hbd
    Hm χl fr hH hd hn hc h0 ha Hm' χl' fr' hHH hd' hc' h0' ha' w i j hi hj
  have e0 : e 0 = 1 := hker 0 (zero_mem Λ)
  have hpow : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul, e0, pow_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have e'0 : e' 0 = 1 := by rw [← map_zero h, hψ, e0, map_one]
  have hpa : ∀ a ∈ Λ, (p : ℂ) • a ∈ Λ := fun a haa => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem haa p
  have per : ∀ a ∈ Λ, ∀ z, e (z + a) = e z := fun a haa z => by rw [hadd, hker a haa]; exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hsm : ∀ z a, hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a) = (p : ℂ) ^ 2 * hermForm Hm z a := fun z a => by
    rw [GlobalTheory.UnitFrameGen.hermForm_smul_left, GlobalTheory.UnitFrameGen.hermForm_smul_right, star_natCast]; ring
  have ho1 : ∀ V, IsOpen {z | ⊤ ≤ (e z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe V 0).1
  have ho1' : ∀ V, IsOpen {z | ⊤ ≤ (e' z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe' V 0).1
  have hch : Continuous h := h.toLinearMap.continuous_of_finiteDimensional
  have dh : Differentiable ℂ (fun z => h z) := (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable
  have dsm : Differentiable ℂ (fun z : Fin g → ℂ => (p : ℂ) • z) := differentiable_id.const_smul (p : ℂ)
  have key := GlobalTheory.UnitFrameGen.frames_eq Λ hΛ
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι =>
      {w | ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.1 ∧ ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.2})
    (fun q => ((ho1' _).preimage hch).inter ((ho1 _).preimage (continuous_const_smul (p : ℂ))))
    (fun z => by
      obtain ⟨i', hi'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e' (h z)).left
      obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e ((p : ℂ) • z)).left
      exact ⟨(i', j'), hi', hj'⟩)
    (fun q a haa z hz => by
      refine ⟨?_, ?_⟩
      · rw [hψ, per a haa, ← hψ]; exact hz.1
      · rw [smul_add, per _ (hpa a haa)]; exact hz.2)
    (fun q z => b q.1 q.2 (e z) * fr q.2 ((p : ℂ) • z)) (fun q z => fr' q.1 (h z))
    (fun q q' z => valAt' (e' (h z)).left (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun a z => Real.exp (Real.pi * (hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a)).re +
      Real.pi / 2 * (hermForm Hm ((p : ℂ) • a) ((p : ℂ) • a)).re))
    (fun q => ((hbd q.1 q.2).mono fun z hz => ⟨by rw [← hψ]; exact hz.1, by rw [← hpow]; exact hz.2⟩).mul
      ((hd q.2).comp dsm.differentiableOn fun z hz => hz.2))
    (fun q => (hd' q.1).comp dh.differentiableOn fun z hz => hz.1)
    (fun q z hz => mul_ne_zero (hbn q.1 q.2 (e z) (by rw [← hψ]; exact hz.1) (by rw [← hpow]; exact hz.2))
      (hn q.2 _ hz.2))
    (fun q q' z h1 h2 => by
      have e1 := hc q.2 q'.2 ((p : ℂ) • z) ((top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      have e2 := hbc q.1 q.2 q'.1 q'.2 (e z)
        (by rw [← hψ]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩)
        (by rw [← hpow]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      rw [hpow] at e1
      rw [hψ, e1]
      linear_combination e2 * fr q'.2 ((p : ℂ) • z))
    (fun q q' z h1 h2 => hc' q.1 q'.1 (h z) ((top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩))
    (fun q hz => by
      have z1 := hz.1
      have z2 := hz.2
      rw [map_zero] at z1
      rw [smul_zero] at z2
      rw [map_zero, smul_zero, h0' _ z1, h0 _ z2, e0]
      rw [e'0] at z1
      rw [e0] at z2
      exact hb0 q.1 q.2 z1 z2)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm _ _ _ _ _ (ha _ (hpa a haa) q.2 ((p : ℂ) • z)).1
        ((ha _ (hpa a haa) q.2 _).2 hz.2)
      rw [per a haa, smul_add, norm_mul, norm_mul, this]; ring)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm' _ _ _ _ _ (ha' _ (hΛΛ' a haa) q.1 (h z)).1
        ((ha' _ (hΛΛ' a haa) q.1 (h z)).2 hz.1)
      rw [hHH, hHH] at this
      rw [map_add, this, hsm, hsm])
  exact key (i, j) w ⟨hi, hj⟩

end GlobalTheory.HeckeEx
