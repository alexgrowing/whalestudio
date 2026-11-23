import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionNeZeroAtDivisionPointSelfDualStatement

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate Classical

namespace GlobalTheory.Dict.ThetaHalf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem EF_inv_smul (X : Data E r) (M : ℕ) (u v : Fin r → E) :
    EF X ((M : E)⁻¹ • u) v = (M : ℚ)⁻¹ * EF X u v := by
  have h : (M : E)⁻¹ • u = (M : ℚ)⁻¹ • u := by
    funext j
    simp [Rat.smul_def]
  rw [h, TensLat.EF_eq_bilin, TensLat.EF_eq_bilin, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem mem_smul_iff (X : Data E r) {L : Lt E r} (hL : SelfD X L) {𝔪 : Ideal (𝓞 E)} {M : ℕ}
    (hM : M ≠ 0) (h𝔪 : 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)}) (x : Fin r → E) :
    x ∈ 𝔪 • L ↔ ∀ y ∈ 𝔪 • L, ∃ k : ℤ, (M : ℚ)⁻¹ * EF X x y = k := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hcc : ∀ a : E, cc (cc a) = a := fun a => IsCMField.complexConj_apply_apply E a
  constructor
  · intro hx y hy
    refine Submodule.smul_induction_on hx (fun a ha u hu => ?_) fun x₁ x₂ h₁ h₂ => ?_
    · refine Submodule.smul_induction_on hy (fun b hb v hv => ?_) fun y₁ y₂ h₁ h₂ => ?_
      · let b' : 𝓞 E := ⟨cc (b : E), Base.isIntegral_cc b.isIntegral_coe⟩
        have hb' : b' ∈ conjI 𝔪 := Ideal.subset_span ⟨b, hb, rfl⟩
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (h𝔪 ▸ Ideal.mul_mem_mul ha hb')
        have ht' : (t : E) * M = a * cc (b : E) := by
          have h5 := congrArg (algebraMap (𝓞 E) E) ht
          rw [map_mul, map_mul, map_natCast] at h5
          exact h5
        obtain ⟨k, hk⟩ := (hL.2 _).1 (L.smul_mem t hu) v hv
        refine ⟨k, ?_⟩
        rw [← hk, ← EF_inv_smul]
        change EF X ((M : E)⁻¹ • (a : E) • u) ((b : E) • v) = EF X ((t : E) • u) v
        rw [← hcc (b : E), ← TensLat.EF_smul, smul_smul, smul_smul]
        congr 2
        field_simp
        linear_combination -ht'
      · obtain ⟨k₁, h₁⟩ := h₁
        obtain ⟨k₂, h₂⟩ := h₂
        refine ⟨k₁ + k₂, ?_⟩
        rw [Int.cast_add, ← h₁, ← h₂]
        simp only [TensLat.EF_eq_bilin, map_add, mul_add]
    · obtain ⟨k₁, h₁⟩ := h₁
      obtain ⟨k₂, h₂⟩ := h₂
      refine ⟨k₁ + k₂, ?_⟩
      rw [Int.cast_add, ← h₁, ← h₂]
      simp only [TensLat.EF_eq_bilin, map_add, mul_add, LinearMap.add_apply]
  · intro h
    have h1 : ∀ b ∈ conjI 𝔪, b • (M : E)⁻¹ • x ∈ L := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨a, ha, hb⟩ := hb
        refine (hL.2 _).2 fun u hu => ?_
        obtain ⟨k, hk⟩ := h _ (Submodule.smul_mem_smul ha hu)
        refine ⟨k, ?_⟩
        change EF X ((b : E) • (M : E)⁻¹ • x) u = k
        rw [hb, TensLat.EF_smul, hcc, EF_inv_smul]
        exact hk
      | zero => simp
      | add a b _ _ ha hb => rw [add_smul]; exact L.add_mem ha hb
      | smul t a _ ha => rw [smul_eq_mul, mul_smul]; exact L.smul_mem t ha
    have h2 : ∀ c ∈ 𝔪 * conjI 𝔪, c • (M : E)⁻¹ • x ∈ 𝔪 • L := by
      intro c hc
      refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun c₁ c₂ h₁ h₂ => ?_
      · rw [mul_smul]; exact Submodule.smul_mem_smul ha (h1 b hb)
      · rw [add_smul]; exact add_mem h₁ h₂
    have h3 := h2 M (h𝔪 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (M : 𝓞 E) • (M : E)⁻¹ • x = x := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hME,
        one_smul]
    rwa [h4] at h3

theorem span_smul (X : Data E r) {L : Lt E r} (hL : SelfD X L) {𝔪 : Ideal (𝓞 E)} {M : ℕ}
    (hM : M ≠ 0) (h𝔪 : 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)}) :
    Submodule.span E ((𝔪 • L : Lt E r) : Set (Fin r → E)) = ⊤ := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMm : (M : 𝓞 E) ∈ 𝔪 := by
    refine Ideal.mul_le_left (J := conjI 𝔪) ?_
    rw [h𝔪]
    exact Ideal.mem_span_singleton_self _
  rw [eq_top_iff, ← TensLat.span_of_selfD X hL, Submodule.span_le]
  intro u hu
  have h1 : (M : E)⁻¹ • (M : 𝓞 E) • u = u := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hME,
      one_smul]
  have h2 : (M : 𝓞 E) • u ∈ 𝔪 • L := Submodule.smul_mem_smul hMm hu
  have h3 := Submodule.smul_mem _ (M : E)⁻¹ (Submodule.subset_span (R := E) h2)
  rw [h1] at h3
  exact h3

theorem exists_ne_zero_of_scaled {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {g : ℕ} (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)) (hp : Function.Injective p)
    (L : Submodule ℤ V) (hfg : L.FG) {M : ℕ} (hM : 2 ≤ M)
    (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, (M : ℚ)⁻¹ * B x y = k)
    (hsp : Submodule.span ℝ (p '' (L : Set V)) = ⊤) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hB : ∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) (c : V → ℂ)
    (hc : ∀ v, ‖c v‖ = 1) {f : (Fin g → ℂ) → ℂ} (hd : Differentiable ℂ f) (h0 : f ≠ 0)
    (hf : ∀ v ∈ L, ∀ z, f (z + p v) = (c v * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
      Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) :
    ∃ v ∈ L, f ((M : ℂ)⁻¹ • p v) ≠ 0 := by
  have hM0 : M ≠ 0 := by omega
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have hMR : (0 : ℝ) < (M : ℝ)⁻¹ := by positivity
  have hsc : ∀ z u : Fin g → ℂ, z ⬝ᵥ ((M : ℝ)⁻¹ • Hm).mulVec u = (M : ℝ)⁻¹ • (z ⬝ᵥ Hm.mulVec u) :=
    fun z u => by rw [smul_mulVec, dotProduct_smul]
  refine GlobalTheory.T.thetaFunction_ne_zero_at_divisionPoint_selfDual V g ((M : ℚ)⁻¹ • B) p hp L hfg hL hsp ((M : ℝ)⁻¹ • Hm) ?_ (fun z hz => ?_)
    (fun u v => ?_) c hc M hM f hd h0 fun v hv z => ?_
  · ext i j
    rw [conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, star_smul, hH.apply, star_trivial]
  · rw [hsc, smul_re, smul_eq_mul]
    exact mul_pos hMR (hpos z hz)
  · rw [hsc, smul_im, LinearMap.smul_apply, LinearMap.smul_apply, hB]
    simp
  · rw [hf v hv z, hsc, hsc]
    congr 3
    simp only [real_smul]
    push_cast
    field_simp

theorem exists_ne_zero_on_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ (w : E) (L : Lt E r), SelfD X L → ∀ x ∈ X.dom, ∀ (𝔪 : Ideal (𝓞 E)) (M : ℕ), 2 ≤ M → 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)} → ∀ ϑ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L ϑ → ϑ ≠ 0 → ∃ u ∈ 𝔪 • L, ϑ (pv X idx x ((M : E)⁻¹ • u)) ≠ 0 := by
  intro E _ _ _ r X g bas idx hs w L hL x hx' 𝔪 M hM h𝔪 θ hθ h0
  have hM0 : M ≠ 0 := by omega
  obtain ⟨hconj, hpos, him, -, hsm, hinj, hspan, -⟩ :=
    GlobalTheory.Dict.hx_laws E r X g bas idx 0 hs Even.zero x hx'
  set Hm := (hMat X bas idx x)ᵀ * imInv X bas idx x * (hMat X bas idx x).map star with hHm
  have hform : ∀ z u, hx X bas idx x z u = z ⬝ᵥ Hm.mulVec (star u) := fun z u =>
    SiegelNormalForm.form_pull _ _ z u
  have hH : Hm.IsHermitian := by
    ext i j
    have := hconj (Pi.single j 1) (Pi.single i 1)
    rw [hform, hform, SiegelNormalForm.form_single, SiegelNormalForm.form_single] at this
    exact this.symm
  clear_value Hm
  let p : (Fin r → E) →ₗ[ℤ] (Fin g → ℂ) := (AddMonoidHom.mk' (pv X idx x) fun u v => by
    unfold pv; rw [per_add]; rfl).toIntLinearMap
  have hp : ∀ v, p v = pv X idx x v := fun _ => rfl
  have hne : ∀ v, eps1 X w v ≠ 0 := fun v => Complex.exp_ne_zero _
  have key : ∀ v ∈ L, ∀ z, θ (z + p v) =
      ((eps1 X w v)⁻¹ * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
      Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * θ z := by
    intro v hv z
    have h1 := congrFun (hθ.2 v hv) z
    simp only [Pi.smul_apply, smul_eq_mul, fock, hform, add_dotProduct, smul_dotProduct] at h1
    rw [← h1, ← hp, _root_.mul_mul_mul_comm, inv_mul_cancel₀ (hne v), _root_.one_mul,
      ← _root_.mul_assoc, ← Complex.exp_add]
    refine (_root_.one_mul _).symm.trans ?_
    congr 1
    refine Complex.exp_zero.symm.trans (congrArg _ ?_)
    push_cast
    ring
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_scaled (traceFormBilin (X.κ0 / 2) X.Gm) p hinj
    ((𝔪 • L).restrictScalars ℤ)
    (Submodule.FG.of_le hL.1 (Submodule.smul_le_right (I := 𝔪))).restrictScalars hM
    (fun u => by simp only [← TensLat.EF_eq_bilin]; exact mem_smul_iff X hL hM0 h𝔪 u)
    (hspan _ (span_smul X hL hM0 h𝔪)).1 hH (fun z hz => hform z z ▸ hpos z hz)
    (fun u v => by rw [← TensLat.EF_eq_bilin, ← him, hform, hp, hp])
    (fun v => (eps1 X w v)⁻¹)
    (fun v => by
      have : eps1 X w v = cexp ((Real.pi * (EF X v (w • v) : ℚ) : ℝ) * I) := by
        unfold eps1; congr 1; push_cast; ring
      rw [norm_inv, this, Complex.norm_exp_ofReal_mul_I, inv_one])
    hθ.1 h0 (fun v hv => key v (Submodule.smul_le_right (I := 𝔪) hv))
  refine ⟨u, hu, ?_⟩
  have e : pv X idx x ((M : E)⁻¹ • u) = (M : ℂ)⁻¹ • p u := by
    rw [hsm]
    funext j
    rw [map_inv₀, map_natCast, hp, Pi.smul_apply, smul_eq_mul]
  rwa [e]

end GlobalTheory.Dict.ThetaHalf
