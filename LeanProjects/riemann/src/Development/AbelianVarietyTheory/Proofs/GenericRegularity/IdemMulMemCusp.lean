import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs

noncomputable section

namespace GlobalTheory.Reg.IdemCusp

section Model

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsIdemFn (X : Data E r) (χ : Frame X.Ψ r → ℂ) : Prop :=
  (∀ x ∈ X.dom, χ x = 0 ∨ χ x = 1) ∧ DifferentiableOn ℂ χ X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, χ (rmul x b) = χ x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, χ (lact γ x) = χ x

theorem flow_const (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℝ) :
    χ (X.flow ξ (fun τ => (s τ : ℂ)) x) = χ x := by
  have hpath : Continuous fun t : ℝ => CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x :=
    ((CuspCoefficientFlow.cont_flowL X ξ).comp
      (continuous_pi fun τ => continuous_id.mul continuous_const)).clm_apply continuous_const
  have hin : ∀ t : ℝ, CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x ∈ X.dom := fun t => by
    rw [CuspCoefficientFlow.flowL_apply]
    exact (FlowCoefficientBounds.flow_real X hξ hx (fun τ => t * s τ) 0).1
  set g : ℝ → ℂ := fun t => χ (CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x) with hg
  have hcont : Continuous g := hχ.2.1.continuousOn.comp_continuous hpath hin
  have hzo : ∀ t : ℝ, g t = 0 ∨ g t = 1 := fun t => hχ.1 _ (hin t)

  have hre : Continuous fun t => (g t).re := Complex.continuous_re.comp hcont
  have hsame : g 1 = g 0 := by
    by_contra hne
    have hhalf : (1 / 2 : ℝ) ∈ Set.uIcc (g 0).re (g 1).re := by
      rcases hzo 0 with h0 | h0 <;> rcases hzo 1 with h1 | h1 <;>
        simp_all <;> norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hre.continuousOn hhalf
    rcases hzo t with h | h <;> simp [h] at ht
  have h1 : g 1 = χ (X.flow ξ (fun τ => (s τ : ℂ)) x) := by
    simp only [hg, CuspCoefficientFlow.flowL_apply, one_mul]
  have h0 : g 0 = χ x := by
    simp only [hg, CuspCoefficientFlow.flowL_apply, zero_mul, Complex.ofReal_zero]
    exact congrArg χ (EmbeddingHermitianPairs.flow_zero X ξ x)
  rw [← h1, hsame, h0]

theorem fj_mul (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ) (la : Wt X.Ψ r)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj la ξ 0 (χ * P) x = χ x * X.fj la ξ 0 P x := by
  unfold Data.fj
  split_ifs
  · simp only [Pi.mul_apply, flow_const X hχ hξ hx, mul_assoc, integral_const_mul]
    ring
  · simp
  · simp

theorem mul_mem_SS (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : χ * P ∈ X.SS la := by
  simp only [Data.SS, Set.mem_ofPred_eq] at hP ⊢
  obtain ⟨⟨⟨hd, hB, hΓ⟩, C, hC⟩, hcusp⟩ := hP
  refine ⟨⟨⟨hχ.2.1.mul hd, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, C, fun x hx => ?_⟩,
    fun ξ hξ x hx => ?_⟩
  · simp only [Pi.mul_apply]
    rw [hχ.2.2.1 x hx b hb, hB x hx b hb]
    ring
  · simp only [Pi.mul_apply]
    rw [hχ.2.2.2 γ hγ x hx, hΓ γ hγ x hx]
    ring
  · have hnorm : X.pnorm la (χ * P) x = ‖χ x‖ * X.pnorm la P x := by
      simp only [Data.pnorm, Pi.mul_apply, norm_mul, mul_assoc]
    have h1 : ‖χ x‖ ≤ 1 := by
      rcases hχ.1 x hx with h | h <;> simp [h]
    have h0 : 0 ≤ X.pnorm la P x := by
      unfold Data.pnorm
      positivity
    rw [hnorm]
    exact (mul_le_of_le_one_left h0 h1).trans (hC x hx)
  · rw [fj_mul X hχ la hξ P hx, hcusp ξ hξ x hx, mul_zero]

def mulL {ι : Type} (X : ι → Data E r) (χ : Formalism.L2.PjFree.FDSec X) :
    Formalism.L2.PjFree.FDSec X →ₗ[ℂ] Formalism.L2.PjFree.FDSec X where
  toFun P := fun k => χ k * P k
  map_add' P Q := by
    funext k x
    simp [mul_add]
  map_smul' a P := by
    funext k x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem mul_mem_holSub {ι : Type} (X : ι → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    (χ : Formalism.L2.PjFree.FDSec X) (hχ : ∀ k, IsIdemFn (X k) (χ k)) {P : Formalism.L2.PjFree.FDSec X}
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) : (fun k => χ k * P k) ∈ Formalism.L2.PjFree.holSub X la := by
  have hle : (Formalism.L2.PjFree.holSub X la).map (mulL X χ) ≤ Formalism.L2.PjFree.holSub X la := by
    unfold Formalism.L2.PjFree.holSub
    rw [Submodule.map_span_le]
    intro Q hQ
    exact Submodule.subset_span fun k => mul_mem_SS (X k) (hχ k) (la k) (hQ k)
  exact hle (Submodule.mem_map_of_mem hP)

theorem chi_zero (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  have hsq : X.χ 0 γ * X.χ 0 γ = X.χ 0 γ := by
    have h := X.χ_add 0 0 γ hγ
    rw [add_zero] at h
    exact h.symm
  obtain ⟨n, hn, hpow⟩ := X.χ_fin 0
  have hne : X.χ 0 γ ≠ 0 := by
    intro h0
    have h := hpow γ hγ
    rw [h0, zero_pow hn.ne'] at h
    exact zero_ne_one h
  exact mul_left_cancel₀ hne (by rw [hsq, mul_one])

theorem isIdemFn_of_isSec (X : Data E r) {χ : Frame X.Ψ r → ℂ} (h : X.IsSec 0 χ) (hi : χ * χ = χ) :
    IsIdemFn X χ := by
  obtain ⟨hd, hB, hΓ⟩ := h
  refine ⟨fun x _ => ?_, hd, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hx2 : χ x * χ x = χ x := congrFun hi x
    by_cases h0 : χ x = 0
    · exact Or.inl h0
    · exact Or.inr (mul_left_cancel₀ h0 (by rw [hx2, mul_one]))
  · rw [hB x hx b hb]
    simp [bchar]
  · rw [hΓ γ hγ x hx, chi_zero X hγ, one_mul]

end Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

section Read

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem rdU_mul (U : Formalism.L2.PjFree.Unf Xo c σ r) (f g : Rul Xo c) :
    Formalism.L2.PjFree.rdU U (f * g) = fun k => Formalism.L2.PjFree.rdU U f k * Formalism.L2.PjFree.rdU U g k := by
  funext k x
  simp only [Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply]
  by_cases h : x ∈ (U.X k).dom
  · simp only [dif_pos h]
    unfold Formalism.L2.PjFree.toC evR evalAt
    split_ifs with h1
    · exact map_mul _ _ _
    · exact (mul_zero _).symm
  · simp only [dif_neg h, mul_zero]

theorem laU_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) : Formalism.L2.PjFree.laU U 0 0 k = 0 := by
  unfold Formalism.L2.PjFree.laU
  funext τ j
  simp

end Read

theorem idem_mul_mem_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ χ ∈ sec Xo c 0 0, χ * χ = χ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, χ * g ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  intro E _ _ _ H Dw l Xo c r U hU χ hχ hi a n g hg
  have hχ' := hχ
  unfold sec secW at hχ'
  obtain ⟨hχn, hχw⟩ := hχ'
  unfold Formalism.L2.PjFree.cusp at hg ⊢
  obtain ⟨hgs, hgc⟩ := Submodule.mem_inf.mp hg
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  ·
    have hgs' := hgs
    unfold sec secW at hgs' ⊢
    obtain ⟨hgn, hgw⟩ := hgs'
    refine ⟨fun p q φ y z hyz => ?_, fun p t y y' hyy => ?_⟩
    · show χ q z * g q z = φ (χ p y * g p y)
      rw [hχn p q φ y z hyz, hgn p q φ y z hyz, map_mul]
    · show χ p y' * g p y' = _ * (χ p y * g p y)
      rw [hχw p t y y' hyy, hgw p t y y' hyy]
      have h1 : wchar (ex Dw 0 0) t = 1 := by simp [wchar, ex]
      rw [h1]
      ring
  ·
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hgc ⊢
    intro σ hσ
    have hsec := (hU σ hσ).2.2.2.2.1 0 0 (by unfold Formalism.L2.Pj.Dom; simp [antitone_const]) χ hχ
    rw [rdU_mul]
    refine mul_mem_holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (Formalism.L2.PjFree.rdU (U σ) χ)
      (fun k => ?_) (hgc σ hσ)
    apply isIdemFn_of_isSec
    · have hk := hsec k
      rwa [laU_zero] at hk
    · have hk := congrFun (rdU_mul (U σ) χ χ) k
      rw [hi] at hk
      exact hk.symm

end GlobalTheory.Reg.IdemCusp
