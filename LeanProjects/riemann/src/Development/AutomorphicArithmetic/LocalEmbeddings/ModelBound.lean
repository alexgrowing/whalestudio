import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteTypeStatement
import Development.AutomorphicArithmetic.DivisorFrames.ComplexPointsDenseOpen
import Development.AutomorphicArithmetic.DivisorFrames.ExistsOpenComplexPointsAlgebra

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.CompHt GlobalTheory.ChowHt

namespace GlobalTheory.ImageModel

private theorem ratVal_pow' {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {y : CxPts p σ} {f : X.functionField} (hf : RegAt (under y) f) (n : ℕ) :
    RegAt (under y) (f ^ n) ∧ ratVal (f ^ n) y = ratVal f y ^ n := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn p σ U := mem_ptsIn.2 hU
  rw [← map_pow, ratVal_fnOf hy, ratVal_fnOf hy, ev_eq hy, ev_eq hy]
  exact ⟨regAt_fnOf hU _ _, map_pow _ _ _⟩

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω]

theorem IsModelOf.bound {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V} {e : V →ₗ[K] Ω} {D : ℕ}
    {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : HermLB p} {ψ : Ω →+* X.functionField}
    {s : W → L.B.Sec} (hM : IsModelOf Nm W e D p L ψ s) (R : Subalgebra K Ω) (hR : Algebra.FiniteType K R)
    {c F : Ω} {τ : ℕ} {C : ℝ} (hc0 : c ≠ 0) (hτ : τ ≠ 0) (hC : 0 ≤ C) (hc : ∀ v, c * e v ∈ R) (hF : c ^ τ * F ∈ R)
    (σ : K →+* ℂ)
    (hbd : ∀ (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame Nm W b g A → ∀ φ : R →+* ℂ,
      φ.comp (algebraMap K R) = σ →
      ‖φ ⟨_, hF⟩‖ ^ 2 ≤ C * (∑ a, ‖∑ m, A σ m a * φ ⟨_, hc (b m)⟩‖ ^ 2) ^ τ)
    (w : W) (hw : e w ≠ 0) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K))) (k : L.B.ι)
    (hy : y ∈ ptsIn p _ (L.B.U k))
    (hreg : RegAt (under y) (ψ F * (ψ (e w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ)) :
    ‖ratVal (ψ F * (ψ (e w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ) y‖ ^ 2 *
      Real.exp (-((τ : ℝ) * (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ k y)) ≤ C := by
  obtain ⟨N, n, b, g, A, cc, gw, hfr, -, hb, hφ⟩ := hM.fs
  haveI := GlobalTheory.T.locallyOfFiniteType_of_isProjOver _ _ p hM.arith.isProjOver
  obtain ⟨V₁, hV₁, hV⟩ := UpperTheory.exists_open_complex_points_algebra K Ω X p ψ hM.base R hR
  have h := gen_mem (mem_ptsIn.1 hy)
  have hψw : ψ (e w) ≠ 0 := (map_ne_zero ψ).2 hw
  have hψc : ψ c ≠ 0 := (map_ne_zero ψ).2 hc0
  let u : X.functionField := (ψ c)⁻¹ * (ψ (e w))⁻¹ * fnOf (L.B.U k) h ((s w).f k)
  obtain ⟨V₂, hV₂, ua, hua⟩ := (regAt_genericPoint u).exists_fnOf
  obtain ⟨V₃, hV₃, γ, hγ⟩ := hreg.exists_fnOf
  have hγu : fnOf V₃ (gen_mem hV₃) γ = ψ (c ^ τ * F) * u ^ τ := by
    rw [hγ, map_mul, map_pow]
    simp only [u, mul_pow, inv_pow]
    field_simp
  have hsu : ∀ i, fnOf (L.B.U k) h ((s (gw i)).f k) = ψ (c * e (gw i)) * u := fun i => by
    have := hM.ratio (gw i) w k h
    rw [map_mul]
    simp only [u]
    field_simp
    linear_combination -this
  let S : CxPts p (σ.comp (algebraMap (𝓞 K) K)) → ℝ := fun y' =>
    ∑ a, ‖∑ i, (∑ m, σ (cc i m) * A σ m a) * ev p _ (L.B.U k) ((s (gw i)).f k) y'‖ ^ 2
  have key : ∀ y' ∈ ptsIn p (σ.comp (algebraMap (𝓞 K) K)) (V₃ ⊓ L.B.U k) ∩ ptsIn p _ (V₁ ⊓ V₂),
      ‖ev p _ V₃ γ y'‖ ^ 2 ≤ C * S y' ^ τ := by
    rintro y' ⟨h1, h2⟩
    obtain ⟨h3, hk⟩ := mem_ptsIn_inf.1 h1
    obtain ⟨h1', h2'⟩ := mem_ptsIn_inf.1 h2
    obtain ⟨φ, hφσ, hφv⟩ := hV σ y' h1'
    have hu : RegAt (under y') u := hua ▸ regAt_fnOf (mem_ptsIn.1 h2') _ _
    obtain ⟨hup, hupv⟩ := ratVal_pow' hu τ
    have e1 : ev p _ V₃ γ y' = φ ⟨_, hF⟩ * ratVal u y' ^ τ := by
      rw [← ratVal_fnOf h3 (gen_mem hV₃), hγu, ratVal_mul (hφv ⟨_, hF⟩).1 hup, hupv, ← (hφv ⟨_, hF⟩).2]
    have e2 : ∀ i, ev p _ (L.B.U k) ((s (gw i)).f k) y' = φ ⟨_, hc (gw i)⟩ * ratVal u y' := fun i => by
      rw [← ratVal_fnOf hk h, hsu, ratVal_mul (hφv ⟨_, hc (gw i)⟩).1 hu, ← (hφv ⟨_, hc (gw i)⟩).2]
    have e3 : ∀ m, φ ⟨_, hc (b m)⟩ = ∑ i, σ (cc i m) * φ ⟨_, hc (gw i)⟩ := fun m => by
      have : (⟨_, hc (b m)⟩ : R) = ∑ i, algebraMap K R (cc i m) * ⟨_, hc (gw i)⟩ := by
        apply Subtype.ext
        simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubalgebraClass.coe_algebraMap]
        rw [hb m, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, Algebra.smul_def]; ring
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hφσ]; rfl
    have e4 : S y' = (∑ a, ‖∑ m, A σ m a * φ ⟨_, hc (b m)⟩‖ ^ 2) * ‖ratVal u y'‖ ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← mul_pow, ← norm_mul]
      congr 2
      simp only [e2, e3, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e4, norm_mul, mul_pow, mul_pow, norm_pow, ← pow_mul, ← pow_mul, mul_comm τ 2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbd N n b g A hfr φ hφσ) (by positivity)
  have hyT : y ∈ ptsIn p (σ.comp (algebraMap (𝓞 K) K)) (V₃ ⊓ L.B.U k) := mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hV₃, hy⟩
  have hd := UpperTheory.complex_points_dense_open K X p σ (V₁ ⊓ V₂) ⟨_, memInf (gen_mem hV₁.choose_spec) hV₂⟩
  have hcl := hd.open_subset_closure_inter (isOpen_ptsIn _) hyT
  have c1 : ContinuousAt (ev p _ V₃ γ) y :=
    (continuousOn_ev γ).continuousAt ((isOpen_ptsIn _).mem_nhds (mem_ptsIn.2 hV₃))
  have c2 : ∀ i, ContinuousAt (ev p _ (L.B.U k) ((s (gw i)).f k)) y := fun i =>
    (continuousOn_ev _).continuousAt ((isOpen_ptsIn _).mem_nhds hy)
  have c3 : ContinuousAt S y := tendsto_finset_sum _ fun a _ =>
    ((tendsto_finset_sum _ fun i _ => (c2 i).tendsto.const_mul _).norm.pow 2)
  have hle : ‖ev p _ V₃ γ y‖ ^ 2 ≤ C * S y ^ τ :=
    ContinuousWithinAt.closure_le hcl (c1.norm.pow 2).continuousWithinAt
      (continuousAt_const.mul (c3.pow τ)).continuousWithinAt key
  have hS : (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ k y = Real.log (S y) := hφ σ k y
  have hS0 : 0 ≤ S y := Finset.sum_nonneg fun _ _ => by positivity
  rw [← hγ, ratVal_fnOf (mem_ptsIn.2 hV₃), hS]
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0, zero_pow hτ, mul_zero] at hle
    rw [le_antisymm hle (by positivity), zero_mul]
    exact hC
  · rw [← Real.log_pow, Real.exp_neg, Real.exp_log (pow_pos h0 τ), ← div_eq_mul_inv, div_le_iff₀ (pow_pos h0 τ)]
    exact hle

end GlobalTheory.ImageModel
