import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ContinuousAeval
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace ChowFormHeightComparison₂.GenericDenseBound

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem finiteType_sections {K : Type} [Field K] [NumberField K] {X : Scheme.{0}} {p : X ⟶ Sp (𝓞 K)}
    (hp : IsProjOver p) {W : X.Opens} (hW : IsAffineOpen W) : Algebra.FiniteType ℤ Γ(X, W) := by
  have : IsProper p := by
    obtain ⟨N, j, _, e⟩ := hp
    have := isProper_str (𝓞 K) N
    rw [← e]
    infer_instance
  have hft : (algX p W).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩
      (show W ≤ p ⁻¹ᵁ ⊤ from le_top)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of (𝓞 K))).symm.commRingCatIsoToRingEquiv.surjective)
  have h0 : (algebraMap ℤ (𝓞 K)).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h1 := hft.comp h0
  rw [Subsingleton.elim ((algX p W).comp (algebraMap ℤ (𝓞 K))) (algebraMap ℤ Γ(X, W))] at h1
  exact RingHom.finiteType_algebraMap.1 h1

theorem final_ineq {a Q t : ℝ} {τ : ℕ} (hQ : 0 ≤ Q) (h : a ≤ Real.exp (2 * (τ : ℝ) * t) * Q ^ τ) :
    a * Real.exp (-((τ : ℝ) * Real.log Q)) ≤ Real.exp (2 * (τ : ℝ) * t) := by
  rcases hQ.eq_or_lt with h0 | h0
  · subst h0
    rw [Real.log_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact h.trans (mul_le_of_le_one_right (Real.exp_pos _).le (pow_le_one₀ le_rfl zero_le_one))
  · rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log h0, mul_inv_le_iff₀ (pow_pos h0 τ)]
    exact h

theorem norm_le_of_emb {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : GlobalTheory.HermLB p}
    {ψ : Ω →+* X.functionField} {s : W → L.B.Sec} (hM : GlobalTheory.ImageModel.IsModelOf Nm W ev d p L ψ s) (β : Ω) (τ : ℕ)
    (t : ℝ)
    (hb : ∀ (N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame Nm W b g A → ∀ (σ : K →+* ℂ) (ρ : Ω →+* ℂ),
      ρ.comp (algebraMap K Ω) = σ → ‖ρ β‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (ev (b i))) ^ τ)
    (w : W) (hw : ev w ≠ 0) (σ : 𝓞 K →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ ptsIn p σ (L.B.U k))
    (hr : RegAt (under y) (ψ β * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ)) :
    ‖ratVal (ψ β * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ) y‖ ^ 2 *
      Real.exp (-((τ : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * (τ : ℝ) * t) := by
  obtain ⟨N, n, b, g, A, c, gw, hF, -, hbc, hφ⟩ := hM.fs
  obtain ⟨U', hU', a, ha⟩ := hr.exists_fnOf
  have hyk : under y ∈ L.B.U k := mem_ptsIn.1 hy
  obtain ⟨O, hO, hyO, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (memInf hU' hyk)
  have hO' : IsAffineOpen O := hO
  have hle1 : O ≤ U' := hle.trans inf_le_left
  have hle2 : O ≤ L.B.U k := hle.trans inf_le_right
  have hyO' : y ∈ ptsIn p σ O := mem_ptsIn.2 hyO
  have hg : genericPoint X ∈ O := gen_mem hyO
  have : Nonempty O := ⟨⟨_, hyO⟩⟩
  have := finiteType_sections hM.arith.isProjOver hO'
  have := functionField_isFractionRing_of_isAffineOpen X O hO'
  have halg : ∀ z : Γ(X, O), algebraMap Γ(X, O) X.functionField z = fnOf O hg z := fun _ => rfl
  let r : Option (Fin n) → Γ(X, O) := fun j => j.elim (resG X hle1 a) fun j => resG X hle2 ((s (gw j)).f k)
  have hψw : ψ (ev w) ≠ 0 := (map_ne_zero ψ).2 hw
  set u := fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) with hu
  obtain ⟨σ', hσ', hineq⟩ := bound_of_emb (Ω := X.functionField) (ψ.comp (algebraMap K Ω)) (algX p O)
    (fun z => by
      rw [halg, RingHom.comp_apply, hM.base]
      exact (RingHom.congr_fun (fnOf_comp_algX p O hg) z).trans rfl)
    (evHom hyO') r (fun _ v => ‖v none‖ ^ 2)
    (fun σ' v => Real.exp (2 * (τ : ℝ) * t) * (∑ a, ‖∑ j, (∑ m, σ' (c j m) * A σ' m a) * v (some j)‖ ^ 2) ^ τ)
    (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun ρ => by
      have h1 := hb N n b g A hF _ (ρ.comp ψ) rfl
      have e0 : (ρ.comp ψ).comp (algebraMap K Ω) = ρ.comp (ψ.comp (algebraMap K Ω)) := rfl
      rw [e0] at h1
      generalize hσ' : ρ.comp (ψ.comp (algebraMap K Ω)) = σ' at h1 ⊢
      have hσa : ∀ z, σ' z = ρ (ψ (algebraMap K Ω z)) := fun z => by rw [← hσ']; rfl
      set lam := ρ ((ψ (ev w))⁻¹ * u) with hlam
      have e1 : ρ (algebraMap Γ(X, O) X.functionField (r none)) = ρ (ψ β) * lam ^ τ := by
        rw [halg]
        show ρ (fnOf O hg (resG X hle1 a)) = _
        rw [fnOf_resG, ha, hlam, ← map_pow ρ, ← map_mul ρ, mul_pow, mul_assoc]
      have e2 : ∀ j, ρ (algebraMap Γ(X, O) X.functionField (r (some j))) = ρ (ψ (ev (gw j))) * lam := fun j => by
        rw [halg]
        show ρ (fnOf O hg (resG X hle2 ((s (gw j)).f k))) = _
        rw [fnOf_resG, hlam, ← map_mul ρ]
        congr 1
        have := hM.ratio w (gw j) k (hle2 hg)
        rw [← mul_assoc, mul_comm (ψ (ev (gw j))), mul_assoc, eq_inv_mul_iff_mul_eq₀ hψw]
        exact this
      have e3 : ∀ m, ρ (ψ (ev (b m))) = ∑ j, σ' (c j m) * ρ (ψ (ev (gw j))) := fun m => by
        rw [hbc m]
        simp only [map_sum, map_smul, Algebra.smul_def, map_mul, hσa]
      have e4 : ∀ a, ∑ j, (∑ m, σ' (c j m) * A σ' m a) * (ρ (ψ (ev (gw j))) * lam) =
          lam * ∑ m, A σ' m a * ρ (ψ (ev (b m))) := fun a => by
        simp only [e3, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      simp only [e1, e2, e4, norm_mul, mul_pow, norm_pow, ← Finset.mul_sum]
      have hS : 0 ≤ ∑ a, ‖∑ m, A σ' m a * ρ (ψ (ev (b m)))‖ ^ 2 := by positivity
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have e5 : (Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ') (fun i => (ρ.comp ψ) (ev (b i))) ^ τ) ^ 2 =
          Real.exp (2 * (τ : ℝ) * t) * (∑ a, ‖∑ m, A σ' m a * ρ (ψ (ev (b m)))‖ ^ 2) ^ τ := by
        rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul, mul_comm τ 2, pow_mul]
        unfold GlobalTheory.Adelic.archSize
        simp only [RingHom.comp_apply]
        rw [Real.sq_sqrt hS]
        congr 2
        push_cast
        ring
      rw [e5] at h2
      have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ (‖lam‖ ^ τ) ^ 2 by positivity)
      refine h3.trans_eq ?_
      ring)
  have hσ : σ'.comp (algebraMap (𝓞 K) K) = σ := hσ'.trans (RingHom.ext fun z =>
    (ev_eq hyO' _).symm.trans (ev_algX hyO' z))
  subst hσ
  rw [hφ σ' k y, ← ha, ratVal_fnOf (mem_ptsIn.2 hU')]
  refine final_ineq (by positivity) ?_
  have f1 : evHom hyO' (r none) = GlobalTheory.CxPts.ev p _ U' a y := (ev_eq hyO' _).symm.trans (ev_res hle1 hyO' a)
  have f2 : ∀ j, evHom hyO' (r (some j)) = valR y.1 (L.B.U k) ((s (gw j)).f k) := fun j =>
    (ev_eq hyO' _).symm.trans (ev_res hle2 hyO' _)
  simp only [f1, f2] at hineq
  exact hineq

end ChowFormHeightComparison₂.GenericDenseBound
