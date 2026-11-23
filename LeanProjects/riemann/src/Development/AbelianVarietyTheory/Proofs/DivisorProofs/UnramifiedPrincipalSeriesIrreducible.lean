import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesIrreducibleUnramStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParametersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepUnitaryTwistExistsStatement

noncomputable section

open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.JSPrinBound

open GlobalTheory.SmGL GlobalTheory.CuspRep

theorem exists_map_of_subquotient {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ G V} {Q : Representation ℂ G W}
    {σ : Representation ℂ G U} (hρ : ρ.IsIrreducible) (hQ : GlobalTheory.SmGL.IsSubquotient Q ρ) (f : Q.IntertwiningMap σ)
    (hf : f ≠ 0) : ∃ F : V →ₗ[ℂ] U, F ≠ 0 ∧ ∀ g v, F (ρ g v) = σ g (F v) := by
  obtain ⟨S, g, hg⟩ := hQ
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (DFunLike.ext _ _ fun y => by simpa using h y)
  obtain ⟨x, rfl⟩ := hg y
  have hS : S = ⊤ := by
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      subst h
      have hx : x = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 x.2)
      rw [hx, map_zero, map_zero] at hy
      exact hy rfl
    · exact h
  have hmem : ∀ v, v ∈ S.toSubmodule := fun v => by rw [hS]; trivial
  let P : V →ₗ[ℂ] S.toSubmodule := LinearMap.id.codRestrict S.toSubmodule hmem
  have hP : ∀ a v, P (ρ a v) = S.toRepresentation a (P v) := fun a v => Subtype.ext rfl
  have hPx : P x.1 = x := Subtype.ext rfl
  refine ⟨f.toLinearMap ∘ₗ g.toLinearMap ∘ₗ P, fun h => hy ?_, fun a v => ?_⟩
  · have h1 := LinearMap.congr_fun h x.1
    simp only [LinearMap.comp_apply, hPx, LinearMap.zero_apply] at h1
    exact h1
  · simp only [LinearMap.comp_apply, hP]
    exact (congrArg f (g.isIntertwining _ _ a (P v))).trans (f.isIntertwining _ _ a _)

theorem jsBound_no_map : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (τ : GlobalTheory.CuspRep.CuspSub E (1 + 1))
    (w : HeightOneSpectrum (𝓞 E)) (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ) (s₁ s₂ : ℝ), GlobalTheory.Published.JacquetShalikaBound →
    GlobalTheory.SplitWeil.IsUnram χ₁ → GlobalTheory.SplitWeil.IsUnram χ₂ → (∀ u, ‖(χ₁ u : ℂ)‖ = 1) → (∀ u, ‖(χ₂ u : ℂ)‖ = 1) →
    1 < |s₁ - s₂| →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Q : Representation ℂ (GL (Fin (1 + 1)) (w.adicCompletion E)) V),
      GlobalTheory.SmGL.IsSubquotient Q (GlobalTheory.SmGL.prod₂
        (GlobalTheory.SmGL.detRep (Fin 1) (χ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (s₁ : ℂ)))
        (GlobalTheory.SmGL.detRep (Fin 1) (χ₂ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (s₂ : ℂ)))) →
      ∀ f : Q.IntertwiningMap (τ.locRep w), f ≠ 0 → False := by
  intro E _ _ _ τ w χ₁ χ₂ s₁ s₂ hJS hu₁ hu₂ hn₁ hn₂ hs V _ _ Q hQ f hf
  set k := w.adicCompletion E
  set ϖ : kˣ := Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) with hϖdef
  set q : ℝ := (Ideal.absNorm w.asIdeal : ℝ) with hqdef
  have hq1 : 1 < q := by
    have := HeightOneSpectrum.one_lt_absNorm w
    rw [hqdef]; exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans hq1
  have hnabs : GlobalTheory.SplitWeil.nabs k ϖ = q⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.SmGL.SphCompletion.ord_completion, GlobalTheory.LocLanglands.resCard_eq_normV]
    have h := Formalism.L2.Host.unif_spec w
    unfold Formalism.L2.Host.IsUnifAt at h
    rw [h]
    simp [q, Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hnorm : ∀ (χ : kˣ →* ℂˣ) (s : ℝ), (∀ u, ‖(χ u : ℂ)‖ = 1) →
      ‖(((χ * absPow k (s : ℂ)) ϖ : ℂˣ) : ℂ)‖ = q ^ (-s) := by
    intro χ s hχ
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ, one_mul, val_absPow_ofReal, hnabs, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), Real.inv_rpow hq0.le, Real.rpow_neg hq0.le]
  have hne : ∀ {χ χ' : kˣ →* ℂˣ} {s s' : ℝ}, (∀ u, ‖(χ u : ℂ)‖ = 1) → (∀ u, ‖(χ' u : ℂ)‖ = 1) →
      χ * absPow k (s : ℂ) = χ' * absPow k (s' : ℂ) * absPow k 1 → s = s' + 1 := by
    intro χ χ' s s' h h' e
    have e2 : χ' * absPow k (s' : ℂ) * absPow k 1 = χ' * absPow k ((s' + 1 : ℝ) : ℂ) := by
      rw [mul_assoc, ← absPow_add]; push_cast; rfl
    have := congrArg (fun m : kˣ →* ℂˣ => ‖((m ϖ : ℂˣ) : ℂ)‖) (e.trans e2)
    rw [hnorm χ s h, hnorm χ' _ h'] at this
    have := (Real.rpow_right_inj hq0 hq1.ne').1 this
    linarith
  set μ₁ := χ₁ * absPow k (s₁ : ℂ) with hμ₁
  set μ₂ := χ₂ * absPow k (s₂ : ℂ) with hμ₂
  have hU : ∀ {χ : kˣ →* ℂˣ} (s : ℝ), GlobalTheory.SplitWeil.IsUnram χ → GlobalTheory.SplitWeil.IsUnram (χ * absPow k (s : ℂ)) :=
    fun s h x hx => by rw [MonoidHom.mul_apply, h x hx, isUnram_absPow k _ x hx, mul_one]
  have hirr := GlobalTheory.T.principal_series_irreducible_unram k μ₁ μ₂ (hU s₁ hu₁) (hU s₂ hu₂)
    (fun e => by have := hne hn₁ hn₂ e; rw [this] at hs; norm_num at hs)
    (fun e => by have := hne hn₂ hn₁ e; rw [this, show s₁ - (s₁ + 1) = -1 by ring] at hs; norm_num at hs)
  set ρ := GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin 1) μ₁) (GlobalTheory.SmGL.detRep (Fin 1) μ₂) with hρ
  obtain ⟨F, hF0, hFi⟩ := exists_map_of_subquotient hirr hQ f hf
  let σ : GlobalTheory.CuspRep.SmIrr (GL (Fin (1 + 1)) k) := ⟨_, ρ, GlobalTheory.SmGL.isSmooth_prod₂ _ _, hirr⟩
  have hσ : τ.IsLocComp w σ := ⟨F, hF0, hFi⟩
  have hB := GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ (GlobalTheory.T.principal_series_satake_parameters E w μ₁ μ₂ (hU s₁ hu₁) (hU s₂ hu₂))
  obtain ⟨ν, hνu, hνU⟩ := GlobalTheory.T.cusp_rep_unitary_twist_exists E (1 + 1) (GlobalTheory.CuspRep.CG.mk τ) (by norm_num)
  have hB' := GlobalTheory.SphGal.hasSatGL_twist E _ τ ν w _ (hνu w) hB
  have hJ := hJS E (1 + 1) ((GlobalTheory.CuspRep.CG.mk τ).twist ν) hνU w _ hB'
  have hc : 0 < ‖((ν.val w : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have key : ∀ (χ : kˣ →* ℂˣ) (s : ℝ), (∀ u, ‖(χ u : ℂ)‖ = 1) →
      (χ * absPow k (s : ℂ)) ϖ ∈ ({μ₁ ϖ, μ₂ ϖ} : Multiset ℂˣ) →
      -(1 / 2) * Real.log q < -s * Real.log q + Real.log ‖((ν.val w : ℂˣ) : ℂ)‖ ∧
        -s * Real.log q + Real.log ‖((ν.val w : ℂˣ) : ℂ)‖ < 1 / 2 * Real.log q := by
    intro χ s hχ hm
    have h := hJ _ (Multiset.mem_map.2 ⟨_, hm, rfl⟩)
    rw [Units.val_mul, norm_mul, hnorm χ s hχ] at h
    have e : Real.log (q ^ (-s) * ‖((ν.val w : ℂˣ) : ℂ)‖) = -s * Real.log q + Real.log ‖((ν.val w : ℂˣ) : ℂ)‖ := by
      rw [Real.log_mul (by positivity) hc.ne', Real.log_rpow hq0]
    constructor
    · have := Real.log_lt_log (by positivity) h.1
      rwa [Real.log_rpow hq0, e] at this
    · have := Real.log_lt_log (by positivity) h.2
      rwa [Real.log_rpow hq0, e] at this
  have k₁ := key χ₁ s₁ hn₁ (Multiset.mem_cons_self _ _)
  have k₂ := key χ₂ s₂ hn₂ (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))
  have hL : 0 < Real.log q := Real.log_pos hq1
  rcases lt_abs.1 hs with h | h <;> nlinarith

end GlobalTheory.JSPrinBound

end
