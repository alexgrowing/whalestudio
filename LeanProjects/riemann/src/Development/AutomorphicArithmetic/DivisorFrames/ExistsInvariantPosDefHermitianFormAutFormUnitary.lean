import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeHermitianPairing
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory in
theorem UpperTheory.exists_invariant_posDef_hermitian_form_autForm_unitary :
    ∀ (D : D7) [IsCMField D.host.E] (V : HSp D), V.SigOK → V.IsPosDef → ∀ (j : UA D.host.E V.rank ≃ₜ* GA D V),
        (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) →
        ∃ B : (UA D.host.E V.rank → ℂ) →ₗ⋆[ℂ] (UA D.host.E V.rank → ℂ) →ₗ[ℂ] ℂ, (∀ φ, IsAutFormU φ → φ ≠ 0 → 0 < (B φ φ).re) ∧
          ∀ k ∈ finU D.host.E V.rank, ∀ φ ψ, IsAutFormU φ → IsAutFormU ψ →
            B (RU D.host.E V.rank k φ) (RU D.host.E V.rank k ψ) = B φ ψ := by
  intro D _ V hs hp j hj
  classical
  obtain ⟨h1, h2, h3, h4, h5, _h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (GA D V), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨hR, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact V (fun τ => GlobalTheory.RepsObj.gramAt_posDef hp hs τ)

  let N : Submodule ℂ (UA D.host.E V.rank → ℂ) :=
    { carrier := {φ | Continuous φ ∧ ∀ γ ∈ ratU D.host.E V.rank, ∀ g, φ (γ * g) = φ g}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun γ hγ g => by simp [ha.2 γ hγ g, hb.2 γ hγ g]⟩
      zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun γ hγ g => by simp [ha.2 γ hγ g]⟩ }
  have hAN : ∀ φ, IsAutFormU φ → φ ∈ N := fun φ h => ⟨h.cont, h.left⟩
  have hRN : ∀ k, ∀ φ ∈ N, RU D.host.E V.rank k φ ∈ N := by
    intro k φ h
    refine ⟨h.1.comp (continuous_mul_const k), fun γ hγ g => ?_⟩
    show φ (γ * g * k) = φ (g * k)
    rw [mul_assoc, h.2 γ hγ]
  have hLC : ∀ x ∈ N, Continuous (fun g => x (j.symm g)) ∧
      ∀ γ ∈ GQ V, ∀ g, x (j.symm (γ * g)) = x (j.symm g) := by
    intro x hx
    refine ⟨hx.1.comp j.symm.continuous, fun γ hγ g => ?_⟩
    rw [map_mul]
    exact hx.2 _ ((hj _).2 (by rwa [j.apply_symm_apply])) _
  have hI : ∀ x ∈ N, ∀ y ∈ N, IntegrableOn (fun g => star (x (j.symm g)) * y (j.symm g)) 𝓕 μ := by
    intro x hx y hy
    exact GlobalTheory.MultPetersson.integrableOn_star_mul μ 𝓕 C hμ h𝓕 hC hcov (hLC x hx).1 (hLC y hy).1 (hLC x hx).2
      (hLC y hy).2
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl N
  let P : (UA D.host.E V.rank → ℂ) →ₗ[ℂ] N := Submodule.projectionOnto N q hq
  have hPN : ∀ T, ((P T : N) : UA D.host.E V.rank → ℂ) ∈ N := fun T => (P T).2
  have hPid : ∀ T ∈ N, ((P T : N) : UA D.host.E V.rank → ℂ) = T := fun T hT =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨T, hT⟩)
  let F : (UA D.host.E V.rank → ℂ) → (UA D.host.E V.rank → ℂ) → ℂ := fun x y =>
    ∫ g in 𝓕, star ((P x).1 (j.symm g)) * (P y).1 (j.symm g) ∂μ
  let B : (UA D.host.E V.rank → ℂ) →ₗ⋆[ℂ] (UA D.host.E V.rank → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F
    (fun x x' y => by
      simp only [F, map_add, Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x') _ (hPN y))]
      congr 1
      funext g
      simp only [Pi.add_apply, star_add, add_mul])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]
      ring)
    (fun x y y' => by
      simp only [F, map_add, Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x) _ (hPN y'))]
      congr 1
      funext g
      simp only [Pi.add_apply, mul_add])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring)
  have hB : ∀ x ∈ N, ∀ y ∈ N, B x y = ∫ g in 𝓕, star (x (j.symm g)) * y (j.symm g) ∂μ := by
    intro x hx y hy
    show F x y = _
    simp only [F, hPid x hx, hPid y hy]
  refine ⟨B, ?_, ?_⟩
  · intro T hT' h0
    have hT := hAN T hT'
    rw [hB _ hT _ hT]
    have hre : ∫ g in 𝓕, star (T (j.symm g)) * T (j.symm g) ∂μ = ((∫ g in 𝓕, ‖T (j.symm g)‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.conj_mul']
      push_cast
      rfl
    rw [hre, Complex.ofReal_re]
    have hnn : 0 ≤ ∫ g in 𝓕, ‖T (j.symm g)‖ ^ 2 ∂μ := integral_nonneg fun g => by positivity
    refine lt_of_le_of_ne hnn fun hz => h0 ?_
    have hi : IntegrableOn (fun g => ‖T (j.symm g)‖ ^ 2) 𝓕 μ := by
      have := (hI T hT T hT).norm
      have e2 : (fun g => ‖star (T (j.symm g)) * T (j.symm g)‖) = fun g => ‖T (j.symm g)‖ ^ 2 := by
        funext g
        rw [norm_mul, norm_star, sq]
      rw [e2] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi).1 hz.symm
    have := GlobalTheory.SchurConst.eq_zero_of_ae μ 𝓕 hμ h𝓕 (fun g => T (j.symm g)) (hLC T hT).1 (hLC T hT).2 (by
      filter_upwards [hae] with g hg
      simpa using hg)
    funext x
    have h := congrFun this (j x)
    simpa using h
  · intro k _hk T T' hT0 hT0'
    have hT := hAN T hT0
    have hT' := hAN T' hT0'
    rw [hB _ (hRN k T hT) _ (hRN k T' hT'), hB _ hT _ hT']
    haveI := h5
    haveI := h4
    haveI := h2
    haveI := h7
    haveI := hR
    have hmap : Measure.map (fun g => g * j k) μ = μ := map_mul_right_eq_self μ (j k)
    have hh : ∀ x : UA D.host.E V.rank → ℂ, ∀ g, RU D.host.E V.rank k x (j.symm g) = x (j.symm (g * j k)) := by
      intro x g
      rw [map_mul, j.symm_apply_apply]
      rfl
    simp only [hh]
    have hinv : ∀ γ ∈ GQ V, ∀ g, (fun g => star (T (j.symm g)) * T' (j.symm g)) (γ * g) =
        (fun g => star (T (j.symm g)) * T' (j.symm g)) g := by
      intro γ hγ g
      simp only [(hLC T hT).2 γ hγ, (hLC T' hT').2 γ hγ]
    exact (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 (j k) hmap _ hinv (hI T hT T' hT')).2
