import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
set_option maxSynthPendingDepth 1

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical HeckeAlgebra PositivityTheory.JacquetShalikaLocal
open ValuativeRel (valuation)
open scoped ValuativeRel Pointwise

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "π" => (GLnLocal.uniformizer F : F)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem torusPow_central (t : GL (Fin n) F) (c : GL (Fin n) F)
    (h : ∃ a : F, (t : Matrix (Fin n) (Fin n) F) = diagonal fun _ => a) : t * c = c * t := by
  obtain ⟨a, ha⟩ := h
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_mul, Units.val_mul, ha, diagonal_mul, mul_diagonal, mul_comm]

theorem torusPow_one_mem_minusculeSet :
    torusPow F n (fun _ => 1) ∈ minusculeSet F n n := by
  have hπ : π ≠ 0 := Cartan.uniformizer_ne_zero F
  have hinv : (torusPow F n (fun _ => (1 : ℤ)))⁻¹ = torusPow F n (fun _ => -1) := by
    rw [← torusPow_neg]
    congr 1
  refine ⟨fun i j => ?_, fun i j => ?_, ?_⟩
  · change ((torusPow F n (fun _ => (1 : ℤ)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]
    rw [coe_torusPow, diagonal_apply]
    split_ifs
    · simp
    · exact (𝒪[F]).zero_mem
  · rw [hinv]
    change π * ((torusPow F n (fun _ => (-1 : ℤ)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]
    rw [coe_torusPow, diagonal_apply]
    split_ifs
    · rw [_root_.zpow_neg_one, mul_inv_cancel₀ hπ]
      exact (𝒪[F]).one_mem
    · rw [mul_zero]
      exact (𝒪[F]).zero_mem
  · rw [coe_torusPow, det_diagonal]
    simp

theorem inv_mul_mem_integralGL_of_mem {x : GL (Fin n) F} (hx : x ∈ minusculeSet F n n) :
    (torusPow F n (fun _ => 1))⁻¹ * x ∈ integralGL F n := by
  obtain ⟨-, h2, h3⟩ := hx
  have hπ : π ≠ 0 := Cartan.uniformizer_ne_zero F
  have hdet : (x : Matrix (Fin n) (Fin n) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero
  set ϖ := torusPow F n (fun _ => (1 : ℤ)) with hϖ
  have hk : ϖ * x⁻¹ ∈ integralGL F n := by
    refine mem_integralGL_of_forall_mem (fun i j => ?_) ?_
    · have : (ϖ * x⁻¹ : GL (Fin n) F) i j = π * (x⁻¹ : GL (Fin n) F) i j := by
        change ((ϖ : Matrix (Fin n) (Fin n) F) * ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) i j = _
        rw [hϖ, coe_torusPow, diagonal_mul]
        simp
      rw [this]
      exact h2 i j
    · have e : (((ϖ * x⁻¹ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F).det *
          (x : Matrix (Fin n) (Fin n) F).det = π ^ n := by
        rw [← det_mul, ← Units.val_mul, inv_mul_cancel_right, hϖ, coe_torusPow, det_diagonal]
        simp
      have e' := congrArg (valuation F) e
      rw [map_mul, map_pow, h3] at e'
      have hv : valuation F π ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 hπ)
      exact mul_right_cancel₀ hv (by rw [e', one_mul])
  have := (integralGL F n).inv_mem hk
  rw [_root_.mul_inv_rev, inv_inv] at this
  rwa [show ϖ⁻¹ * x = x * ϖ⁻¹ by
    have hc := torusPow_central (ϖ⁻¹) x ⟨π⁻¹, by
      rw [show ϖ⁻¹ = torusPow F n (fun _ => (-1 : ℤ)) by rw [hϖ, ← torusPow_neg]; congr 1, coe_torusPow]
      simp⟩
    exact hc]

section Hecke

variable {V : Type} [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem integral_minusculeHecke_form (ρ : Representation ℂ (GL (Fin n) F) V) {v : V}
    (hK : ∀ g ∈ integralGL F n, ρ g v = v) (l : V →ₗ[ℂ] ℂ) (r : ℕ) {e : ℂ}
    (hT : ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v = e • v)
    (g : GL (Fin n) F) :
    ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * l (ρ (g * x) v) ∂μ =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * (e * l (ρ g v)) := by
  classical
  set Φ : GL (Fin n) F → ℂ := fun x =>
    (minusculeHecke μ r : HeckeAlgebra μ) x * l (ρ (g * x) v) with hΦ
  have hcs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [hΦ, minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  have hKΦ : ∀ x, ∀ k ∈ integralOpen F n, Φ (x * k) = Φ x := by
    intro x k hk
    simp only [hΦ]
    rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, map_mul,
      Module.End.mul_apply, hK k hk]
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs hKΦ,
    Complex.real_smul]
  congr 1
  change (∑ᶠ x : GL (Fin n) F ⧸ integralGL F n, Φ x.out) = _
  set L : V →ₗ[ℂ] ℂ := l ∘ₗ ρ g with hL
  have hpt : ∀ c : GL (Fin n) F ⧸ integralGL F n, Φ c.out =
      L ((minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v) := by
    intro c
    simp only [hΦ, hL, minusculeHecke_apply, map_smul, smul_eq_mul, LinearMap.comp_apply, map_mul,
      Module.End.mul_apply]
  have hfin : (Function.support fun c : GL (Fin n) F ⧸ integralGL F n =>
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v).Finite := by
    have hc : HasCompactSupport ((minusculeSet F n r).indicator (fun _ => (1 : ℂ))) :=
      HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => Set.indicator_of_notMem hx _
    refine (finite_image_mk_tsupport (integralOpen F n) hc).subset
      fun (c : GL (Fin n) F ⧸ integralGL F n) hc' => ?_
    refine ⟨c.out, subset_tsupport _ fun h0 => hc' ?_, QuotientGroup.out_eq' c⟩
    exact (congrArg (fun t : ℂ => t • ρ c.out v) h0).trans (zero_smul ℂ _)
  have hmap : L (∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v) =
      ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
        L ((minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v) :=
    AddMonoidHom.map_finsum (L : V →+ ℂ) hfin
  simp only [hpt]
  rw [← hmap, hT, map_smul, smul_eq_mul, hL, LinearMap.comp_apply]

theorem integral_centralHecke_form {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) (g : GL (Fin n) F) :
    ∫ x, (centralHecke μ : HeckeAlgebra μ) x * f (g * x) ∂μ =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
        f (g * torusPow F n (fun _ => -1)) := by
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * f (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) * f (g * (g₀ * y))) =
      (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => f (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    by_cases hy : y ∈ integralGL F n
    · have hm : g₀ * y ∈ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show y ∈ (integralGL F n : Set (GL (Fin n) F))
        from hy), one_mul, ← mul_assoc, hf _ _ hy]
    · have hm : g₀ * y ∉ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show y ∉ (integralGL F n :
        Set (GL (Fin n) F)) from hy), zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul]

end Hecke

theorem rho_torusPow_neg_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) {v : V}
    (hK : ∀ g ∈ integralGL F n, ρ g v = v) {e : ℂ} (he : e ≠ 0)
    (hT : ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n n).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v = e • v) :
    ρ (torusPow F n (fun _ => -1)) v = e⁻¹ • v := by
  set ϖ := torusPow F n (fun _ => (1 : ℤ)) with hϖ
  set c₀ : GL (Fin n) F ⧸ integralGL F n := QuotientGroup.mk ϖ with hc₀
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) ϖ
  have hout : c₀.out ∈ minusculeSet F n n := by
    rw [hc₀, hk]
    have := mul_mem_minusculeSet (torusPow_one_mem_minusculeSet (F := F) (n := n))
      (integralGL F n).one_mem k.2
    rwa [one_mul] at this
  have hsum : ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n n).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v = ρ ϖ v := by
    rw [finsum_eq_single _ c₀ fun c hc => ?_]
    · rw [Set.indicator_of_mem hout, one_smul, hc₀, hk, map_mul, Module.End.mul_apply, hK _ k.2]
    · rw [Set.indicator_of_notMem, zero_smul]
      intro hm
      apply hc
      rw [← QuotientGroup.out_eq' c]
      exact (QuotientGroup.eq.2 (inv_mul_mem_integralGL_of_mem hm)).symm
  have h1 : ρ ϖ v = e • v := hsum.symm.trans hT
  have hinv : torusPow F n (fun _ => (-1 : ℤ)) = ϖ⁻¹ := by
    rw [hϖ, ← torusPow_neg]
    congr 1
  have h2 : ρ ϖ⁻¹ (ρ ϖ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h1, map_smul] at h2
  rw [hinv]
  calc ρ ϖ⁻¹ v = e⁻¹ • (e • ρ ϖ⁻¹ v) := by rw [smul_smul, inv_mul_cancel₀ he, one_smul]
    _ = e⁻¹ • v := by rw [h2]

theorem esymmL_self : esymmL n n = monomial (fun _ : Fin n => (1 : ℤ)) := by
  rw [esymmL]
  have : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [this, Finset.sum_singleton]
  congr 1
  funext i
  simp [lamS]

theorem evalAt_esymmL_self_mul (z : Fin n → ℂˣ) :
    evalAt z (esymmL n n) * evalAt z (monomial (fun _ : Fin n => (-1 : ℤ))) = 1 := by
  rw [← map_mul, esymmL_self, monomial, monomial, AddMonoidAlgebra.single_mul_single]
  have : (fun _ : Fin n => (1 : ℤ)) + (fun _ => -1) = 0 := by
    funext i
    simp
  rw [this, one_mul, ← AddMonoidAlgebra.one_def, map_one]

theorem heckeEigenvector_whittaker : L7 := by
  unfold L7
  intro F _ _ _ _ ψ hψ n V _ _ ρ v z hv l hl g
  borelize (GL (Fin n) F)
  let μ : Measure (GL (Fin n) F) := Measure.haar
  obtain ⟨hK, hT⟩ := hv
  set W : GL (Fin n) F → ℂ := fun g => l (ρ g v) with hW
  have hWN : ∀ u ∈ unipotent F n, ∀ g, W (u * g) = Whittaker.psiN ψ u * W g := by
    intro u hu g
    simp only [hW, map_mul, Module.End.mul_apply]
    exact hl u hu _
  have hWK : ∀ g, ∀ k ∈ integralGL F n, W (g * k) = W g := by
    intro g k hk
    simp only [hW, map_mul, Module.End.mul_apply, hK k hk]
  have hTm : ∀ r ≤ n, minusculeHecke μ r ∈ eigenSubalgebra μ z W hWK := by
    intro r hr g
    change ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * l (ρ (g * x) v) ∂μ = _ * l (ρ g v)
    rw [integral_minusculeHecke_form ρ hK l r (hT r hr) g,
      evalAt_satakeTransform_minusculeHecke z hr]
    ring
  have hen : evalAt z (esymmL n n) ≠ 0 := left_ne_zero_of_mul_eq_one (evalAt_esymmL_self_mul z)
  have hcen : ρ (torusPow F n (fun _ => -1)) v = (evalAt z (esymmL n n))⁻¹ • v := by
    refine rho_torusPow_neg_one ρ hK hen ?_
    have := hT n le_rfl
    simpa using this
  have hc : centralHecke μ ∈ eigenSubalgebra μ z W hWK := by
    intro g
    rw [integral_centralHecke_form hWK g, satakeTransform_centralHecke, map_smul, smul_eq_mul]
    simp only [hW, map_mul, Module.End.mul_apply, hcen, map_smul, smul_eq_mul]
    rw [inv_eq_of_mul_eq_one_right (evalAt_esymmL_self_mul z)]
    ring
  have htop := eigenSubalgebra_eq_top z hWK hTm hc
  have heig : ∀ (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F),
      ∫ x, (h : HeckeAlgebra μ) x * W (g * x) ∂μ = evalAt z (satakeTransform μ h) * W g := by
    intro h g
    have hmem : h ∈ eigenSubalgebra μ z W hWK := by
      rw [htop]
      exact Algebra.mem_top
    exact hmem g
  have := eq_smul_sphericalWhittaker hψ.1 hψ.2.1 z hWN hWK heig g
  simpa [hW] using this

end GlobalTheory.CompanionTheory.SatakeBound

end
