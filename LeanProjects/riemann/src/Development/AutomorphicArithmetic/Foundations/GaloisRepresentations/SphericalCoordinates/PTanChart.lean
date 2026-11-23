import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tanChart_of :
    UpperTheory.Gal.W2.TanDeriv → UpperTheory.Gal.W2.FlatAffine → UpperTheory.Gal.W2.ConjCharpoly → UpperTheory.Gal.W2.TanChart := by
  intro hTD hFA hCC E _ _ _ d hd Z Y sZ s' c₁ c₂ h₁ h₂ B s v₀ hB hv hs hs' hflat G G' hG hGv hev y hy0 A hT
  obtain ⟨U, W, hW1, hW2, t, hy, hU, hW, φ, hφ1, hφ2, hφ3, hφ4⟩ := hT
  obtain ⟨ψ, hψ1, hψ2⟩ := hTD E Y s' B s v₀ hB hv hs hs' y hy0 W hy
  let e₁ : Fin d → Sec s' W := fun l => Sec.res s' hW1 (appSec sZ s' c₁ U (t l))
  let e₂ : Fin d → Sec s' W := fun l => Sec.res s' hW2 (appSec sZ s' c₂ U (t l))
  have hφ2' : ∀ l, φ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) = Pi.single l 1 := hφ2
  have hφ3' : ∀ j, φ (KaehlerDifferential.D ℂ (Sec s' W) (e₂ j)) = fun l => A j l := hφ3
  let N : Set E := {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W}
  have hNo : IsOpen N := (hs W 0).1
  have hv₀N : v₀ ∈ N := by
    refine ⟨hv, ?_⟩
    have := hy
    simp only [CxPts.ptsIn, Set.mem_setOf_eq] at this
    rw [hy0] at this
    exact this
  have hNn : N ∈ 𝓝 v₀ := hNo.mem_nhds hv₀N
  have hK : ∀ ω, ψ ω = ∑ l, (φ ω) l • ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) := by
    intro ω
    set ω' := ω - ∑ l, (φ ω) l • KaehlerDifferential.D ℂ (Sec s' W) (e₁ l) with hω'
    have hφω' : φ ω' = 0 := by
      rw [hω', map_sub, map_sum]
      simp only [map_smul, hφ2']
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    obtain ⟨m, b, ω'', hb0, hωeq⟩ := hφ4 ω' hφω'
    have hψω' : ψ ω' = 0 := by
      rw [hωeq, map_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hψ1, hb0 i, zero_smul]
    have hω : ω = ω' + ∑ l, (φ ω) l • KaehlerDifferential.D ℂ (Sec s' W) (e₁ l) := by
      rw [hω']
      abel
    conv_lhs => rw [hω]
    rw [map_add, hψω', zero_add, map_sum]
    simp only [map_smul]
  let τ : E →ₗ[ℂ] Fin d → ℂ :=
    LinearMap.pi (fun l => ((ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) : E →L[ℂ] ℂ) : E →ₗ[ℂ] ℂ))
  have hτ : ∀ w l, τ w l = ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) w := fun w l => rfl
  have hinj : Function.Injective τ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hflat
    refine hFA E Y B s v₀ w hB hv hs W hW hv₀N.2 (fun f => ?_)
    have hf : fderiv ℂ (fun v => valAt' (s v) W f) v₀ = ψ (KaehlerDifferential.D ℂ (Sec s' W) f) :=
      (hψ2 f).symm
    rw [hf, hK, ContinuousLinearMap.sum_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [ContinuousLinearMap.smul_apply, ← hτ, hw]
    simp
  have hval : ∀ (c : Y ⟶ Z) (hc : W ≤ c ⁻¹ᵁ U) (f : Sec sZ U) (v : E), ⊤ ≤ s v ⁻¹ᵁ W →
      valAt' (s v) W (Sec.res s' hc (appSec sZ s' c U f)) = valAt' (s v ≫ c) U f := by
    intro c hc f v hvW
    exact (valAt'_res (s v) hc _ hvW).trans (valAt'_comp (s v) c U f)
  have hrel : ∀ w, τ (G' w) = A *ᵥ τ w := by
    intro w
    funext j
    have hd1 : DifferentiableAt ℂ (fun v => valAt' (s v) W (e₁ j)) v₀ :=
      ((hs W (e₁ j)).2).differentiableAt hNn
    have hGN : ∀ᶠ v in 𝓝 v₀, G v ∈ N := by
      have hNn' : N ∈ 𝓝 (G v₀) := by rw [hGv]; exact hNn
      exact hG.continuousAt.preimage_mem_nhds hNn'
    have heq : (fun v => valAt' (s v) W (e₂ j)) =ᶠ[𝓝 v₀]
        (fun v => valAt' (s v) W (e₁ j)) ∘ G := by
      filter_upwards [hNn, hGN, hev] with v hvN hGvN hevv
      simp only [Function.comp_apply]
      rw [hval c₂ hW2 (t j) v hvN.2, hval c₁ hW1 (t j) (G v) hGvN.2, hevv]
    have hd1' : HasFDerivAt (fun v => valAt' (s v) W (e₁ j))
        (fderiv ℂ (fun v => valAt' (s v) W (e₁ j)) v₀) (G v₀) := by
      rw [hGv]; exact hd1.hasFDerivAt
    have hcomp := hd1'.comp v₀ hG
    have hfd : fderiv ℂ (fun v => valAt' (s v) W (e₂ j)) v₀ =
        (fderiv ℂ (fun v => valAt' (s v) W (e₁ j)) v₀).comp G' := by
      rw [heq.fderiv_eq]
      exact hcomp.fderiv
    have h2 : ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₂ j)) w = ∑ l, A j l * τ w l := by
      rw [hK, hφ3', ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hτ]
    rw [Matrix.mulVec, dotProduct, ← h2, hψ2, hfd, hτ, hψ2]
    rfl
  exact hCC E d hd τ (G' : E →ₗ[ℂ] E) A hinj hrel
