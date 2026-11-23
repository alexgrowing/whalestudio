import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

theorem tanDeriv_of : TanDeriv := by
  intro V _ _ Y s' B s v₀ hB hv₀ hs hss y hy W hyW
  have hv₀S : v₀ ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} := ⟨hv₀, by rw [← hy]; exact hyW⟩
  have hnhds : {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} ∈ 𝓝 v₀ := (hs W 0).1.mem_nhds hv₀S
  have hval : ∀ v (hv : v ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W}) (b : Sec s' W),
      valAt' (s v) W b = CxPts.ev s' (RingHom.id ℂ) W b ⟨s v, hss v hv.1⟩ := by
    intro v hv b
    simp only [valAt', CxPts.ev, valR, dif_pos hv.2]
    rfl
  let g : Sec s' W → V → ℂ := fun b v => valAt' (s v) W b
  have hd : ∀ b, DifferentiableAt ℂ (g b) v₀ := fun b =>
    ((hs W b).2 v₀ hv₀S).differentiableAt ((hs W b).1.mem_nhds hv₀S)
  have hadd : ∀ b c, g (b + c) =ᶠ[𝓝 v₀] g b + g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b + c) = valAt' (s v) W b + valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_add _ _ _)
  have hmul : ∀ b c, g (b * c) =ᶠ[𝓝 v₀] g b * g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b * c) = valAt' (s v) W b * valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_mul _ _ _)
  have hconst : ∀ a : ℂ, ∀ᶠ v in 𝓝 v₀, g (algebraMap ℂ (Sec s' W) a) v = a := fun a =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (algebraMap ℂ (Sec s' W) a) = a
      rw [hval v hv]
      exact CxPts.ev_algX (show (⟨s v, hss v hv.1⟩ : CxPts s' (RingHom.id ℂ)) ∈ CxPts.ptsIn s' (RingHom.id ℂ) W from hv.2) a)
  have hyeq : (⟨s v₀, hss v₀ hv₀S.1⟩ : CxPts s' (RingHom.id ℂ)) = y := Subtype.ext hy.symm
  have hv0 : ∀ b, g b v₀ = CxPts.evHom hyW b := fun b => by
    change valAt' (s v₀) W b = _
    rw [hval v₀ hv₀S b, hyeq]
    exact CxPts.ev_eq hyW b
  have hφa : ∀ a : ℂ, CxPts.evHom hyW (algebraMap ℂ (Sec s' W) a) = a := fun a =>
    (CxPts.ev_eq hyW _).symm.trans (CxPts.ev_algX hyW a)
  letI : Module (Sec s' W) (V →L[ℂ] ℂ) := Module.compHom _ (CxPts.evHom hyW)
  haveI : IsScalarTower ℂ (Sec s' W) (V →L[ℂ] ℂ) := ⟨fun a b m => by
    change (CxPts.evHom hyW (a • b)) • m = a • ((CxPts.evHom hyW b) • m)
    have h1 : CxPts.evHom hyW (a • b) = a * CxPts.evHom hyW b :=
      (congrArg (CxPts.evHom hyW) (Algebra.smul_def a b)).trans
        ((map_mul (CxPts.evHom hyW) _ _).trans (congrArg (· * CxPts.evHom hyW b) (hφa a)))
    exact (congrArg (· • m) h1).trans (mul_smul _ _ _)⟩
  let L : Sec s' W →ₗ[ℂ] (V →L[ℂ] ℂ) :=
    { toFun := fun b => fderiv ℂ (g b) v₀
      map_add' := fun b c => by
        change fderiv ℂ (g (b + c)) v₀ = fderiv ℂ (g b) v₀ + fderiv ℂ (g c) v₀
        rw [(hadd b c).fderiv_eq, fderiv_add (hd b) (hd c)]
      map_smul' := fun a b => by
        change fderiv ℂ (g (a • b)) v₀ = a • fderiv ℂ (g b) v₀
        have h' : g (a • b) =ᶠ[𝓝 v₀] fun v => a * g b v := by
          rw [Algebra.smul_def]
          filter_upwards [hmul (algebraMap ℂ _ a) b, hconst a] with v h1 h2
          rw [h1, Pi.mul_apply, h2]
        rw [h'.fderiv_eq, fderiv_const_mul (hd b)] }
  let D : Derivation ℂ (Sec s' W) (V →L[ℂ] ℂ) := Derivation.mk' L (fun b c => by
    change fderiv ℂ (g (b * c)) v₀ =
      (CxPts.evHom hyW b) • fderiv ℂ (g c) v₀ + (CxPts.evHom hyW c) • fderiv ℂ (g b) v₀
    rw [(hmul b c).fderiv_eq, fderiv_mul (hd b) (hd c), hv0 b, hv0 c])
  refine ⟨D.liftKaehlerDifferential.restrictScalars ℂ, fun b ω => ?_, fun b => ?_⟩
  · change D.liftKaehlerDifferential (b • ω) = _
    rw [LinearMap.map_smul]
    exact congrArg (· • D.liftKaehlerDifferential ω) (CxPts.ev_eq hyW b).symm
  · change D.liftKaehlerDifferential (KaehlerDifferential.D ℂ _ b) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl

end UpperTheory.Gal.W2
