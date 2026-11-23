import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationExpUniqueFullLevelMarkingStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.fixEq_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.OneAt → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixEq := by
  intro hHC hOne hLat p _ D G L gb N N' h hLev X X' c₁ c₂ hX hL hX' hL' ρ hFine v t₀ B PD RD D' t hCls P j a hCo y hSees ga hga P₁ P₂ x₁ x₂ e₁ e₂ hU₁ hU₂ hP
  have hN3 : 3 ≤ N := hLev.1
  have hNp : N.Coprime p := hLev.2.1
  have hdvd : N ∣ N' := hLev.2.2.2.2.1
  obtain ⟨hPl, hCA, hLoc, -⟩ := hCo
  obtain ⟨-, hS1, hS2⟩ := hSees
  obtain ⟨D'', t'', P'', e'', inc, j'', hCls'', hU'', hPinc, he'', hd, hjinc, hPl'', hCA'', hLoc''⟩ :=
    hHC p D G L gb N N' h hLev X X' c₂ hX hL hX' hL' ρ hFine D' t P₁ x₁ e₁ hU₁ B j a.1.1 (PD.lat a.1.2) hPl hCA hLoc
  obtain ⟨e₂', hU₂', he₂'⟩ :=
    hOne p D G L gb N N' h hLev X X' c₁ hX hL hX' hL' ρ hFine B PD D' t hCls j a.1 hPl hCA hLoc P₂ x₂ e₂ hU₂
  have hCAN : IsCoordA L (trivX B) N D' t j a.1.1 := by
    refine ⟨hCA.1, fun b => ?_⟩
    obtain ⟨w, hw, hweq⟩ := hCA.2 b
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k • w, AddSubgroup.nsmul_mem _ hw k, ?_⟩
    rw [hweq, hk, mul_smul]
  have hmem1 : (a.1.1 * h⁻¹)⁻¹ * B.toAf y * a.1.1 ∈ L.KN N := by
    have hS1' : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ L.KN N := hS1
    rw [mul_inv_rev, inv_inv]
    rw [mul_assoc h, mul_assoc h]
    exact hS1'
  obtain ⟨w, hwm, hwj⟩ :=
    (hLat p D G L B PD N (by omega) hNp D'' t'' D' t j'' j (a.1.1 * h⁻¹, a.1.2) a.1 N N' t'' t
      hCls'' hCls hPl'' hPl hCA'' hCAN hLoc'' hLoc y).mp ⟨hmem1, hS2⟩
  have hcancel : ∀ w' : VQ D, (actY L y) ((actY L y⁻¹) w') = w' := by
    intro w'
    simp only [actY]
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hgi : ∀ u, w (ga u) = inc u := by
    intro u
    apply hPl''.1
    rw [hjinc, hwj, hga, hcancel]
  have hPw : ∀ x, P'' (w x) = P₂ x := by
    intro x
    obtain ⟨d, u, hd0, hdu⟩ := hd (w x)
    have hgu : ga u = d • x := by
      apply w.injective
      rw [hgi, hdu, map_nsmul]
    have h2 : d • P'' (w x) = d • P₂ x := by
      rw [← map_nsmul, ← map_nsmul, ← map_nsmul, ← hgu, hgi, hPinc, hP]
    exact smul_right_injective _ hd0 h2
  have hPw' : ∀ x, P'' (w x) = (LinearEquiv.refl ℂ (Fin D.g → ℂ)) (P₂ x) := fun x => hPw x
  have hpt : x₂ ≫ c₁.q = x₁ ≫ c₂.q :=
    hFine.sep D' D'' t t'' P₂ P'' _ _ e₂' e'' hU₂' hU'' w (LinearEquiv.refl ℂ _) hwm hPw'
  have hT := GlobalTheory.T.uniformisationAt_transport_isometry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w (LinearEquiv.refl ℂ _) (by omega) hU₂' hwm hPw' hU''.2.1
  have key : ∀ (y₁ y₂ : Sp ℂ ⟶ (gfam X.univ hX hL).X) (hy : y₁ = y₂)
      (f₁ : (Fin D.g → ℂ) → (Over.mk y₁ ⟶ (gfam X.univ hX hL).A))
      (f₂ : (Fin D.g → ℂ) → (Over.mk y₂ ⟶ (gfam X.univ hX hL).A)),
      UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' y₁ f₁ →
      UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' y₂ f₂ →
      ∀ z, Over.Hom.left (f₁ z) = Over.Hom.left (f₂ z) := by
    intro y₁ y₂ hy f₁ f₂ h₁ h₂ z
    subst hy
    rw [GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking _ _ _ _ _ _ _ _ _ _ _ _ _ f₁ f₂ hN3
      (GlobalTheory.UPel.HT.Datum.Cls.fullMark D N (by omega) hNp D'' t'' hCls'') h₁ h₂]
  refine ⟨hpt.symm, fun z => ?_⟩
  rw [← he'' z, ← he₂' z]
  exact key _ _ hpt.symm e'' _ hU'' hT z
