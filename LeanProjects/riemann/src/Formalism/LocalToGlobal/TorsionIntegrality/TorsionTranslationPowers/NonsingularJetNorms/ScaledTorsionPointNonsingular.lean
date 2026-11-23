import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Taylor0ConstMul
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSys
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section

namespace Formalism.L2.Th1.E

namespace ScaledTorsionTransport

theorem transport {K : Type*} [Field K] [DecidableEq K] {W W' : WeierstrassCurve K} (hW : W = W')
    {x y x' y' : K} (hx : x = x') (hy : y = y') (h : W.toAffine.Nonsingular x y) (N : ℕ)
    (hN : N • WeierstrassCurve.Affine.Point.some _ _ h = 0) :
    ∃ h' : W'.toAffine.Nonsingular x' y', N • WeierstrassCurve.Affine.Point.some _ _ h' = 0 := by
  subst hW hx hy
  exact ⟨h, hN⟩

end ScaledTorsionTransport

open Formalism.L2.Th1 in
open Classical in

theorem scaled_torsion_point_of_add (hA : PtOfAdd) : ScaledTorsionPointNonsingular := by
  intro l _ L ι lam hlam z N hNz hz
  have hμ0 : ι.symm lam ≠ 0 := by
    intro h0
    apply hlam
    rw [← ι.apply_symm_apply lam, h0, map_zero]
  have hc : (ι.symm lam)⁻¹ ≠ 0 := inv_ne_zero hμ0
  obtain ⟨hmem, -, -, hwp, -, -, -, -, -, hg2, hg3⟩ := F.homogeneity L _ hc
  have hz' : (ι.symm lam)⁻¹ * z ∉ (F.scalePair L _ hc).lattice := by
    rw [hmem, inv_mul_cancel_left₀ hc]
    exact hz
  have hNz' : (N : ℂ) * ((ι.symm lam)⁻¹ * z) ∈ (F.scalePair L _ hc).lattice := by
    rw [hmem]
    have e : ((ι.symm lam)⁻¹)⁻¹ * ((N : ℂ) * ((ι.symm lam)⁻¹ * z)) = (N : ℂ) * z := by
      field_simp
    rw [e]
    exact hNz
  have htor := Tor.nsmul_ptOf (l := l) (L := F.scalePair L _ hc) (ι := ι) hA PtOfZero_of
    ((ι.symm lam)⁻¹ * z) N
  rw [(PtOfZero_of l (F.scalePair L _ hc) ι _).2 hNz',
    AnaSys.ptOf_notMem (l := l) (L := F.scalePair L _ hc) (ι := ι) _ hz'] at htor
  refine ScaledTorsionTransport.transport ?_ ?_ ?_ _ N htor
  · simp only [curveL, hg2, hg3, map_mul, map_inv₀, map_pow, inv_pow, inv_inv,
      RingEquiv.apply_symm_apply]
  · simp only [hwp, map_mul, map_inv₀, map_pow, inv_pow, inv_inv, RingEquiv.apply_symm_apply]
  · simp only [ScaledModelNorms.dwp_scale, map_mul, map_inv₀, map_pow, inv_pow, inv_inv,
      RingEquiv.apply_symm_apply]

end Formalism.L2.Th1.E
