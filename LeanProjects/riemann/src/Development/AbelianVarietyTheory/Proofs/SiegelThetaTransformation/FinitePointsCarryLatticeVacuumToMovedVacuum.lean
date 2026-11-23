import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeVacuaTensorCorrespondLineStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransportStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InnerProductTranslatedVacuaEqGaussianKernelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem ipO_Th_self_eq (D : D7) (S T : HSp D) (C : Ctx S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (hμ : IsCovolOne (ratL T S) μ 𝓕) (x : Frame C.X.Ψ T.rank) (hx : x ∈ C.X.dom)
    (v v' : TF S.rank C.g) (hv : SW.IsSB v) (hv' : SW.IsSB v') (h : SW.ip v v = SW.ip v' v') :
    ipO μ 𝓕 (C.Th x v) (C.Th x v) = ipO μ 𝓕 (C.Th x v') (C.Th x v') := by

  have hR : IsRealPt (0 : WO S T) := by simp [IsRealPt]
  obtain ⟨a, -, b, -, hab⟩ :=
    GlobalTheory.SW.dbl_zero_and_norm D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even
  have hip := (ScalarProduct.ip_basic D S T C).2 μ 𝓕 hμ
  have key : ∀ φ : TF S.rank C.g, SW.IsSB φ → ipO μ 𝓕 (C.Th x φ) (C.Th x φ) =
      a * SW.ip φ φ * (gaussR C.X C.bas C.idx x (C.zOf x 0) * conj (gaussR C.X C.bas C.idx x (C.zOf x 0)) *
        kZero C.X C.idx x x (C.zOf x 0) (fun k i => conj (C.zOf x 0 k i))) := by
    intro φ hφ
    have hT : C.IsTh (C.Th x φ) := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C x hx φ hφ).1.1
    rw [← ((hip _ hT).2.2.2 _ hT).2.2.2.2.1 0,
      GlobalTheory.T.innerProduct_translated_vacua_eq_gaussianKernel D S T C μ 𝓕 hμ x hx x hx φ φ hφ hφ 0 0 hR hR, (hab φ φ hφ hφ).1]
  rw [key v hv, key v' hv', h]

theorem om_Th_vac : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ Λ' ∈ Vset D.host.E S.rank M, ∀ L L' : Lt D.host.E T.rank, SelfD C.X L → SelfD C.X L' → ∀ h ∈ GfC S, ∀ g ∈ GfC T, IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → ∀ v v', IsVac C.X C.bas w (tens Λ L) v → IsVac C.X C.bas w (tens Λ' L') v' → ∀ B, C.IsB B → ∃ c : ℂ, ‖c‖ = 1 ∧ om (h, g) (C.Th (C.xB B) v) = c • (C.Th (C.xB B) v') := by
  intro D S T C om hom w hwi hw1 hw2 M Λ hΛ Λ' hΛ' L L' hL hL' h hh g hg hmS hmT v v' hv hv' B hB
  have hBB := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  have hx : C.xB B ∈ C.X.dom := hBB.2.1
  have hfix : C.mvB g B = B := (hBB.2.2.2.2.2 g).2.2.1 hg
  set f := C.Th (C.xB B) v with hf
  set f' := C.Th (C.xB B) v' with hf'
  have hfT : C.IsTh f := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx v hv.1).1.1
  have hfT' : C.IsTh f' := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx v' hv'.1).1.1

  have hLat : IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f :=
    ((GlobalTheory.T.latticeVacua_tensor_correspond_line D S T C w hwi hw1 hw2 M Λ hΛ L hL).1 _ hx v hv.1).2 hv.2.2
  have hLat' : IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ' L')) (om (h, g) f) :=
    (GlobalTheory.T.completedTensorLattice_lattice_vacuum_transport D S T C h g Λ Λ' L L' hmS hmT).2 om hom f hfT hLat
  have hTh : C.IsTh (om (h, g) f) := hom.om_pres (h, g) f hfT
  have hFock : C.IsFock B (om (h, g) f) := by
    have h1 := ((GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors D S T C om hom h g f hfT).2 B hB).1
      ((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B hB v hv.1).1
    rwa [hfix] at h1
  obtain ⟨t, ht⟩ :=
    (GlobalTheory.T.latticeVacua_tensor_correspond_line D S T C w hwi hw1 hw2 M Λ' hΛ' L' hL').2 B hB v' hv' _ hTh hFock hLat'

  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := ScalarProduct.ip_basic D S T C
  have hsame : ipO μ 𝓕 f f = ipO μ 𝓕 f' f' :=
    ipO_Th_self_eq D S T C μ 𝓕 hμ _ hx v v' hv.1 hv'.1 (by rw [hv.2.1, hv'.2.1])
  have hom_eq : ipO μ 𝓕 (om (h, g) f) (om (h, g) f) = ipO μ 𝓕 f f :=
    ((hip μ 𝓕 hμ f hfT).2.2.2 f hfT).2.2.2.2.2 om hom (h, g)
  have hsc : ipO μ 𝓕 (t • f') (t • f') = t * conj t * ipO μ 𝓕 f' f' := by
    simp only [ipO, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  by_cases h0 : ipO μ 𝓕 f' f' = 0
  · have hz' : f' = 0 := (hip μ 𝓕 hμ f' hfT').2.1 h0
    have hz : f = 0 := (hip μ 𝓕 hμ f hfT).2.1 (hsame.trans h0)
    refine ⟨1, by simp, ?_⟩
    rw [hz, hz', map_zero, smul_zero]
  · refine ⟨t, ?_, ht⟩
    have h2 : t * conj t = 1 := by
      have := hom_eq
      rw [ht, hsc, hsame] at this
      exact (mul_left_eq_self₀.mp this).resolve_right h0
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖t‖ ^ 2 = 1 := by exact_mod_cast h2
    have h4 : 0 ≤ ‖t‖ := norm_nonneg t
    nlinarith [sq_nonneg (‖t‖ - 1), sq_nonneg (‖t‖ + 1)]

end GlobalTheory.Ker
