import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KZeroOnFrConstEntire
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InnerProductTranslatedVacuaEqGaussianKernelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerVacIp

variable {D : D7} {S T : HSp D} (C : Ctx S T)

theorem isONFr_xB (B : C.Bas) (hB : C.IsB B) : IsONFr C.X (C.xB B) := by
  unfold IsONFr
  intro τ
  have h1 : ∀ x y : T.V, star (T.hT x y) = T.hT y x := by
    intro x y
    exact T.herm.eq x y
  have h2 : ∀ x : D.host.E, tauE D (C.m.e.symm τ) (star x) = (starRingEnd ℂ) (tauE D (C.m.e.symm τ) x) := by
    intro x
    unfold tauE
    dsimp only [star, Formalism.BasicNotions.Host.cmStar]
    exact IsCMField.complexEmbedding_complexConj D.host.E (D.host.emb ↑(D.eTau (C.m.e.symm τ))) x
  have key : ∀ i j, (τ : D.host.E →+* ℂ) (C.X.Gm i j) = tauE D (C.m.e.symm τ) (HSpace.gram T i j) := by
    intro i j
    have he := C.m.e_emb (C.m.e.symm τ)
    rw [Equiv.apply_symm_apply] at he
    rw [he, C.m.gT, Matrix.transpose_apply, NumberField.ComplexEmbedding.conjugate_coe_eq, ← h2]
    unfold HSpace.gram
    rw [h1]
  rw [← hB (C.m.e.symm τ)]
  ext a b
  unfold FD.gram mat Ctx.xB hermC FD.col gramAt
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.star_def, Complex.conj_conj, Finset.sum_mul, key]
  rw [Finset.sum_comm]

theorem rho_zero_pt (f : WO S T → ℂ) : C.rho 0 f = f := by
  unfold Ctx.rho heisO
  funext w
  simp [symplOH, symplO, hO]

theorem zOf_zero (x : Frame C.X.Ψ T.rank) : C.zOf x 0 = 0 := by
  unfold Ctx.zOf Ctx.realPt zR
  funext k i
  simp [compAt, hermC]
  intro _
  simp only [← Pi.zero_def, Matrix.mulVec_zero, Pi.zero_apply]

theorem ip_vacua : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsCovolOne (ratL T S) μ 𝓕 → ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ φ' : TF S.rank C.g, SW.IsSB φ → SW.IsSB φ' →
      ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ') = a * ip φ φ' := by
  intro D S T C μ 𝓕 hμ
  have h0 : IsRealPt (0 : WO S T) := by
    unfold IsRealPt
    simp
  have hg : ∀ x : Frame C.X.Ψ T.rank, gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
    intro x
    unfold gaussR
    simp [hx]
  obtain ⟨a, ha, b, -, hdbl⟩ :=
    GlobalTheory.SW.dbl_zero_and_norm D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even
  obtain ⟨⟨κ, hκ, hk⟩, -⟩ :=
    GlobalTheory.Ker.kZero_onFr_const_entire D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even
  refine ⟨a * κ, mul_ne_zero ha (Complex.ofReal_ne_zero.mpr hκ.ne'), ?_⟩
  intro B hB φ φ' hφ hφ'
  obtain ⟨hdom, hk0⟩ := hk _ (isONFr_xB C B hB)
  have h := GlobalTheory.T.innerProduct_translated_vacua_eq_gaussianKernel D S T C μ 𝓕 hμ _ hdom _ hdom φ φ' hφ hφ' 0 0 h0 h0
  rw [rho_zero_pt, rho_zero_pt, zOf_zero, hg] at h
  have hz : (fun k i => (starRingEnd ℂ) ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [hz, hk0, (hdbl φ φ' hφ hφ').1] at h
  rw [h]
  simp only [map_one, one_mul]
  ring

end GlobalTheory.KerVacIp
