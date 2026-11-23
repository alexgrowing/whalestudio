import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeOfImNeZero

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem colNorm_exists_im_ne_zero {K : Type} [Field K] [IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (h a)

theorem colNorm_normAt_column (D : D7) (u : D.what₂.Word) (x : (D.div.Nu u).V) :
    Formalism.HermitianLatticesTheory.normAt (D.div.Nu u).b (D.div.Nu u).X (InfinitePlace.mk D.what₂.embLL) x = ‖D.jN u x‖ := by
  rw [D.nuIn_norm, normAt_sq_eq_majAt_re, (D.fm u).emb_norm, ← D.nuIn_jN, norm_eq_sqrt_re_inner (𝕜 := ℂ), D.eMu_isom]
  rfl

theorem colNorm_of_nuTie : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), R.NuTie → M.ColNorm := by
  intro D Bs A X fc s R cr M h u
  obtain ⟨L, hL⟩ := h u
  refine ⟨1, one_pos, fun φ => ?_⟩
  rw [one_mul]
  have htw : ∀ a, (InfinitePlace.mk D.what₂.embLL).embedding a = cj s (D.what₂.embLL a) := by
    rw [← R.v0]; exact R.twist
  have := fnorm_cjv_eq_norm D.what₂.LL D.what₂.embLL s htw (colNorm_exists_im_ne_zero _) (D.div.Nu u) _ L _ (R.eNu u) hL
    (D.what₂.Mu u) (D.jN u) (M.cφ u) (colNorm_normAt_column D u) (M.cφ_eq u) φ
  rw [← R.v0] at this
  exact this

end GlobalTheory.Mem.SJ
