import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionArchimedeanFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameGram

theorem inner_eq_pi_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x y : D.B.carrier) (c c' : Fin D.g → ℂ), D.IsVec a x c → D.IsVec a y c' → ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] y) : ℂ) = Real.pi * a.herm c' c := by
  intro E _ _ _ H L _ _ D σ a x y c c' hx hy
  obtain ⟨t', m, hP, hA⟩ := GlobalTheory.T.complex_abelian_fibre_ample E H L D σ
  obtain ⟨hab, g, u, Hm, χ, hAH, d₁, d₂⟩ := FrameEx.exists_goodUnif E H _ D.t (emb σ) t' m hP hA
  have hp : IsGrpPullback t'.G D.t.G (emb σ) m.φ := m.cart
  obtain ⟨v, hlift, vA, hvA, hdiff⟩ := hx
  obtain ⟨w, hlift', wA, hwA, hdiff'⟩ := hy
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L)) = emb σ := Category.comp_id _
  let v₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk v.left (by simpa using Over.w v)
  let w₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk w.left (by simpa using Over.w w)
  have hl₀ : D.MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 D.t.G.left) x v₀ := hlift
  have hl₁ : D.MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 D.t.G.left) y w₀ := hlift'
  obtain ⟨hL, hvt, hwt, A', _, φ', g', u', Hm', χ', p, q, a', b', hp', hah', ep, eq', dp, dq, hval⟩ :=
    D.fib σ x y v₀ w₀ hl₀ hl₁
  have hp₀ : IsGrpPullback t'.G D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) m.φ :=
    IsGrpPullback.congr hp e.symm rfl
  have hpz : IsGrpPullback A' D.t.G (emb σ) φ' := IsGrpPullback.congr hp' e rfl
  let x₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm v₀
  let y₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm w₀
  have hx₁ : HodgeLin.tanEquiv hp₀ x₁ = v₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have hy₁ : HodgeLin.tanEquiv hp₀ y₁ = w₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have tx₁ : IsTangent x₁ := (HodgeLin.isTangent_iff hp₀ x₁).2 (by rw [hx₁]; exact hvt)
  have ty₁ : IsTangent y₁ := (HodgeLin.isTangent_iff hp₀ y₁).2 (by rw [hy₁]; exact hwt)
  have lx₁ : x₁.left ≫ m.φ = v.left := congrArg (fun r => r.left) hx₁
  have ly₁ : y₁.left ≫ m.φ = w.left := congrArg (fun r => r.left) hy₁
  obtain ⟨cx, hcx, -⟩ := d₁ x₁ tx₁
  obtain ⟨cy, hcy, -⟩ := d₁ y₁ ty₁
  have T1 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G a.A m.φ a.φ g D.g u a.u Hm a.Hm χ a.χ D.t.PP.isLB
    hab hp a.cart d₁ d₂ hAH a.ah y₁ x₁ wA vA cy cx c' c ty₁ tx₁ (hwA.trans ly₁.symm) (hvA.trans lx₁.symm) hcy hcx
    hdiff' hdiff
  have T2 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G A' m.φ φ' g g' u u' Hm Hm' χ χ' D.t.PP.isLB
    hab hp hpz d₁ d₂ hAH hah' y₁ x₁ q p cy cx b' a' ty₁ tx₁ (eq'.trans ly₁.symm) (ep.trans lx₁.symm) hcy hcx dq dp
  have hH : a.herm c' c = hermForm Hm' b' a' := T1.trans T2.symm
  rw [hH]
  exact hval

end GlobalTheory.CompanionTheory.Ar.Sl.FrameGram
