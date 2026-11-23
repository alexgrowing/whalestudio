import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualGramHermitianFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDerivativeTangentVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentRiemannDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameMultiplicitySumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFramePolarizedPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFramePolarizationIsoStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.PullHodge

theorem isDualEigOn_hodge : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (q : T ⟶ Sp (𝓞 κ.c.F)), b ≫ s.T.Z.s = q → ∀ (Q : Out.PolAV T) (θ : Q.A.left ⟶ s.T.Z.t.G.left) (hθ : IsGrpPullback Q.A s.T.Z.t.G b θ), LBIso (s.T.Z.t.PP.L.pull θ) Q.L → ∀ h : VMetric q (LieVB.omega Q.A) Q.g, (PPAS.ofPolAV Q).IsHodge h → ∀ (α : (Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G) ≅ LieVB.omega Q.A), α.hom = LieVB.omegaBase hθ → ∀ h₀ : VMetric q ((Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G)) Q.g, h₀.IsIsometry h α → IsDualEigOn (fun σ' => x.hodge σ') b h₀ := by
  intro P2 PH D A N j S κ s x T b q hbq Q θ hθ hL h hh α hα h₀ hiso
  intro σ' yc y hy u U W hU f f' hyU
  have hW' : b ⁻¹ᵁ U ≤ LieVB.unitSec Q.A ⁻¹ᵁ (θ ⁻¹ᵁ W) := by
    have e : LieVB.unitSec Q.A ⁻¹ᵁ (θ ⁻¹ᵁ W) = b ⁻¹ᵁ (LieVB.unitSec s.T.Z.t.G ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, LieVB.unitSec_comp hθ]
    rw [e]
    exact fun p hp => hU hp
  have horig : ⊤ ≤ (y.1 ≫ LieVB.unitSec Q.A) ⁻¹ᵁ (θ ⁻¹ᵁ W) := by
    rw [Scheme.Hom.comp_preimage]
    exact (top_le_preimage_iff_mem _ _).2 (hW' (mem_ptsIn.1 hyU))
  have e1 := hiso _ (b ⁻¹ᵁ U) (QCoh.pullbackSections b (LieVB.omega s.T.Z.t.G) (le_refl (b ⁻¹ᵁ U)) (LieVB.dUnit s.T.Z.t.G hU f))
    (QCoh.pullbackSections b (LieVB.omega s.T.Z.t.G) (le_refl (b ⁻¹ᵁ U)) (LieVB.dUnit s.T.Z.t.G hU f')) y hyU
  have e2 : ∀ g : Γ(s.T.Z.t.G.left, W), (α.hom.app (b ⁻¹ᵁ U)) (QCoh.pullbackSections b (LieVB.omega s.T.Z.t.G) (le_refl (b ⁻¹ᵁ U)) (LieVB.dUnit s.T.Z.t.G hU g)) = LieVB.dUnit Q.A hW' (θ.appLE W (θ ⁻¹ᵁ W) le_rfl g) := fun g => by
    rw [hα]
    exact LieVB.omegaBase_dUnit hθ hU le_rfl hW' le_rfl g
  refine e1.symm.trans ((congrArg₂ (fun a c => (h.met (σ'.comp (algebraMap (𝓞 κ.c.F) κ.c.F))).form a c y) (e2 f) (e2 f')).trans ?_)
  have key := hh (σ'.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) y
  have kd : Nonempty ((PPAS.ofPolAV Q).RiemannData y.1) := key.1
  obtain ⟨d⟩ := kd
  have e4 := key.2 d (b ⁻¹ᵁ U) (θ ⁻¹ᵁ W) hW' (θ.appLE W (θ ⁻¹ᵁ W) le_rfl f) (θ.appLE W (θ ⁻¹ᵁ W) le_rfl f') hyU
  refine e4.trans ?_
  have hu' : ∀ τ i, Formalism.L2.Pj.IsTanAtG s.T.Z.t (y.1 ≫ b) (u.v τ i) := fun τ i => by rw [hy]; exact u.tan τ i
  choose z v hv1 hv2 hv3 using fun τ i => GlobalTheory.T.exists_tangent_riemann_data D A N j S κ s T b Q θ hθ y.1 d (u.v τ i) (hu' τ i)
  have hG := GlobalTheory.T.eigen_frame_polarization_iso D A N j S κ s x T b Q θ hθ hL (GlobalTheory.T.eigen_frame_polarized_pullback P2 PH D A N j S κ s x T b Q θ hθ hL) σ' yc y.1 hy u d z
    fun τ i => ⟨v τ i, hv1 τ i, hv2 τ i, hv3 τ i⟩
  have hder : ∀ τ i (g : Γ(s.T.Z.t.G.left, W)), TrivSqZeroExt.snd (valR (u.v τ i) W g) =
      ∑ a, z τ i a * d.cov (θ ⁻¹ᵁ W) (θ.appLE W (θ ⁻¹ᵁ W) le_rfl g) a := fun τ i g => by
    rw [← hv3 τ i]
    exact GlobalTheory.T.riemann_derivative_tangent_vector T (PPAS.ofPolAV Q) y.1 d _ θ W horig g (v τ i) (z τ i) (hv1 τ i) (hv2 τ i)
  have u₁ : EigFrame s.T.Z σ' (y.1 ≫ b) := by rw [hy]; exact u
  simp_rw [hder]
  exact GlobalTheory.T.dual_gram_hermitian_frame (fun τ => S.Dw.mult τ) Q.g d.H d.posDef (GlobalTheory.T.eigen_frame_multiplicity_sum D A N j S κ s T b Q θ hθ σ' y.1 u₁) z
    (fun τ => (x.hodge σ').gram yc u τ) (fun τ => (x.hodge σ').pos yc u τ) hG.1 hG.2 _ _

end GlobalTheory.PullHodge
