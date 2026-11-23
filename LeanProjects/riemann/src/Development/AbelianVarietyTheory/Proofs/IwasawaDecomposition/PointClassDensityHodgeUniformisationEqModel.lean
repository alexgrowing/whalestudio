import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationGramLocalHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainModelMetricContDiffAtAndIsUnitStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase

open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix

namespace GlobalTheory.UnifDensTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem aeval_term {κ S : Type} [CommRing S] [Algebra ℝ S] (φ : κ → S) (x : κ) (a s : ℕ) :
    aeval φ ((C ((-1 : ℝ) ^ a) * X x) ^ s) = (algebraMap ℝ S ((-1 : ℝ) ^ a) * φ x) ^ s := by
  rw [map_pow (aeval φ), map_mul (aeval φ), aeval_C, aeval_X]

theorem chernPoly_cast {n a b : ℕ} (hab : a = b) (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    chernPoly (fun u => (G u).submatrix (Fin.cast hab.symm) (Fin.cast hab.symm)) v k = chernPoly G v k := by
  subst hab; rfl

theorem chernTop_pointPoly_eq (H : Host E) (Dw : Datum H) {n : ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → Mat Dw.mult ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) :
    chernTop (pointPoly H Dw) G v =
      GlobalTheory.GoodMetric.chernTop (m := fun _ : GlobalTheory.AllWt.Psi H => Dw.p)
        (∏ τ : GlobalTheory.AllWt.Psi H, (MvPolynomial.C ((-1 : ℝ) ^ Dw.p) * MvPolynomial.X (τ, Dw.p)) ^ (Dw.p + Dw.q - Dw.p))
        (fun u τ => (G u τ.1).submatrix (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)
          (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)) v := by
  unfold chernTop
  congr 3
  rw [pointPoly, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [aeval_term, aeval_term]
  erw [chernPoly_cast (GlobalTheory.HodgeGenUnf.mult_psi τ) (fun u => G u τ.1) v Dw.p]
  exact congrArg (fun m => (algebraMap ℝ (MvPolynomial (Fin n × Fin n) ℂ) ((-1 : ℝ) ^ m) *
    chernPoly (fun u => G u τ.1) v m) ^ (Dw.p + Dw.q - m)) (GlobalTheory.HodgeGenUnf.mult_psi τ)

theorem chernTop_reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] (a : ι → ι') (ha : Function.Bijective a)
    (p s : ℕ) {n : ℕ} (K : ReciprocityTheory.L2DbarEstimates.V n → Mat (fun _ : ι' => p) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p)
                 (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ s) (fun u τ => K u (a τ)) v =
      GlobalTheory.GoodMetric.chernTop (m := fun _ : ι' => p)
        (∏ τ : ι', (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ s) K v := by
  unfold chernTop
  congr 3
  rw [map_prod, map_prod]
  simp only [aeval_term]
  exact Fintype.prod_bijective _ ha _ _ fun τ => rfl

end GlobalTheory.UnifDensTransport

namespace GlobalTheory.UnifDensTransport

theorem letter_bijective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)}
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) :
    Function.Bijective (GlobalTheory.HodgeGenUnf.letter hσ hU k) := by
  obtain ⟨hb, hg, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  refine ⟨fun a b hab => Subtype.ext (hb.1 (congrArg Subtype.val hab)), fun τ' => ?_⟩
  obtain ⟨τ, hτ⟩ := hb.2 τ'.1
  have hm : τ H.rt = H.rt0 := (hg τ).1 (by rw [hτ]; exact ((hU.2.1 k).2 τ'.1).1 τ'.2)
  exact ⟨⟨τ, hm⟩, Subtype.ext hτ⟩

theorem chernTop_pointPoly_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : (U.X k).Ψ => Dw.p) (∏ τ : (U.X k).Ψ, (MvPolynomial.C ((-1 : ℝ) ^ Dw.p) * MvPolynomial.X (τ, Dw.p)) ^ (Dw.p + Dw.q - Dw.p)) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA
  rw [chernTop_pointPoly_eq, ← chernTop_reindex _ (letter_bijective hσ hU k)]
  choose cc hcc g hg hgu hG using GlobalTheory.T.hodge_metric_uniformisation_gram_local_holomorphic E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA
  exact GlobalTheory.PointChern.chernTop_changeFrame _ _ _ (fun w τ => g τ w) cc v hcc hg hgu
    (fun τ => (GlobalTheory.T.boundedDomainModelMetric_contDiffAt_and_isUnit _ _ _ _ h v hv _).1) (fun τ => (GlobalTheory.T.boundedDomainModelMetric_contDiffAt_and_isUnit _ _ _ _ h v hv _).2) (Filter.eventually_all.2 hG)

end GlobalTheory.UnifDensTransport
