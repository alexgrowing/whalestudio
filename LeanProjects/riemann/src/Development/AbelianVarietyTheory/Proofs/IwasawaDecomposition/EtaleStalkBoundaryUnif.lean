import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryEtaleStalkUnif
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryEtaleStalkForms
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.ChartTrait

theorem exists_surjective_formAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (t : SAB H (Sp R)), SABMap t X.t ξ → ∀ (P : PELUnif (maximalIdeal R) t), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W) (tW : SAB H (Sp W)), SABMap tW X.t (spMap f ≫ ξ) → ∀ (PW : PELUnif (maximalIdeal W) tW), Set.range (jK W ≫ spMap f ≫ ξ) ⊆ Set.range X.j → ∀ be ∈ levelForms H 1 PW.D.toPre.X, IsMonomial PW.D.toPre ![ϖ] ![be] → ∃ e : P.D.toPre.X →ₗ[𝓞 E] PW.D.toPre.X, Function.Surjective e ∧ FormAt P.D.toPre f ϖ (be.compl₁₂ e.toAddMonoidHom.toIntLinearMap e.toAddMonoidHom.toIntLinearMap) := by
  intro E _ _ _ H D l Xo c X R _ _ _ ξ t m P hR _ _ hT W _ _ _ hW ϖ hϖ f tW mW PW hχ be _ hmon
  by_cases hf : IsLocalHom f
  · obtain ⟨e, he⟩ := GlobalTheory.ChartCentre.exists_equiv_formAt X ξ t m P hR hT W hW ϖ hϖ (spMap f ≫ ξ) tW mW PW hχ be hmon
      W hW (RingHom.id W) f Function.injective_id inferInstance hf
      (by rw [← Category.assoc, GlobalTheory.Ex.UnifModel.spMap_comp (d := f) fun _ => rfl])
    exact ⟨e.toLinearMap, e.surjective, he⟩
  · obtain ⟨ρ, hρ, hc⟩ := GlobalTheory.FarTrait.exists_quot_coord X ξ t m P hR hT hW f hf (fun p => hχ ⟨p, rfl⟩) tW mW PW
    refine ⟨ρ, hρ, fun y => ?_⟩
    obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff P.D.toPre y).2
      (GlobalTheory.PeriodFormCompare.psiIn_top P.D y)
    obtain ⟨u, n, hn, hcW⟩ := hmon (ρ y)
    refine ⟨r, n 0, hr, by simpa using hn 0, (hc y r _ hr hcW).trans ?_⟩
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero]
    exact associated_unit_mul_left _ _ u.isUnit

end GlobalTheory.ChartTrait
