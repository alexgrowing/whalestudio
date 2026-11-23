import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormCompleteExtensionStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitQuotForm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → P.TorsionIso →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
    ∀ ψ : R →+* V, Function.Injective ψ → ¬ (∀ r ∈ maximalIdeal R, ψ r ∈ maximalIdeal V) →
    ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
    ∀ (T : CDVR) (f : V →+* T.V), Function.Injective f → IsLocalHom f →
    ∀ u : SAB H (Sp T.V), SABMap u t (spMap f ≫ spMap ψ) → ∀ (P' : PELUnif (maximalIdeal T.V) u) (ϖ' : T.V),
    Irreducible ϖ' → ∀ be' ∈ levelForms H 1 P'.D.toPre.X, IsMonomial P'.D.toPre ![ϖ'] ![be'] →
    ∃ (r : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X) (e : ℕ), Function.Surjective r ∧ Associated (f ϖ) (ϖ' ^ e) ∧
      ∀ a b, be' (r a) (r b) = e * be a b := by
  intro E _ _ _ H R _ _ _ t P hR hP V _ _ _ hV ϖ hϖ ψ hψ hnl be hbe hF T f hf hfl u hu P' ϖ' hϖ' be' hbe' hM
  obtain ⟨r, hrs, hr⟩ := GlobalTheory.T.boundary_form_complete_extension E H R t P hR hP V hV ψ hψ hnl T f hf hfl u hu P'
  have hfϖ0 : f ϖ ≠ 0 := (map_ne_zero_iff f hf).2 hϖ.ne_zero
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hfϖ0 hϖ'
  have diag : ∀ y, be' (r y) (r y) = (e : ℤ) * be y y := by
    intro y
    obtain ⟨a, n, ha, hn, hass⟩ := hF y
    obtain ⟨a0, b, ha0, hb, hab⟩ := hr y
    obtain ⟨w, hw⟩ := PsiCoordLocal.exists_unit_of_coord ha0 ha
    obtain ⟨u1, n1, hn1, hb1⟩ := hM.coord hb
    have h0 : Associated (ψ a0) (ϖ ^ n) := by
      refine Associated.trans ?_ hass
      rw [hw, map_mul]
      exact (associated_unit_mul_left _ _ (w.isUnit.map ψ)).symm
    have h1 : Associated b (ϖ' ^ (e * n)) := by
      refine hab.symm.trans ((h0.map f).trans ?_)
      rw [map_pow, pow_mul]
      exact he.pow_pow
    have h2 : Associated b (ϖ' ^ n1 0) := by
      rw [hb1]
      simp only [Fin.prod_univ_one, Matrix.cons_val_zero]
      exact associated_unit_mul_left _ _ u1.isUnit
    obtain ⟨v, hv⟩ := h2.symm.trans h1
    have key : n1 0 = e * n := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ' hϖ' v 1 _ _
      (by rw [Units.val_one, one_mul, mul_comm]; exact hv)
    have := hn1 0
    simp only [Matrix.cons_val_zero] at this
    rw [this, key, hn]
    push_cast
    ring
  refine ⟨r, e, hrs, he, fun a b => ?_⟩
  have hab := diag (a + b)
  have ha := diag a
  have hb := diag b
  have s' := hbe'.1 (r a) (r b)
  have s := hbe.1 a b
  simp only [map_add, LinearMap.add_apply] at hab
  have h2 : (2 : ℤ) * be' (r a) (r b) = 2 * ((e : ℤ) * be a b) := by
    linear_combination hab - ha - hb + s' - (e : ℤ) * s
  exact mul_left_cancel₀ (by norm_num) h2

end GlobalTheory.TraitQuotForm
