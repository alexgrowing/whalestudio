import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalOrderBoundaryFormEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedUniformisationPolarisedTripleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormBaseChangeDvrStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitQuot

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R → P.TorsionIso →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
    ∀ ψ : R →+* V, Function.Injective ψ → ¬ IsLocalHom ψ →
    ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap (f.comp ψ))) (P' : PELUnif (maximalIdeal V') t')
        (be' : LinearMap.BilinForm ℤ P'.D.toPre.X) (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
        be' ∈ levelForms H 1 P'.D.toPre.X ∧ Function.Surjective ρ ∧ (∀ a b, be' (ρ a) (ρ b) = be a b) ∧
        IsMonomial P'.D.toPre ![f ϖ] ![be'] := by
  intro E _ _ _ H R _ _ _ t P hR hT V _ _ _ hV ϖ hϖ ψ hψ hnl be hbe hF
  obtain ⟨PP', cub, sym, adj, prim, mV, -⟩ := sabPull CubePf.cubePull (spMap ψ) t
  have j : Function.Injective ((algebraMap V (FractionRing V)).comp ψ) := (IsFractionRing.injective V _).comp hψ
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift j
  have e : spMap gK ≫ jK R = jK V ≫ spMap ψ :=
    (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm
  have hp := GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap gK) e
  obtain ⟨V', _, _, _, f, hV', hf, hfl, hfϖ, t', m', ⟨P'⟩⟩ := GlobalTheory.T.exists_unramified_uniformisation_polarisedTriple E H V hV ϖ hϖ _ hp
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mV m'
  have hsp : spMap f ≫ spMap ψ = spMap (f.comp ψ) := GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl
  have n' : SABMap t' t (spMap (f.comp ψ)) := hsp ▸ n
  obtain ⟨ρ, hρs, hρ⟩ := GlobalTheory.T.boundary_form_base_change_dvr E H R t P hR hT V' hV' (f.comp ψ) (hf.comp hψ)
    (fun hl => hnl ⟨fun a ha => hl.map_nonunit a (ha.map f)⟩) t' n' P'
  obtain ⟨hd, hc, hz⟩ := hV'
  obtain ⟨be', hbe', hmon, -⟩ := exists_periodForm P' hfϖ
  refine ⟨V', inferInstance, inferInstance, inferInstance, f, ⟨hd, hc, hz⟩, hf, hfl, hfϖ, t', n', P', be', ρ, hbe',
    hρs, ?_, hmon⟩
  have hdiag : ∀ y, be' (ρ y) (ρ y) = be y y := by
    intro y
    obtain ⟨r, k, hr, hk, ha⟩ := hF y
    obtain ⟨u, m, hm, hc⟩ := hmon (ρ y)
    have h1 := hρ y r _ hr hc
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, RingHom.comp_apply] at h1
    have h2 : Associated ((f ϖ) ^ k) ((f ϖ) ^ (m 0)) := by
      have h3 : Associated (f (ψ r)) ((f ϖ) ^ k) := by
        rw [← map_pow]; exact ha.map f
      exact h3.symm.trans (h1.trans (associated_unit_mul_left _ _ u.isUnit))
    have h4 := BalancedTrait.pow_eq_of_associated hfϖ h2
    have h5 := hm 0
    simp only [Matrix.cons_val_zero] at h5
    rw [h5, hk, h4]
  intro a b
  have s1 := BalancedTrait.two_mul_apply be (mem_levelForms.1 hbe).1 a b
  have s2 := BalancedTrait.two_mul_apply be' (mem_levelForms.1 hbe').1 (ρ a) (ρ b)
  rw [← map_add, hdiag, hdiag, hdiag] at s2
  omega

end GlobalTheory.TraitQuot
