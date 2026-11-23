import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystemsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSystemDefectCocycleGlobalFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassSecondSystemEqNegDefectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectedLocIsoOfDefectCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem sysHom_of_K_eq : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S S' : Sys I π s₀, S.Full hI → S.K hI = S'.K hI → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hρ S S' hF hK
  obtain ⟨Φ⟩ := GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems R R₀ I hI π hπ hk X₀ s₀ S S'
  obtain ⟨θ, v, hθ, hv, hvI, hvs⟩ := GlobalTheory.T.exists_liftSystemDefect_cocycle_globalForms R R₀ I hI π hπ hk X₀ s₀ S S' Φ

  have hcl : ∀ w, H1.mk _ (v w) = 0 := by
    intro w
    obtain ⟨f, hf⟩ := hG.surj w
    obtain ⟨c', hc'⟩ := hρ.1 (Form.cl s₀ f)
    have hmem : c' ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) :=
      (GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀ S hρ hF c').2 (by rw [hc', hodgeFiltration_eq_range]; exact ⟨f, rfl⟩)
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hmem
    have hρz : rho hI hk s₀ z = 0 := (hρ.2 z).2 hz
    have hfo : FormOf hI hk y w := ⟨f, by rw [← hc', map_add, hρz, add_zero], hf⟩
    have hm := GlobalTheory.T.crystallineClass_secondSystem_eq_neg_defect R R₀ I hI π hπ hk X₀ s₀ hG.const S S' Φ θ hθ y hy w hfo (v w) (hv w)
    have hy' : y ∈ S'.K hI := hK ▸ hy
    have h0 : S'.r hI y = 0 := hy'
    rw [h0] at hm
    exact neg_eq_zero.1 hm.symm

  let W : Submodule R (C0 S'.F) :=
    { carrier := {g | S'.IsIdealValuedLiftSystemCochain g}
      add_mem' := fun {g g'} hg hg' U ↦ Ideal.add_mem _ (hg U) (hg' U)
      zero_mem' := fun U ↦ Ideal.zero_mem _
      smul_mem' := fun r g hg U ↦ by
        show r • g U ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hg U) }
  have hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0 := by
    intro r hr m hm
    funext U
    show r • m U = 0
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    have h2 := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (S'.F.obj U)) hrI) (hm U)
    rw [← sq, map_sq hI] at h2
    rw [Algebra.smul_def]
    simpa using h2
  have hq : ∀ w, ∃ m ∈ W, d0 S'.F m = ((Z1 S'.F).subtype.toAddMonoidHom.comp v) w := by
    intro w
    obtain ⟨g, hgI, hg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hG.const S' (v w) (hvI w) (hcl w)
    exact ⟨g, hgI, hg⟩
  have hv' : ∀ (r : R) w, ((Z1 S'.F).subtype.toAddMonoidHom.comp v) (π r • w) =
      r • ((Z1 S'.F).subtype.toAddMonoidHom.comp v) w := by
    intro r w
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype, hvs]
    rfl
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hG.proj
    (C0 S'.F) (C1 S'.F) W hW (d0 S'.F) _ hv' hq
  exact GlobalTheory.T.exists_corrected_locIso_of_defect_coboundary R R₀ I hI π hπ hk X₀ s₀ hG.par S S' Φ θ hθ u hu2 hu1 (fun w U V a ↦
    (hv w U V a).symm.trans (congrFun (congrFun (congrFun (hu3 w) U) V) a).symm)

end GlobalTheory.LiftSys
