import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralDetSubOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors TensorProduct

namespace GlobalTheory.HalfLevelDet

theorem det_baseChange_eq {E : Type} [Field E] [NumberField E] {r : ℕ} {L : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] (hr : Module.finrank (𝓞 E) L = r)
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (f : L →ₗ[𝓞 E] L) (g : Matrix (Fin r) (Fin r) E) (hg : ∀ a, φ (f a) = g *ᵥ φ a) :
    LinearMap.det (LinearMap.baseChange E f) = g.det := by
  have hb := TensorProduct.isBaseChange (𝓞 E) L E
  have hl := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E _).2 hb
  have h1 : Module.finrank E (E ⊗[𝓞 E] L) = Module.finrank E (Fin r → E) := by
    rw [IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl,
      IsLocalizedModule.finrank_eq (𝓞 E)⁰ (TensorProduct.mk (𝓞 E) E L 1) le_rfl, hr]
    simp
  let F : E ⊗[𝓞 E] L →ₗ[E] (Fin r → E) := φ.liftBaseChange E
  have hF : ∀ (c : E) (a : L), F (c ⊗ₜ a) = c • φ a := fun c a => by simp [F]
  have hsurj : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ a, by rw [hF, one_smul]⟩
  have hinj : Function.Injective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h1).2 hsurj
  let e : (E ⊗[𝓞 E] L) ≃ₗ[E] (Fin r → E) := LinearEquiv.ofBijective F ⟨hinj, hsurj⟩
  have hc : ∀ x, e (LinearMap.baseChange E f x) = g *ᵥ e x := by
    intro x
    change F _ = g *ᵥ F x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a => rw [LinearMap.baseChange_tmul, hF, hF, hg, Matrix.mulVec_smul]
    | add x y hx hy => rw [map_add, map_add, map_add, Matrix.mulVec_add, hx, hy]
  rw [← LinearMap.det_conj (LinearMap.baseChange E f) e, ← LinearMap.det_toLin']
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [hc]

theorem det_eq_one_of_trivial_on_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (γ : Dw.La ≃ₗ[𝓞 E] Dw.La), (∀ a b, Dw.EF (γ a) (γ b) = Dw.EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ e, γ a = a + l.M • e) → LinearMap.det (LinearMap.baseChange E (γ : Dw.La →ₗ[𝓞 E] Dw.La)) = 1 := by
  intro E _ _ _ H Dw l γ hiso hhalf
  have := Dw.fin
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Dw l γ hiso hhalf
  obtain ⟨ξ, hξ0, hξ⟩ : ∃ δ : E, δ ≠ 0 ∧ cc δ = -δ := by
    have hne : IsCMField.complexConj E ≠ 1 := IsCMField.complexConj_ne_one E
    obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
      by_contra h
      push Not at h
      exact hne (AlgEquiv.ext h)
    refine ⟨x - IsCMField.complexConj E x, sub_ne_zero.mpr hx.symm, ?_⟩
    unfold cc
    rw [map_sub, IsCMField.complexConj_apply_apply]
    ring
  obtain ⟨Gm, φ, hM⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw ξ hξ hξ0 _ rfl
  obtain ⟨g, hgu, hg⟩ :=
    GlobalTheory.IsoExt.exists_unitary_of_isometry E H Dw Dw _ ξ Gm φ φ γ hξ hM hM hiso
  rw [det_baseChange_eq Dw.rank φ hM.2.1 (γ : Dw.La →ₗ[𝓞 E] Dw.La) g hg]
  refine GlobalTheory.CongruenceDet.det_eq_one E _ l.M Gm (LinearMap.range φ) g hM.2.2.2.1
    (Submodule.fg_range φ) hM.2.1 l.three_le ⟨hgu, fun x => ⟨?_, ?_⟩⟩ ?_
  · rintro ⟨a, rfl⟩
    exact ⟨γ a, hg a⟩
  · rintro ⟨a, ha⟩
    refine ⟨γ.symm a, ?_⟩
    have h := hg (γ.symm a)
    rw [LinearEquiv.apply_symm_apply, ha] at h
    have h' := congrArg (fun v => (g⁻¹ : GL _ E).1 *ᵥ v) h
    simpa [Matrix.mulVec_mulVec] using h'.symm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := hfull a
    exact ⟨φ e, ⟨e, rfl⟩, by rw [← hg, he, map_add, map_nsmul]⟩

end GlobalTheory.HalfLevelDet
