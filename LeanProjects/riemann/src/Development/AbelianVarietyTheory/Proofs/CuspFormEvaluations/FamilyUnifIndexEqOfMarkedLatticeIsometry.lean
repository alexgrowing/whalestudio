import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnifMatch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

lemma isPeriod_comp_symm {D' D'' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (gam : D'.La ≃ₗ[𝓞 E] D''.La) (hg : ∀ a b, D''.EF (gam a) (gam b) = D'.EF a b)
    {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P) :
    IsPeriod D'' ty (P.comp gam.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hE⟩ := hP
  have hP' : ∀ x, (P.comp gam.symm.toLinearMap.toAddMonoidHom) x = P (gam.symm x) := fun _ => rfl
  have hr : (P.comp gam.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨gam.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨gam x, by rw [hP', LinearEquiv.symm_apply_apply]⟩
  refine ⟨?_, ?_, ?_, ?_, Hm, hH, hpos, ?_⟩
  · intro a x k
    rw [hP', hP', map_smul, h1]
  · intro x y hxy
    exact gam.symm.injective (h2 hxy)
  · rw [hr]; exact h3
  · have : Set.range (P.comp gam.symm.toLinearMap.toAddMonoidHom) = Set.range P := by
      have := congrArg (fun s : AddSubgroup (Fin g → ℂ) => (s : Set (Fin g → ℂ))) hr
      simpa only [AddMonoidHom.coe_range] using this
    rw [this, h4]
  · intro x y
    rw [hP', hP', hE, ← hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

lemma isHolTo_ex {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) {P : (U.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (U.Di i) ty P) : IsHolTo Set.univ (fun z => (U.ex i P z).left) := by
  have h := (U.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  intro V f
  obtain ⟨ho, hd⟩ := h V f
  have hc : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  refine ⟨?_, ?_⟩
  · have h3 := ho.preimage hc.continuous
    have h4 : {b ∈ Set.univ | ⊤ ≤ (U.ex i P b).left ⁻¹ᵁ V} =
        (fun z : Fin g → ℂ => ((0, z) : (Fin 0 → ℂ) × (Fin g → ℂ))) ⁻¹'
          {b ∈ Set.univ ×ˢ Set.univ | ⊤ ≤ (U.ex i P b.2).left ⁻¹ᵁ V} := by
      ext z
      exact ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩
    exact h4 ▸ h3
  · refine hd.comp (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) hc.differentiableOn ?_
    intro z hz
    exact ⟨⟨trivial, trivial⟩, hz.2⟩

theorem index_eq_of_isometry : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ U : FamilyUnif Xo σ ty, ∀ (i j : Fin U.n) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ a b, (U.Di j).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a, ∃ e, gam (U.t i a) = U.t j a + l.M' • e) → i = j := by
  intro hT hL E _ _ _ H D l Xo σ g ty hr hσ hty U i j gam hg ht
  obtain ⟨-, P, hP⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (U.Di i) g ty
    (by rw [(U.sig i).1, (U.sig i).2]; exact hty)
  have hP' := isPeriod_comp_symm gam hg hP
  refine U.disj i j P _ hP hP' ?_
  refine (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hT hL E H D l Xo σ g ty hr hσ hty (U.Di i) (U.Di j)
    (U.t i) (U.t j) P _ _ _ (U.ex i P) (U.ex j _)
    ⟨U.over_σ i P hP, hP, ⟨U.ex_add i P hP, U.ex_onto i P hP, isHolTo_ex U i hP, U.ex_diff i P hP⟩,
      U.ex_ker i P hP, U.ex_lin i P hP, U.ex_weil i P hP, U.ex_eta i P hP, U.ex_etaA i P hP⟩
    ⟨U.over_σ j _ hP', hP', ⟨U.ex_add j _ hP', U.ex_onto j _ hP', isHolTo_ex U j hP', U.ex_diff j _ hP'⟩,
      U.ex_ker j _ hP', U.ex_lin j _ hP', U.ex_weil j _ hP', U.ex_eta j _ hP', U.ex_etaA j _ hP'⟩).2
    ⟨gam, LinearEquiv.refl ℂ _, hg, fun a _ => ?_, fun a => ?_, fun a => ?_⟩
  · obtain ⟨e, he⟩ := ht a
    obtain ⟨c, hc⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    exact ⟨c • e, by rw [he, hc, mul_smul]⟩
  · obtain ⟨e, he⟩ := ht a
    obtain ⟨c, hc⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
    exact ⟨c • e, by rw [he, hc, mul_smul]⟩
  · change P (gam.symm (gam a)) = P a
    rw [LinearEquiv.symm_apply_apply]

end GlobalTheory.UnifMatch
