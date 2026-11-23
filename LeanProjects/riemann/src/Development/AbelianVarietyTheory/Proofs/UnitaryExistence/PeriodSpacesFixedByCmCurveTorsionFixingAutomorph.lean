import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PermutesPeriodSpacesIdOfFixesCmCurveTorsion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexLinearOfPureTypes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingAtConjugateSplitPointTransportedTwistedStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPeriodSpacePermOfComplexAutStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPeriodAnyLevelStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.AnyLevel

theorem conj_point_eq_of_isSplit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0) (hty : IsTypeFn H D.p D.q ty) (τ : ℂ ≃+* ℂ)
    (hτσ : (τ : ℂ →+* ℂ).comp σ = σ)
    (hfix : FixesCurve H τ l.M') (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hs : IsSplit hP) : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
  obtain ⟨C, io, hC⟩ := hfix
  have hτ : τ H.rt0 = H.rt0 := by
    rw [← hσ]
    exact RingHom.congr_fun hτσ _
  obtain ⟨i', P', hP', hu⟩ := F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P)
    (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])
  obtain ⟨Φ, hE, hp, hm, hlevA, hlev⟩ := GlobalTheory.T.marking_at_conjugate_splitPoint_transported_twisted E H D l Xo σ g ty F hD hσ hty τ hτ C io hC.1 i P hP i' P' hP' hs
    hu.symm (1, 0) hC
  obtain ⟨L, hL⟩ := exists_complex_linear_of_pure_types E H _ _ g ty P P' hP hP' Φ hs (fun a ha => (hp a).2 ha)
    (fun a ha => (hm a).2 ha)
  have hw : wE H (1, 0) = 1 := by simp [wE]
  have hmem : ∀ v, F.t i v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0) := fun v => by
    rw [show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hs]; trivial
  have hA' : ∀ v, ∃ x, Φ (F.t i v) = F.t i' v + l.A • x := fun v => by
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hmem v)
    obtain ⟨e, he⟩ := hlevA v a ha b hb hab.symm
    rw [hw, map_one, one_smul, one_smul, hab] at he
    exact ⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩
  refine hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i')
      (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P')
      ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, F.ex_onto i P hP, isHolTo_ex_at_period F i P hP,
        (F.ex_diff i P hP).1, (F.ex_diff i P hP).2⟩, F.ex_ker i P hP, F.ex_lin i P hP, F.ex_weil i P hP,
        F.ex_eta i P hP, F.ex_etaA i P hP⟩
      ⟨F.over_σ i' P' hP', hP', ⟨F.ex_add i' P' hP', F.ex_onto i' P' hP', isHolTo_ex_at_period F i' P' hP',
        (F.ex_diff i' P' hP').1, (F.ex_diff i' P' hP').2⟩, F.ex_ker i' P' hP', F.ex_lin i' P' hP',
        F.ex_weil i' P' hP', F.ex_eta i' P' hP', F.ex_etaA i' P' hP'⟩).2 ⟨Φ, L, hE, fun v hv => ?_, hA', hL⟩).symm
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hmem v)
  obtain ⟨e, he⟩ := hlev v hv a ha b hb hab.symm
  rw [hw, map_one, one_smul, one_smul, hab] at he
  exact ⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩

theorem permutes_id_of_fixesCurve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ τ : ℂ ≃+* ℂ, (∀ x : KA l, τ (x : ℂ) = x) → FixesCurve H τ l.M' → ConjugationPermutesPeriods F τ id := by
  intro E _ _ _ H D l Xo σ g ty F hpq hσ hty hσx hsig τ hτ hC
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_periodSpace_perm_of_complexAut E H D l Xo σ g ty F hpq hσ hty hσx τ hτ
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := RingHom.ext fun x => by
    show τ (σ x) = σ x
    rw [hσx, hτ]
  have hid : ∀ i, π i = i := by
    intro i
    obtain ⟨P, hP, hs⟩ := GlobalTheory.T.exists_split_period_any_level E H D l Xo σ g ty F hpq hσ hty hsig i
    have h1 := conj_point_eq_of_isSplit F hpq hσ hty τ hτσ hC i P hP hs
    obtain ⟨P', hP', h2⟩ := hπ i P hP
    exact (F.disj i (π i) P P' hP hP' (h1.symm.trans h2)).symm
  have : (π : Fin F.n → Fin F.n) = id := funext hid
  rwa [this] at hπ

end GlobalTheory.CompRat.AnyLevel
