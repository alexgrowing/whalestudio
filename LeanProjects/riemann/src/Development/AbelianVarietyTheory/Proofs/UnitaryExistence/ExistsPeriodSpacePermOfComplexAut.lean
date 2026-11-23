import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPermPeriodSpacesComplexAut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevelStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentsPeriodSpacesAnyLevelStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjPermutesAnyLevel

open GlobalTheory.ConjPermutes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_map (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : ∀ x : KA l, σ x = (x : ℂ)) (τ : ℂ ≃+* ℂ)
    (hτ : ∀ x : KA l, τ (x : ℂ) = x) :
    ∃ π : Fin F.n → Fin F.n, ConjugationPermutesPeriods F τ π := by
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := RingHom.ext fun x => by
    show τ (σ x) = σ x
    rw [hA, hτ]
  have hon : ∀ i P, IsPeriod (F.Di i) ty P → ∃ i' P', IsPeriod (F.Di i') ty P' ∧
      F.u i' P' = spMap (τ : ℂ →+* ℂ) ≫ F.u i P := fun i P hP =>
    F.onto _ (by rw [Category.assoc, F.over_σ i P hP, ConjPermutes.spMap_comp, hτσ])
  choose P₀ hP₀ using exists_period F hty
  choose π P₁ hP₁ hu₁ using fun i => hon i (P₀ i) (hP₀ i)
  refine ⟨π, fun i P hP => ?_⟩
  obtain ⟨i', P', hP', hu'⟩ := hon i P hP
  obtain ⟨c₀⟩ : Nonempty (Coeff l) := inferInstance
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_coeffField_idempotents_periodSpaces_anyLevel E H D l Xo σ g ty F hD hσ hty hA c₀
  obtain ⟨e, he, hv⟩ := hc (π i)
  let j : c.F →+* ℂ := (τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom
  have hj : (τ : ℂ →+* ℂ).comp j = c.F.val.toRingHom := RingHom.ext fun a => τ.apply_symm_apply _
  have hjσ : σ = j.comp (IntermediateField.inclusion c.le).toRingHom := RingHom.ext fun x => by
    rw [hA]
    exact (τ.symm_apply_eq.2 (hτ x).symm).symm
  have w : ∀ Q, IsPeriod (F.Di i) ty Q →
      F.u i Q ≫ Xo.s = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := fun Q hQ => by
    rw [F.over_σ i Q hQ, ConjPermutes.spMap_comp, ← hjσ]
  have key : ∀ Q (hQ : IsPeriod (F.Di i) ty Q) k Q', IsPeriod (F.Di k) ty Q' →
      F.u k Q' = spMap (τ : ℂ →+* ℂ) ≫ F.u i Q →
      τ (valAt' (X := Xo.XF c) (pullback.lift _ _ (w Q hQ)) ⊤ e) = if k = π i then 1 else 0 := by
    intro Q hQ k Q' hQ' h
    rw [← hv k Q' hQ' (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift _ _ (w Q hQ))
      (by rw [Category.assoc, pullback.lift_fst, h]) (by rw [Category.assoc, pullback.lift_snd, ConjPermutes.spMap_comp, hj]),
      valAt'_spMap_comp]
    rfl
  have hconst := GlobalTheory.T.regularFunction_const_of_finite_values_any_level E H D l Xo σ g ty F hD hσ hty c j e {0, 1} (Set.toFinite _)
    (fun x _ => valAt'_idem x he) i P (P₀ i) hP (hP₀ i) (pullback.lift _ _ (w P hP))
    (pullback.lift _ _ (w _ (hP₀ i))) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have h₁ := key P hP i' P' hP' hu'
  rw [hconst, key _ (hP₀ i) (π i) (P₁ i) (hP₁ i) (hu₁ i), if_pos rfl] at h₁
  obtain rfl : i' = π i := by
    by_contra hne
    rw [if_neg hne] at h₁
    exact one_ne_zero h₁
  exact ⟨P', hP', hu'.symm⟩

theorem exists_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ τ : ℂ ≃+* ℂ, (∀ x : KA l, τ (x : ℂ) = x) → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  intro E _ _ _ H D l Xo σ g ty F hD hσ hty hA τ hτ
  obtain ⟨π, hπ⟩ := exists_map F hD hσ hty hA τ hτ
  obtain ⟨π', hπ'⟩ := exists_map F hD hσ hty hA τ.symm (fun x => τ.symm_apply_eq.2 (hτ x).symm)
  have hinv : Function.LeftInverse π' π := fun i => by
    obtain ⟨P, hP⟩ := exists_period F hty i
    obtain ⟨P', hP', h'⟩ := hπ i P hP
    obtain ⟨P'', hP'', h''⟩ := hπ' (π i) P' hP'
    have e : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := RingHom.ext fun a => τ.symm_apply_apply a
    have e' : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id (CommRingCat.of ℂ)
    rw [← h', ← Category.assoc, ConjPermutes.spMap_comp, e, e', Category.id_comp] at h''
    exact (F.disj _ _ _ _ hP hP'' h'').symm
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 hinv.injective), hπ⟩

end GlobalTheory.ConjPermutesAnyLevel
