import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesOnPeriodSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentCuttingPeriodSpacesStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjPermutes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem ringHom_ext {l : Level H} (hA : l.A = 1) {f f' : KA l →+* ℂ} (h : f (baseKA l).ρ = f' (baseKA l).ρ) :
    f = f' := by
  have hz : zeta l.A = 1 := by
    unfold zeta
    rw [hA]
    simp
  suffices key : ∀ (x : ℂ) (hx : x ∈ IntermediateField.adjoin ℚ ({H.rt0, zeta l.A} : Set ℂ)),
      f ⟨x, hx⟩ = f' ⟨x, hx⟩ by
    ext y
    exact key y.1 y.2
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h
    · exact (congrArg f (Subtype.ext hz)).trans ((map_one f).trans
        ((map_one f').symm.trans (congrArg f' (Subtype.ext hz)).symm))
  | algebraMap r =>
    show f (algebraMap ℚ (KA l) r) = f' (algebraMap ℚ (KA l) r)
    rw [eq_ratCast (algebraMap ℚ (KA l)) r, map_ratCast, map_ratCast]
  | add x y hx hy ihx ihy =>
    show f (⟨x, hx⟩ + ⟨y, hy⟩) = f' (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | inv x hx ih =>
    show f (⟨x, hx⟩⁻¹) = f' (⟨x, hx⟩⁻¹)
    rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
    show f (⟨x, hx⟩ * ⟨y, hy⟩) = f' (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

theorem valAt'_top {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) :
    valAt' x ⊤ f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom f) := by
  unfold valAt'
  rw [dif_pos (by simp)]
  unfold valAt
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem valAt'_spMap_comp {X : Scheme.{0}} (τ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) :
    valAt' (spMap τ ≫ x) ⊤ f = τ (valAt' x ⊤ f) := by
  rw [valAt'_top, valAt'_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom τ)
  have h2 := congrArg (fun φ => φ.hom (x.appTop.hom f)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simp only [spMap, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  exact h2

theorem valAt'_idem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {e : Γ(X, ⊤)} (he : e * e = e) :
    valAt' x ⊤ e ∈ ({0, 1} : Set ℂ) := by
  rw [valAt'_top]
  have h : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) *
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) := by
    rw [← map_mul, ← map_mul, he]
  generalize (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) = v at h ⊢
  have h2 : v * (v - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h0 | h1
  · simp [h0]
  · simp [sub_eq_zero.1 h1]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_period (F : FamilyUnif Xo σ ty) (hty : IsTypeFn H D.p D.q ty) (i : Fin F.n) :
    ∃ P, IsPeriod (F.Di i) ty P := by
  obtain ⟨hp, hq⟩ := F.sig i
  exact GlobalTheory.PeriodNonempty.exists_isPeriod E H (F.Di i) g ty (by rw [hp, hq]; exact hty)

private theorem key_lemma' (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0)
    (i k k' : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (Q : (F.Di k).La →+ (Fin g → ℂ))
    (Q' : (F.Di k').La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    (hQ : IsPeriod (F.Di k) ty Q) (hQ' : IsPeriod (F.Di k') ty Q')
    (h1 : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u k Q) (h2 : spMap (τ : ℂ →+* ℂ) ≫ F.u i P' = F.u k' Q') :
    k' = k := by
  classical
  obtain ⟨c, -, he⟩ := GlobalTheory.T.exists_coeffField_idempotent_cutting_periodSpaces E H D l Xo σ g ty F hD hσ hty hA (Classical.arbitrary _)
  obtain ⟨e, hee, hev⟩ := he k
  have hs : τ.symm H.rt0 = H.rt0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hτ.symm
  have hjc : σ = ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom).comp
      (IntermediateField.inclusion c.le).toRingHom :=
    ringHom_ext hA (hσ.trans hs.symm)
  have hw : F.u i P ≫ Xo.s = spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.10 i P hP, spMap_comp, ← hjc]
  have hw' : F.u i P' ≫ Xo.s = spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.10 i P' hP', spMap_comp, ← hjc]
  have hsnd : spMap (τ : ℂ →+* ℂ) ≫ spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) =
      spMap c.F.val.toRingHom := by
    rw [spMap_comp]
    congr 1
    ext z
    simp
  have hv1 := hev k Q hQ (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift (F.u i P) _ hw)
    (by rw [Category.assoc, pullback.lift_fst]; exact h1)
    (by rw [Category.assoc, pullback.lift_snd]; exact hsnd)
  have hv2 := hev k' Q' hQ' (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift (F.u i P') _ hw')
    (by rw [Category.assoc, pullback.lift_fst]; exact h2)
    (by rw [Category.assoc, pullback.lift_snd]; exact hsnd)
  have heq := GlobalTheory.CompRat.valAt_eq_of_finite_values E H D l Xo σ g ty F hD hσ hty hA c
    ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) e {0, 1}
    (Set.toFinite _) (fun y _ => valAt'_idem y hee) i P P' hP hP'
    (pullback.lift (F.u i P) _ hw) (pullback.lift (F.u i P') _ hw')
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  rw [valAt'_spMap_comp, if_pos rfl] at hv1
  rw [valAt'_spMap_comp, ← heq, hv1] at hv2
  by_contra hne
  rw [if_neg hne] at hv2
  exact one_ne_zero hv2

private theorem spMap_comp_u_comp_s_eq_of_fixes_rt0 (F : FamilyUnif Xo σ ty) (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1)
    (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) : (spMap (τ : ℂ →+* ℂ) ≫ F.u i P) ≫ Xo.s = spMap σ := by
  rw [Category.assoc, F.10 i P hP, spMap_comp]
  congr 1
  exact ringHom_ext hA (by rw [RingHom.comp_apply, hσ]; exact hτ)

theorem exists_map (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0) :
    ∃ π : Fin F.n → Fin F.n, ConjugationPermutesPeriods F τ π := by
  classical
  choose P0 hP0 using fun i => exists_period F hty i
  choose k Q hQ hkQ using fun i => F.18 _ (spMap_comp_u_comp_s_eq_of_fixes_rt0 F hσ hA τ hτ i (P0 i) (hP0 i))
  refine ⟨k, fun i P hP => ?_⟩
  obtain ⟨k', Q', hQ', hk'⟩ := F.18 _ (spMap_comp_u_comp_s_eq_of_fixes_rt0 F hσ hA τ hτ i P hP)
  have hkk := key_lemma' F hD hσ hty hA τ hτ i (k i) k' (P0 i) P (Q i) Q' (hP0 i) hP (hQ i) hQ'
    (hkQ i).symm hk'.symm
  subst hkk
  exact ⟨Q', hQ', hk'.symm⟩

theorem exists_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  intro E _ _ _ H D l Xo σ g ty F hD hσ hty hA τ hτ
  obtain ⟨π, hπ⟩ := exists_map F hD hσ hty hA τ hτ
  have hτ' : τ.symm H.rt0 = H.rt0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hτ.symm
  obtain ⟨π', hπ'⟩ := exists_map F hD hσ hty hA τ.symm hτ'
  have hinv : ∀ i, π' (π i) = i := by
    intro i
    obtain ⟨P, hP⟩ := exists_period F hty i
    obtain ⟨Q, hQ, h1⟩ := hπ i P hP
    obtain ⟨R, hR, h2⟩ := hπ' (π i) Q hQ
    have h3 : spMap (τ.symm : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
      rw [← Category.assoc, spMap_comp]
      have hid : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := by
        ext z
        simp
      rw [hid]
      unfold spMap
      simp
    rw [h1, h2] at h3
    exact F.19 _ _ _ _ hR hP h3
  have hinj : Function.Injective π := fun a b hab => by rw [← hinv a, ← hinv b, hab]
  exact ⟨Equiv.ofBijective π hinj.bijective_of_finite, hπ⟩

end GlobalTheory.ConjPermutes
