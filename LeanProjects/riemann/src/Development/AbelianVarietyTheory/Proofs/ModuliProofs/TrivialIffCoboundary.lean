import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructureStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.EpsBundle

theorem res_constFn' {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a := by
  exact congrArg (fun f => CommRingCat.Hom.hom f ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem res_appLE {Y Y' : Scheme.{0}} (ρ : Y' ⟶ Y) {O O' : Y.Opens} {W W' : Y'.Opens}
    (hW : W' ≤ W) (hO : O' ≤ O) (h : W ≤ ρ ⁻¹ᵁ O) (h' : W' ≤ ρ ⁻¹ᵁ O') (a : Γ(Y, O)) :
    resG Y' hW ((ρ.appLE O W h).hom a) = (ρ.appLE O' W' h').hom (resG Y hO a) := by
  unfold resG
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem eps_sq {X : Scheme.{0}} (p : X ⟶ Sp (DualNumber ℂ)) (U : X.Opens) :
    constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := by
  unfold constFn
  rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

theorem decomp {Y Y' : Scheme.{0}} (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (O : Y.Opens)
    (H : ∀ F : Γ(Y', ρ ⁻¹ᵁ O), ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2)
    (W : Y'.Opens) (hW : ρ ⁻¹ᵁ O = W) (h : W ≤ ρ ⁻¹ᵁ O) (F : Γ(Y', W)) :
    ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.appLE O W h).hom ab.1 + constFn π _ DualNumber.eps * (ρ.appLE O W h).hom ab.2 := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app]
  exact H F

theorem uniq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) {a b a' b' : A}
    (h : φ a + e * φ b = φ a' + e * φ b') : a = a' ∧ b = b' := by
  have := (H (φ a + e * φ b)).unique (y₁ := (a, b)) (y₂ := (a', b')) rfl h
  exact Prod.mk.inj this

theorem unit_form {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B) (he : e * e = 0)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) (u : Bˣ) :
    ∃ b b' c : A, b * b' = 1 ∧ (u : B) = φ b + e * φ c := by
  obtain ⟨⟨b, c⟩, h, -⟩ := H u
  obtain ⟨⟨b', c'⟩, h', -⟩ := H (u⁻¹ : Bˣ)
  refine ⟨b, b', c, ?_, h⟩
  have h1 : (u : B) * (u⁻¹ : Bˣ) = 1 := u.mul_inv
  rw [h', h] at h1
  refine (uniq φ e H (a := b * b') (b := b * c' + c * b') (a' := 1) (b' := 0) ?_).1
  simp only [map_mul, map_add, map_one, map_zero] at h1 ⊢
  linear_combination h1 - (φ c * φ c') * he

theorem overlap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B) (he : e * e = 0)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) {b b' c d d' c' k : A}
    (hb : b * b' = 1) (hd : d * d' = 1)
    (h : φ b + e * φ c = (1 + e * φ k) * (φ d + e * φ c')) : k = c * b' - c' * d' := by
  obtain ⟨h1, h2⟩ := uniq φ e H (a := b) (b := c) (a' := d) (b' := c' + k * d) (by
    simp only [map_mul, map_add]
    linear_combination h + (φ k * φ c') * he)
  subst h1
  have h3 : b' = d' := by linear_combination d' * hb - b' * hd + (0 : A)
  subst h3
  linear_combination (-b') * h2 - k * hb

theorem trivial_iff_coboundary : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (Q : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → ((∃ t : Q.Gen, t.IsGen) ↔ ∃ a : ∀ i, Γ(Y, j ⁻¹ᵁ Q.U i), ∀ i i', k i i' = resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i from fun _ hy => hy.1) (a i) - resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' from fun _ hy => hy.2) (a i')) := by
  intro Y Y' q π ρ j hp hj hq Q k _ hg
  obtain ⟨hO, -, hD⟩ := GlobalTheory.T.const_thickening_complex_functions_structure Y Y' q π ρ j hp hj hq
  have le : ∀ W : Y'.Opens, W ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ W) := fun W => (hO W).ge
  have H : ∀ (W : Y'.Opens) (F : Γ(Y', W)), ∃! ab : Γ(Y, j ⁻¹ᵁ W) × Γ(Y, j ⁻¹ᵁ W),
      F = (ρ.appLE _ W (le W)).hom ab.1 + constFn π _ DualNumber.eps * (ρ.appLE _ W (le W)).hom ab.2 :=
    fun W F => decomp π ρ _ (hD _) W (hO W) (le W) F
  constructor
  · rintro ⟨t, ht⟩
    choose b b' c hb hs using fun i =>
      unit_form (ρ.appLE _ (Q.U i) (le _)).hom _ (eps_sq π _) (H (Q.U i)) (t.s i)
    refine ⟨fun i => c i * b' i, fun i i' => ?_⟩
    have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have E : resG Y' inf_le_left (t.s i : Γ(Y', Q.U i)) =
        (Q.g i i').val * resG Y' inf_le_right (t.s i' : Γ(Y', Q.U i')) := congrArg Units.val (ht i i')
    rw [hg i i' (le _), hs, hs, map_add, map_add, map_mul, map_mul, res_constFn', res_constFn',
      res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _),
      res_appLE ρ _ l₂ _ (le _)] at E
    rw [map_mul, map_mul]
    exact overlap _ _ (eps_sq π _) (H _) (by rw [← map_mul, hb, map_one])
      (by rw [← map_mul, hb, map_one]) E
  · rintro ⟨a, ha⟩
    refine ⟨⟨fun i => ⟨1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i),
      1 - constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i), ?_, ?_⟩⟩, fun i i' => ?_⟩
    · linear_combination (-((ρ.appLE _ (Q.U i) (le _)).hom (a i)) ^ 2) * eps_sq π (Q.U i)
    · linear_combination (-((ρ.appLE _ (Q.U i) (le _)).hom (a i)) ^ 2) * eps_sq π (Q.U i)
    · have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
      have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
      apply Units.ext
      change resG Y' inf_le_left (1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i)) =
        (Q.g i i').val * resG Y' inf_le_right
          (1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i') (le _)).hom (a i'))
      rw [hg i i' (le _), map_add, map_add, map_mul, map_mul, map_one, map_one, res_constFn', res_constFn',
        res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _), ha i i', map_sub]
      linear_combination (-((ρ.appLE _ _ (le _)).hom (resG Y l₁ (a i)) -
        (ρ.appLE _ _ (le _)).hom (resG Y l₂ (a i'))) * (ρ.appLE _ _ (le _)).hom (resG Y l₂ (a i'))) *
        eps_sq π (Q.U i ⊓ Q.U i')

end GlobalTheory.KS.EpsBundle
end
