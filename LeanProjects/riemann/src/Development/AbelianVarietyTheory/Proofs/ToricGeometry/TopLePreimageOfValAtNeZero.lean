import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

variable {X Y : Scheme.{0}}

theorem top_le_preimage_iff_mem (x : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U := by
  constructor
  · intro h
    exact h (Set.mem_univ (default : PrimeSpectrum ℂ))
  · intro h p _
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst this
    exact h

theorem top_le_preimage_mono (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ U :=
  fun _ hp => h (hV hp)

theorem top_le_preimage_inf (x : Sp ℂ ⟶ X) (U V : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) ↔ ⊤ ≤ x ⁻¹ᵁ U ∧ ⊤ ≤ x ⁻¹ᵁ V := by
  simp only [top_le_preimage_iff_mem]
  exact Iff.rfl

theorem top_le_preimage_comp (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) :
    ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
  rw [Scheme.Hom.comp_preimage]

def valAtHom (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem valAtHom_apply (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAtHom x U h f = valAt x U h f := rfl

theorem valAt'_eq_valAt (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valAt x U h f := by
  rw [valAt', dif_pos h]

theorem valAt'_eq_valAtHom (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valAtHom x U h f := valAt'_eq_valAt x h f

theorem valAt'_of_not_le (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ¬ ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = 0 := by
  rw [valAt', dif_neg h]

theorem top_le_preimage_of_valAt'_ne_zero (x : Sp ℂ ⟶ X) {U : X.Opens} {f : Γ(X, U)} (h : valAt' x U f ≠ 0) :
    ⊤ ≤ x ⁻¹ᵁ U := by
  by_contra hU
  exact h (valAt'_of_not_le x hU f)

theorem valAt'_ringHom (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f :=
  ⟨valAtHom x U h, valAt'_eq_valAtHom x h⟩

theorem valAt'_mul (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f * g) = valAt' x U f * valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_mul]
  · simp only [valAt'_of_not_le x h, mul_zero]

theorem valAt'_add (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f + g) = valAt' x U f + valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_add]
  · simp only [valAt'_of_not_le x h, add_zero]

theorem valAt'_zero (x : Sp ℂ ⟶ X) (U : X.Opens) : valAt' x U 0 = 0 := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_zero]
  · simp only [valAt'_of_not_le x h]

theorem valAt'_neg (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valAt' x U (-f) = - valAt' x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_neg]
  · simp only [valAt'_of_not_le x h, neg_zero]

theorem valAt'_sub (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f - g) = valAt' x U f - valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_sub]
  · simp only [valAt'_of_not_le x h, sub_zero]

theorem valAt'_sum {κ : Type*} (x : Sp ℂ ⟶ X) (U : X.Opens) (s : Finset κ) (f : κ → Γ(X, U)) :
    valAt' x U (∑ i ∈ s, f i) = ∑ i ∈ s, valAt' x U (f i) := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_sum]
  · simp only [valAt'_of_not_le x h, Finset.sum_const_zero]

theorem valAt'_one (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U 1 = 1 := by
  simp only [valAt'_eq_valAtHom x h, map_one]

theorem valAt'_prod {κ : Type*} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Finset κ) (f : κ → Γ(X, U)) :
    valAt' x U (∏ i ∈ s, f i) = ∏ i ∈ s, valAt' x U (f i) := by
  simp only [valAt'_eq_valAtHom x h, map_prod]

theorem valAt'_pow (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (n : ℕ) :
    valAt' x U (f ^ n) = valAt' x U f ^ n := by
  simp only [valAt'_eq_valAtHom x h, map_pow]

theorem valAt'_isUnit_ne_zero (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {f : Γ(X, U)} (hf : IsUnit f) :
    valAt' x U f ≠ 0 := by
  rw [valAt'_eq_valAtHom x h]
  exact (hf.map _).ne_zero

theorem valAt'_unit_ne_zero (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valAt' x U u.val ≠ 0 :=
  valAt'_isUnit_ne_zero x h u.isUnit

theorem valAt'_units_zpow (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valAt' x U (u ^ n).val = valAt' x U u.val ^ n := by
  simp only [valAt'_eq_valAtHom x h]
  have := congrArg Units.val (map_zpow (Units.map (valAtHom x U h : Γ(X, U) →* ℂ)) u n)
  rw [Units.val_zpow_eq_zpow_val] at this
  exact this

theorem valAt'_zpow (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valAt' x U (u ^ n).val = valAt' x U u.val ^ n :=
  valAt'_units_zpow x h u n

theorem valAt'_units_inv (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valAt' x U (u⁻¹).val = (valAt' x U u.val)⁻¹ := by
  simpa using valAt'_units_zpow x h u (-1)

theorem valAt'_units_prod {κ : Type*} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Finset κ)
    (u : κ → Γ(X, U)ˣ) : valAt' x U (∏ i ∈ s, u i).val = ∏ i ∈ s, valAt' x U (u i).val := by
  rw [Units.coe_prod, valAt'_prod x h]

theorem valAt'_appLE (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U))
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f := by
  have hU : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := (top_le_preimage_comp x φ U).2 (top_le_preimage_mono x e hV)
  rw [valAt'_eq_valAt x hV, valAt'_eq_valAt _ hU, valAt, valAt, ← CommRingCat.comp_apply (φ.appLE U V e),
    Scheme.Hom.appLE_comp_appLE]

theorem valAt'_map (x : Sp ℂ ⟶ X) {U V : X.Opens} (i : Opposite.op U ⟶ Opposite.op V) (f : Γ(X, U))
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((X.presheaf.map i).hom f) = valAt' x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := top_le_preimage_mono x i.unop.le hV
  rw [valAt'_eq_valAt x hV, valAt'_eq_valAt _ hU, valAt, valAt, ← CommRingCat.comp_apply (X.presheaf.map i),
    Scheme.Hom.map_appLE]

theorem valAt'_res (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    valAt' x V (resG X h f) = valAt' x U f :=
  valAt'_map x (homOfLE h).op f hV

theorem valAt'_comp (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [Scheme.Hom.app_eq_appLE]
    exact valAt'_appLE x φ U _ _ f h
  · rw [valAt'_of_not_le x h, valAt'_of_not_le _ (fun h' => h ((top_le_preimage_comp x φ U).1 h'))]

theorem top_le_preimage_basicOpen_iff (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0 := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · have h1 : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f := by
      have := Scheme.basicOpen_appLE x ⊤ U h f
      rw [top_inf_eq] at this
      exact this
    rw [← h1, valAt'_eq_valAt x h, valAt, top_le_iff]
    generalize (x.appLE U ⊤ h).hom f = g
    rw [← isUnit_iff_ne_zero]
    constructor
    · intro hg
      have : IsUnit g := (Sp ℂ).toRingedSpace.isUnit_of_isUnit_germ ⊤ g fun p hp =>
        ((Sp ℂ).mem_basicOpen g p hp).1 (by rw [hg]; exact hp)
      exact this.map _
    · intro hg
      have : IsUnit g := by
        have h2 := hg.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        simpa using h2
      exact (Sp ℂ).basicOpen_of_isUnit this
  · refine ⟨fun h' => (h (top_le_preimage_mono x (X.basicOpen_le f) h')).elim, fun h' => ?_⟩
    exact (h' (valAt'_of_not_le x h f)).elim

theorem valAt'_id_top (a : ℂ) :
    valAt' (𝟙 (Sp ℂ)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = a := by
  rw [valAt'_eq_valAt (𝟙 (Sp ℂ)) (U := ⊤) le_top]
  unfold valAt
  simp [Scheme.Hom.appLE]

theorem valAt'_constFn (x : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : x ≫ p = 𝟙 _) (U : X.Opens) (a : ℂ)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U (constFn p U a) = a := by
  refine (valAt'_appLE x p ⊤ U le_top _ h).trans ?_
  rw [hp, valAt'_id_top]

theorem valAt'_rules : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) :=
  fun _ x => ⟨top_le_preimage_iff_mem x, fun _ h => valAt'_ringHom x h, fun _ _ h f hV => valAt'_res x h f hV,
    fun _ φ U f => valAt'_comp x φ U f, top_le_preimage_basicOpen_iff x, fun p hp U a h => valAt'_constFn x p hp U a h⟩

end GlobalTheory
