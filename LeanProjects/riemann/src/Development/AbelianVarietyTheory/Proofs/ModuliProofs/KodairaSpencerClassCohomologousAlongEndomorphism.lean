import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsAlongGroupHomStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivationsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}

theorem pbT_pbT (t : T ⟶ Z) (f : Z ⟶ Y) {O₀ : Y.Opens} {O₁ : Z.Opens} {O₂ : T.Opens} (h₁ : O₁ ≤ f ⁻¹ᵁ O₀)
    (h₂ : O₂ ≤ t ⁻¹ᵁ O₁) (s : Γ(Y, O₀)) : pbT t (pbT f s O₁) O₂ = pbT (t ≫ f) s O₂ := by
  have h₃ : O₂ ≤ (t ≫ f) ⁻¹ᵁ O₀ := h₂.trans (t.preimage_mono h₁)
  simp only [pbT, dif_pos h₁, dif_pos h₂, dif_pos h₃]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem app_eq (f : Z ⟶ Y) {O : Y.Opens} (s : Γ(Y, O)) : (f.app O).hom s = pbT f s (f ⁻¹ᵁ O) := by
  simp only [pbT, dif_pos (le_refl (f ⁻¹ᵁ O)), Scheme.Hom.appLE_eq_app]

theorem resG_eq {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : resG Y h s = rsT s O := by
  simp only [rsT, dif_pos h]

theorem pbT_ι_bijective (O : Y.Opens) {O' : Y.Opens} (h : O' ≤ O) {V : O.toScheme.Opens} (hV : V = O.ι ⁻¹ᵁ O') :
    Function.Bijective (fun s : Γ(Y, O') => pbT O.ι s V) := by
  subst hV
  have e : O.ι ''ᵁ (O.ι ⁻¹ᵁ O') = O' := by
    apply le_antisymm
    · exact Set.image_preimage_subset _ _
    · intro x hx
      exact ⟨⟨x, h hx⟩, hx, rfl⟩
  have key : (fun s : Γ(Y, O') => pbT O.ι s (O.ι ⁻¹ᵁ O')) = (O.ι.appLE O' _ le_rfl).hom := by
    funext s
    simp only [pbT, dif_pos (le_refl (O.ι ⁻¹ᵁ O'))]
  rw [key, Scheme.Opens.ι_appLE]
  rw [show homOfLE (x := O.ι ''ᵁ O.ι ⁻¹ᵁ O') (Set.image_subset_iff.mpr le_rfl) = eqToHom e from Subsingleton.elim _ _]
  rw [eqToHom_op, eqToHom_map]
  have hI : ∀ {A B : CommRingCat} (p : A = B), Function.Bijective (eqToHom p).hom := by
    intro A B p
    subst p
    simpa using Function.bijective_id
  exact hI _

theorem constFn_zero' {R : Type} [CommRing R] (q : Y ⟶ Sp R) (O : Y.Opens) : constFn q O 0 = 0 := by
  simp only [constFn, map_zero]

theorem pre_ι_eq (O : Y.Opens) (y : Y ⟶ Z) (m : Z ⟶ X) (W : X.Opens) :
    ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W = O.ι ⁻¹ᵁ (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) := by
  rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
  rfl

private lemma rsT_eq_pbT_id {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) :
    rsT s O = pbT (𝟙 Y) s O := by
  by_cases h : O ≤ O₀
  · have h' : O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := h
    simp only [rsT, pbT, dif_pos h, dif_pos h', Scheme.Hom.appLE, resG]
    rfl
  · have h' : ¬ O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := h
    simp only [rsT, pbT, dif_neg h, dif_neg h']

private lemma pbT_eq_appLE_hom {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ O₀)
    (s : Γ(Y, O₀)) : pbT f s V = (f.appLE O₀ V h).hom s := by
  simp only [pbT, dif_pos h]

private lemma rsT_sub_moduli' {Y : Scheme.{0}} {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (O : Y.Opens) :
    rsT (a - b) O = rsT a O - rsT b O := by
  by_cases h : O ≤ O₀
  · simp only [rsT, dif_pos h, map_sub]
  · simp only [rsT, dif_neg h, sub_zero]

private lemma pbT_zero_eq_zero {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (V : Z.Opens) :
    pbT f (0 : Γ(Y, O₀)) V = 0 := by
  by_cases h : V ≤ f ⁻¹ᵁ O₀
  · simp only [pbT, dif_pos h, map_zero]
  · simp only [pbT, dif_neg h]

private lemma rsT_zero_eq_zero {Y : Scheme.{0}} {O₀ : Y.Opens} (O : Y.Opens) :
    rsT (0 : Γ(Y, O₀)) O = 0 := by
  by_cases h : O ≤ O₀
  · simp only [rsT, dif_pos h, map_zero]
  · simp only [rsT, dif_neg h]

private lemma locDerK_zero' {Y X : Scheme.{0}} {K R : Type} [Field K] [CommRing R] (q : Y ⟶ Sp K)
    (p : X ⟶ Sp R) (m : Y ⟶ X) (W₀ : X.Opens) :
    LocDerK q p m (fun _ => 0) W₀ (fun _ _ => 0) :=
  ⟨fun _ _ _ _ => (add_zero 0).symm, fun _ _ _ _ => by simp, fun _ _ _ _ _ => (rsT_zero_eq_zero _).symm,
    fun _ _ _ => (constFn_zero' q _).symm⟩

variable {K : Type} [Field K] {R : Type} [CommRing R] {g : ℕ}

def IsBasis (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) : Prop :=
  ∀ (T : Scheme.{0}) (y : T ⟶ Y) (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(T, (y ≫ m) ⁻¹ᵁ W)),
    LocDerK (y ≫ q) p (y ≫ m) (fun _ => 0) W₀ d → ∃! c : Fin g → Γ(T, (y ≫ m) ⁻¹ᵁ W₀),
      ∀ W, W ≤ W₀ → ∀ f, d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _

theorem pbT_ι_comb {m : Y ⟶ X} (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (y : Z ⟶ Y) (O : Z.Opens)
    {W₀ W : X.Opens} (hO : O ≤ y ⁻¹ᵁ m ⁻¹ᵁ W₀) (hW : W ≤ W₀) (c : Fin g → Γ(Z, O)) (f : Γ(X, W)) :
    pbT O.ι (∑ a, rsT (c a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W))
      (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W) =
    ∑ a, rsT (pbT O.ι (c a) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀)) _ * pbT (O.ι ≫ y) (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
  have hL : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W ≤ O.ι ⁻¹ᵁ (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) := le_of_eq (pre_ι_eq O y m W)
  have hL₀ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W ≤ ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀ := Scheme.Hom.preimage_mono _ hW
  rw [pbT_eq_appLE_hom _ hL, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, ← pbT_eq_appLE_hom _ hL, ← pbT_eq_appLE_hom _ hL]
  congr 1
  · have h₁ : O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W ≤ (𝟙 Z) ⁻¹ᵁ O := inf_le_left
    have h₂ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀ ≤ O.ι ⁻¹ᵁ O := by
      rw [Scheme.Opens.ι_preimage_self]
      exact le_top
    have h₃ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W ≤ (𝟙 O.toScheme) ⁻¹ᵁ (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀) := hL₀
    rw [rsT_eq_pbT_id, rsT_eq_pbT_id, pbT_pbT O.ι (𝟙 Z) h₁ hL, pbT_pbT (𝟙 O.toScheme) O.ι h₂ h₃]
    simp only [Category.comp_id, Category.id_comp]
  · exact pbT_pbT _ _ inf_le_right hL _

theorem comb_unique {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hb : IsBasis q p m dd) (y : Z ⟶ Y) (O : Z.Opens) (W₀ : X.Opens) (hO : O ≤ y ⁻¹ᵁ m ⁻¹ᵁ W₀)
    (c c' : Fin g → Γ(Z, O))
    (h : ∀ W, W ≤ W₀ → ∀ f : Γ(X, W),
      ∑ a, rsT (c a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) =
      ∑ a, rsT (c' a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W)) :
    c = c' := by
  have hV₀ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀ = O.ι ⁻¹ᵁ O := by rw [pre_ι_eq, inf_eq_left.mpr hO]
  have hz : ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), (fun _ _ => 0 : ∀ W : X.Opens, Γ(X, W) → Γ(O.toScheme, ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W)) W f =
      ∑ a, rsT ((fun a => pbT O.ι (c a - c' a) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀)) a) _ *
        pbT (O.ι ≫ y) (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro W hW f
    have e := pbT_ι_comb dd y O hO hW (fun a => c a - c' a) f
    beta_reduce at e ⊢
    rw [← e]
    simp only [rsT_sub_moduli', sub_mul, Finset.sum_sub_distrib, h W hW f, sub_self, pbT_zero_eq_zero]
  have hz' : ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), (fun _ _ => 0 : ∀ W : X.Opens, Γ(X, W) → Γ(O.toScheme, ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W)) W f =
      ∑ a, rsT ((0 : Fin g → Γ(O.toScheme, ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀)) a) _ *
        pbT (O.ι ≫ y) (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro W hW f
    simp only [Pi.zero_apply, rsT_zero_eq_zero, zero_mul, Finset.sum_const_zero]
  obtain ⟨c₀, -, hu⟩ := hb O.toScheme (O.ι ≫ y) W₀ _ (locDerK_zero' _ p _ W₀)
  have e₁ := hu _ hz
  have e₂ := hu _ hz'
  funext a
  have ha : pbT O.ι (c a - c' a) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀) = pbT O.ι (0 : Γ(Z, O)) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀) := by
    rw [pbT_zero_eq_zero]
    exact congrFun (e₁.trans e₂.symm) a
  exact sub_eq_zero.mp ((pbT_ι_bijective O (le_refl O) hV₀).1 ha)

theorem comb_exists {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hb : IsBasis q p m dd) (y : Z ⟶ Y) (O : Z.Opens) (W₀ : X.Opens) (hO : O ≤ y ⁻¹ᵁ m ⁻¹ᵁ W₀)
    (ν : ∀ W : X.Opens, Γ(X, W) → Γ(Z, O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W))
    (hν : LocDerK ((O.ι ≫ y) ≫ q) p ((O.ι ≫ y) ≫ m) (fun _ => 0) W₀ (fun W f => pbT O.ι (ν W f) _)) :
    ∃ c : Fin g → Γ(Z, O), ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ν W f =
      ∑ a, rsT (c a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) := by
  have hV₀ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀ = O.ι ⁻¹ᵁ O := by rw [pre_ι_eq, inf_eq_left.mpr hO]
  obtain ⟨c₀, hc₀, -⟩ := hb O.toScheme (O.ι ≫ y) W₀ _ hν
  choose c hc using fun a => (pbT_ι_bijective O (le_refl O) hV₀).2 (c₀ a)
  have hc' : ∀ a, pbT O.ι (c a) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀) = c₀ a := hc
  refine ⟨c, fun W hW f => ?_⟩
  apply (pbT_ι_bijective O (inf_le_left : O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W ≤ O) (pre_ι_eq O y m W)).1
  have e := hc₀ W hW f
  beta_reduce at e ⊢
  rw [e, pbT_ι_comb dd y O hO hW c f]
  simp only [hc']

private lemma pbT_add_of_open {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (V : Z.Opens) :
    pbT f (a + b) V = pbT f a V + pbT f b V := by
  by_cases h : V ≤ f ⁻¹ᵁ O₀
  · simp only [pbT, dif_pos h, map_add]
  · simp only [pbT, dif_neg h, add_zero]

private lemma pbT_mul_of_le_preimage {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) {V : Z.Opens}
    (h : V ≤ f ⁻¹ᵁ O₀) : pbT f (a * b) V = pbT f a V * pbT f b V := by
  simp only [pbT, dif_pos h, map_mul]

private lemma pbT_congr {Y Z : Scheme.{0}} {f f' : Z ⟶ Y} (e : f = f') {O₀ : Y.Opens} (s : Γ(Y, O₀))
    (V : Z.Opens) : pbT f s V = pbT f' s V := by
  subst e
  rfl

private lemma pbT_rsT_eq_rsT_pbT {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ O : Y.Opens} {V₀ V : Z.Opens} (s : Γ(Y, O₀))
    (hO : O ≤ O₀) (hV : V ≤ f ⁻¹ᵁ O) (hV₀ : V₀ ≤ f ⁻¹ᵁ O₀) (hVV : V ≤ V₀) :
    pbT f (rsT s O) V = rsT (pbT f s V₀) V := by
  have hO' : O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := hO
  have hVV' : V ≤ (𝟙 Z) ⁻¹ᵁ V₀ := hVV
  rw [rsT_eq_pbT_id, rsT_eq_pbT_id, pbT_pbT f (𝟙 Y) hO' hV, pbT_pbT (𝟙 Z) f hV₀ hVV']
  simp only [Category.comp_id, Category.id_comp]

private lemma pbT_constFn_of_le_preimage {Y Z : Scheme.{0}} {R : Type} [CommRing R] (f : Z ⟶ Y) (q : Y ⟶ Sp R)
    {O : Y.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ O) (r : R) : pbT f (constFn q O r) V = constFn (f ≫ q) V r := by
  rw [pbT_eq_appLE_hom f h]
  exact congrArg (fun φ : Γ(Sp R, ⊤) ⟶ Γ(Z, V) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ O V (by exact le_top) h)

theorem locDer_diff {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₁ W₂ : X.Opens}
    {d₁ d₂ : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h₁ : LocDerK q p m D W₁ d₁) (h₂ : LocDerK q p m D W₂ d₂)
    (f : X ⟶ X) (f₀ : Y ⟶ Y) (hp : f ≫ p = p) (hq : f₀ ≫ q = q) (hm : f₀ ≫ m = m ≫ f)
    (t : T ⟶ Y) (ht : ⊤ ≤ t ⁻¹ᵁ m ⁻¹ᵁ W₁) :
    LocDerK ((t ≫ f₀) ≫ q) p ((t ≫ f₀) ≫ m) (fun _ => 0) W₂ (fun W h =>
      pbT t (d₁ (W₁ ⊓ f ⁻¹ᵁ W) (pbT f h _)) _ - pbT (t ≫ f₀) (d₂ W h) _) := by
  have ht' : t ⁻¹ᵁ m ⁻¹ᵁ W₁ = ⊤ := top_le_iff.mp ht
  have hM : ∀ W, ((t ≫ f₀) ≫ m) ⁻¹ᵁ W = t ⁻¹ᵁ m ⁻¹ᵁ (W₁ ⊓ f ⁻¹ᵁ W) := by
    intro W
    rw [Category.assoc, hm, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, ht', top_inf_eq]
    rfl
  have hL : ∀ W, ((t ≫ f₀) ≫ m) ⁻¹ᵁ W ≤ t ⁻¹ᵁ m ⁻¹ᵁ (W₁ ⊓ f ⁻¹ᵁ W) := fun W => le_of_eq (hM W)
  have hL' : ∀ W, ((t ≫ f₀) ≫ m) ⁻¹ᵁ W ≤ (t ≫ f₀) ⁻¹ᵁ m ⁻¹ᵁ W := fun W => le_rfl
  have hA : ∀ W (h : Γ(X, W)), pbT t ((m.app (W₁ ⊓ f ⁻¹ᵁ W)).hom (pbT f h (W₁ ⊓ f ⁻¹ᵁ W))) (((t ≫ f₀) ≫ m) ⁻¹ᵁ W) =
      (((t ≫ f₀) ≫ m).app W).hom h := by
    intro W h
    have e₁ : W₁ ⊓ f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W := inf_le_right
    have e₂ : m ⁻¹ᵁ (W₁ ⊓ f ⁻¹ᵁ W) ≤ (m ≫ f) ⁻¹ᵁ W := m.preimage_mono inf_le_right
    rw [app_eq, app_eq, pbT_pbT m f e₁ le_rfl, pbT_pbT t (m ≫ f) e₂ (hL W)]
    exact pbT_congr (by rw [Category.assoc, hm]) _ _
  have hB : ∀ W (h : Γ(X, W)), pbT (t ≫ f₀) ((m.app W).hom h) (((t ≫ f₀) ≫ m) ⁻¹ᵁ W) =
      (((t ≫ f₀) ≫ m).app W).hom h := by
    intro W h
    rw [app_eq, app_eq, pbT_pbT (t ≫ f₀) m le_rfl (hL' W)]
  refine ⟨fun W hW h h' => ?_, fun W hW h h' => ?_, fun W W' hh hW h => ?_, fun W hW r => ?_⟩
  · rw [pbT_add_of_open, h₁.add (W₁ ⊓ f ⁻¹ᵁ W) inf_le_left, pbT_add_of_open, h₂.add W hW, pbT_add_of_open]
    abel
  · rw [pbT_mul_of_le_preimage f h h' (inf_le_right : W₁ ⊓ f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W), h₁.mul (W₁ ⊓ f ⁻¹ᵁ W) inf_le_left,
      h₂.mul W hW, pbT_add_of_open, pbT_add_of_open, pbT_mul_of_le_preimage _ _ _ (hL W), pbT_mul_of_le_preimage _ _ _ (hL W),
      pbT_mul_of_le_preimage _ _ _ (hL' W), pbT_mul_of_le_preimage _ _ _ (hL' W), hA, hA, hB, hB]
    ring
  · have hV : W₁ ⊓ f ⁻¹ᵁ W' ≤ W₁ ⊓ f ⁻¹ᵁ W := inf_le_inf_left _ (f.preimage_mono hh)
    rw [h₂.res W W' hh hW, resG_eq, pbT_rsT_eq_rsT_pbT f h hh inf_le_right inf_le_right hV, ← resG_eq hV,
      h₁.res _ _ hV inf_le_left,
      pbT_rsT_eq_rsT_pbT t _ (m.preimage_mono hV) (hL W') (hL W) ((t ≫ f₀ ≫ m).preimage_mono hh),
      pbT_rsT_eq_rsT_pbT (t ≫ f₀) _ (m.preimage_mono hh) (hL' W') (hL' W) (((t ≫ f₀) ≫ m).preimage_mono hh),
      rsT_sub_moduli']
  · rw [pbT_constFn_of_le_preimage f p (inf_le_right : W₁ ⊓ f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W), hp, h₁.base _ inf_le_left,
      h₂.base W hW, pbT_constFn_of_le_preimage t q (hL W), pbT_constFn_of_le_preimage (t ≫ f₀) q (hL' W), Category.assoc t f₀ q, hq,
      sub_self, constFn_zero']

private lemma pbT_sub' {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (a b : Γ(Y, O₀)) (V : Z.Opens) :
    pbT f (a - b) V = pbT f a V - pbT f b V := by
  by_cases h : V ≤ f ⁻¹ᵁ O₀
  · simp only [pbT, dif_pos h, map_sub]
  · simp only [pbT, dif_neg h, sub_zero]

private lemma pbT_rsT_of_le_of_le_preimage {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ O : Y.Opens} {L : Z.Opens} (s : Γ(Y, O₀))
    (hV : L ≤ f ⁻¹ᵁ O) (hO : O ≤ O₀) : pbT f (rsT s O) L = pbT f s L := by
  have hO' : O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := hO
  rw [rsT_eq_pbT_id, pbT_pbT f (𝟙 Y) hO' hV, Category.comp_id]

private lemma rsT_rsT_of_le {Y : Scheme.{0}} {O₀ O O' : Y.Opens} (s : Γ(Y, O₀)) (h₁ : O ≤ O₀) (h₂ : O' ≤ O) :
    rsT (rsT s O) O' = rsT s O' := by
  have h₁' : O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := h₁
  have h₂' : O' ≤ (𝟙 Y) ⁻¹ᵁ O := h₂
  rw [rsT_eq_pbT_id, rsT_eq_pbT_id, rsT_eq_pbT_id, pbT_pbT (𝟙 Y) (𝟙 Y) h₁' h₂', Category.comp_id]

private lemma rsT_pbT_of_le_preimage {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {V₀ V : Z.Opens} (s : Γ(Y, O₀))
    (hV₀ : V₀ ≤ f ⁻¹ᵁ O₀) (hV : V ≤ V₀) : rsT (pbT f s V₀) V = pbT f s V := by
  have hV' : V ≤ (𝟙 Z) ⁻¹ᵁ V₀ := hV
  rw [rsT_eq_pbT_id, pbT_pbT (𝟙 Z) f hV₀ hV', Category.id_comp]

private lemma rsT_constFn_of_le {Y : Scheme.{0}} {R : Type} [CommRing R] (q : Y ⟶ Sp R) {O O' : Y.Opens}
    (h : O' ≤ O) (r : R) : rsT (constFn q O r) O' = constFn q O' r := by
  have h' : O' ≤ (𝟙 Y) ⁻¹ᵁ O := h
  rw [rsT_eq_pbT_id, pbT_constFn_of_le_preimage (𝟙 Y) q h', Category.id_comp]

private lemma rsT_sum_mul {Y : Scheme.{0}} {n : ℕ} {O O' : Y.Opens} (h : O' ≤ O) (u v : Fin n → Γ(Y, O)) :
    rsT (∑ a, u a * v a) O' = ∑ a, rsT (u a) O' * rsT (v a) O' := by
  rw [← resG_eq h, map_sum]
  simp only [map_mul]
  simp only [resG_eq h]

private lemma pbT_sum_mul {Y Z : Scheme.{0}} {n : ℕ} (f : Z ⟶ Y) {O : Y.Opens} {V : Z.Opens}
    (h : V ≤ f ⁻¹ᵁ O) (u v : Fin n → Γ(Y, O)) :
    pbT f (∑ a, u a * v a) V = ∑ a, pbT f (u a) V * pbT f (v a) V := by
  rw [pbT_eq_appLE_hom f h, map_sum]
  simp only [map_mul]
  simp only [← pbT_eq_appLE_hom f h]

private lemma rsT_sum_rsT_mul_pbT_inf {Y₁ Y₂ : Scheme.{0}} {n : ℕ} (y : Y₁ ⟶ Y₂) {O Q V : Y₁.Opens} {A : Y₂.Opens}
    (hQ : Q ≤ O) (hV : V ≤ y ⁻¹ᵁ A) (c : Fin n → Γ(Y₁, O)) (e : Fin n → Γ(Y₂, A)) :
    rsT (∑ a, rsT (c a) (O ⊓ V) * pbT y (e a) (O ⊓ V)) (Q ⊓ V) = ∑ a, rsT (c a) (Q ⊓ V) * pbT y (e a) (Q ⊓ V) := by
  rw [rsT_sum_mul (inf_le_inf_right V hQ)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [rsT_rsT_of_le _ inf_le_left (inf_le_inf_right V hQ), rsT_pbT_of_le_preimage y _ (inf_le_right.trans hV) (inf_le_inf_right V hQ)]

private lemma sum_mul_sum_eq_sum_sum_mul_mul {A : Type} [CommRing A] {n : ℕ} (t : Fin n → A) (C : Fin n → Fin n → A) (P : Fin n → A) :
    ∑ a, t a * ∑ b, C b a * P b = ∑ b, (∑ a, C b a * t a) * P b := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem cohom_of_basis {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hb : IsBasis q p m dd) {I : Type} {W : I → X.Opens} {D : R → K}
    {d : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} {θ : Fin g → C1 (fun i => m ⁻¹ᵁ W i)}
    (hc : KSCoc q p m D W dd d θ)
    (f : X ⟶ X) (f₀ : Y ⟶ Y) (hp : f ≫ p = p) (hq : f₀ ≫ q = q) (hm : f₀ ≫ m = m ≫ f) (F : Matrix (Fin g) (Fin g) K)
    (hres : ∀ a O O' (s : Γ(Y, O)), O' ≤ O → dd a O' (rsT s O') = rsT (dd a O s) O')
    (hend : ∀ j (O : Y.Opens) (s : Γ(Y, O)), dd j (f₀ ⁻¹ᵁ O) ((f₀.app O).hom s) =
      ∑ a, constFn q _ (F a j) * (f₀.app O).hom (dd a O s)) (x : Fin g) :
    Cohom f₀ _ (lc q (F x) θ) (θ x) := by
  have hmW : ∀ W' : X.Opens, f₀ ⁻¹ᵁ m ⁻¹ᵁ W' = m ⁻¹ᵁ f ⁻¹ᵁ W' := fun W' => by
    rw [← Scheme.Hom.comp_preimage, hm]
    rfl
  have hVi : ∀ i k W', m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ (W i ⊓ f ⁻¹ᵁ W') := by
    intro i k W'
    rw [Scheme.Hom.preimage_inf, ← hmW]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hex : ∀ i k, ∃ c : Fin g → Γ(Y, m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k), ∀ W', W' ≤ W k → ∀ h : Γ(X, W'),
      rsT (d i (W i ⊓ f ⁻¹ᵁ W') (pbT f h (W i ⊓ f ⁻¹ᵁ W'))) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') -
        pbT f₀ (d k W' h) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
      ∑ a, rsT (c a) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') *
        pbT f₀ (dd a (m ⁻¹ᵁ W') ((m.app W').hom h)) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
    intro i k
    have ht : ⊤ ≤ (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k).ι ⁻¹ᵁ m ⁻¹ᵁ W i := by
      rw [← Scheme.Opens.ι_preimage_self (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k)]
      exact Scheme.Hom.preimage_mono _ inf_le_left
    have hD := locDer_diff (hc.der i) (hc.der k) f f₀ hp hq hm _ ht
    refine comb_exists hb f₀ _ (W k) inf_le_right
      (fun W' h => rsT (d i (W i ⊓ f ⁻¹ᵁ W') (pbT f h (W i ⊓ f ⁻¹ᵁ W'))) _ - pbT f₀ (d k W' h) _) ?_
    convert hD using 1
    funext W' h
    have hL := le_of_eq (pre_ι_eq (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k) f₀ m W')
    rw [pbT_sub', pbT_rsT_of_le_of_le_preimage _ _ hL (hVi i k W'), pbT_pbT _ f₀ inf_le_right hL]
  choose c hc' using hex
  have hE : ∀ i k (Q : Y.Opens), Q ≤ m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k → ∀ W', W' ≤ W k → ∀ h : Γ(X, W'),
      ∑ a, rsT (c i k a) (Q ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') * pbT f₀ (dd a (m ⁻¹ᵁ W') ((m.app W').hom h)) (Q ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
      rsT (d i (W i ⊓ f ⁻¹ᵁ W') (pbT f h (W i ⊓ f ⁻¹ᵁ W'))) (Q ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') -
        pbT f₀ (d k W' h) (Q ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
    intro i k Q hQ W' hW' h
    have e := rsT_sum_rsT_mul_pbT_inf f₀ hQ (le_refl (f₀ ⁻¹ᵁ m ⁻¹ᵁ W')) (c i k) (fun a => dd a (m ⁻¹ᵁ W') ((m.app W').hom h))
    rw [← hc' i k W' hW' h] at e
    rw [← e, rsT_sub_moduli', rsT_rsT_of_le _ (hVi i k W') (inf_le_inf_right _ hQ),
      rsT_pbT_of_le_preimage f₀ _ inf_le_right (inf_le_inf_right _ hQ)]
  refine ⟨fun i k => c i k x, fun i i' k => ?_, fun i k k' => ?_⟩
  · have hQ : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k := inf_le_right
    have hQi : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ≤ m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hQi' : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ≤ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have key := comb_unique hb f₀ _ (W k) hQ
      (fun a => rsT (c i' k a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k) -
        rsT (c i k a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k))
      (fun a => rsT (lc q (F a) θ i i') (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k)) ?_
    · exact congrFun key x
    intro W' hW' h
    have hQ' : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k :=
      inf_le_left
    have hQc : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W') := by
      rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, ← hmW]
      exact le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans (inf_le_left.trans inf_le_right))) inf_le_right
    have hQf : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' := inf_le_right
    have hOcf : m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W') ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' := by
      rw [hmW]
      exact Scheme.Hom.preimage_mono _ inf_le_right
    have hOθ : m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W') ≤ m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' := Scheme.Hom.preimage_mono _ inf_le_left
    have EA : ∀ j, W i ⊓ W i' ⊓ f ⁻¹ᵁ W' ≤ W j ⊓ f ⁻¹ᵁ W' →
        rsT (d j (W j ⊓ f ⁻¹ᵁ W') (pbT f h (W j ⊓ f ⁻¹ᵁ W'))) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
        rsT (d j (W i ⊓ W i' ⊓ f ⁻¹ᵁ W') (pbT f h (W i ⊓ W i' ⊓ f ⁻¹ᵁ W'))) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
      intro j hj
      rw [← rsT_rsT_of_le _ (Scheme.Hom.preimage_mono _ hj) hQc, ← (hc.der j).res _ _ hj inf_le_left, resG_eq,
        rsT_pbT_of_le_preimage f h inf_le_right hj]
    have Eu : (m.app (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')).hom (pbT f h (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')) =
        rsT ((f₀.app (m ⁻¹ᵁ W')).hom ((m.app W').hom h)) (m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')) := by
      rw [app_eq m (pbT f h _), app_eq m h, app_eq f₀, pbT_pbT f₀ m le_rfl le_rfl,
        rsT_pbT_of_le_preimage (f₀ ≫ m) h (le_rfl : f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ (f₀ ≫ m) ⁻¹ᵁ W') hOcf,
        pbT_pbT m f inf_le_right le_rfl]
      exact pbT_congr hm.symm _ _
    have Edd : ∀ a, rsT (dd a (m ⁻¹ᵁ (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')) ((m.app (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')).hom
        (pbT f h (W i ⊓ W i' ⊓ f ⁻¹ᵁ W')))) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
        ∑ b, constFn q (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') (F b a) *
          pbT f₀ (dd b (m ⁻¹ᵁ W') ((m.app W').hom h)) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
      intro a
      rw [Eu, hres a _ _ _ hOcf, rsT_rsT_of_le _ hOcf hQc, hend a (m ⁻¹ᵁ W') ((m.app W').hom h), rsT_sum_mul hQf]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [rsT_constFn_of_le _ hQf, app_eq f₀, rsT_pbT_of_le_preimage f₀ _ le_rfl hQf]
    simp only [rsT_sub_moduli', rsT_rsT_of_le _ hQi hQ', rsT_rsT_of_le _ hQi' hQ', sub_mul, Finset.sum_sub_distrib]
    rw [hE i' k _ hQi' W' hW' h, hE i k _ hQi W' hW' h, sub_sub_sub_cancel_right,
      EA i (le_inf (inf_le_left.trans inf_le_left) inf_le_right), EA i' (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      ← rsT_sub_moduli', hc.diff i i' _ inf_le_left, rsT_sum_mul hQc]
    have Elc : ∀ b, rsT (rsT (lc q (F b) θ i i') (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k)) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') =
        ∑ a, constFn q (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') (F b a) * rsT (θ a i i') (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') := by
      intro b
      rw [rsT_rsT_of_le _ inf_le_left hQ']
      exact (rsT_sum_mul (hQ'.trans inf_le_left) (fun a => constFn q _ (F b a)) (fun a => θ a i i')).trans
        (Finset.sum_congr rfl (fun a _ => by rw [rsT_constFn_of_le _ (hQ'.trans inf_le_left)]))
    refine (Finset.sum_congr rfl (fun a _ => ?_)).trans ((sum_mul_sum_eq_sum_sum_mul_mul (fun a => rsT (θ a i i') (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W'))
      (fun b a => constFn q (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W') (F b a))
      (fun b => pbT f₀ (dd b (m ⁻¹ᵁ W') ((m.app W').hom h)) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W i' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W'))).trans
      (Finset.sum_congr rfl (fun b _ => ?_)))
    · rw [rsT_rsT_of_le _ hOθ hQc, Edd a]
    · rw [Elc b]
  · have hR : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ (W k ⊓ W k') := by
      rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hRk : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ≤ m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k := inf_le_left
    have hRk' : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ≤ m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hRθ : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ≤ f₀ ⁻¹ᵁ (m ⁻¹ᵁ W k ⊓ m ⁻¹ᵁ W k') := by
      rw [Scheme.Hom.preimage_inf]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have key := comb_unique hb f₀ _ (W k ⊓ W k') hR
      (fun a => rsT (c i k a) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k') -
        rsT (c i k' a) (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k'))
      (fun a => pbT f₀ (θ a k k') (m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k')) ?_
    · exact congrFun key x
    intro W' hW' h
    have hR' : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤
        m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' := inf_le_left
    have hRf : m ⁻¹ᵁ W i ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W k' ⊓ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' ≤ f₀ ⁻¹ᵁ m ⁻¹ᵁ W' := inf_le_right
    have hWθ : m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W k ⊓ m ⁻¹ᵁ W k' := Scheme.Hom.preimage_mono _ hW'
    simp only [rsT_sub_moduli', rsT_rsT_of_le _ hRk hR', rsT_rsT_of_le _ hRk' hR', sub_mul, Finset.sum_sub_distrib]
    rw [hE i k _ hRk W' (hW'.trans inf_le_left) h, hE i k' _ hRk' W' (hW'.trans inf_le_right) h,
      sub_sub_sub_cancel_left, ← pbT_sub', hc.diff k k' W' hW', pbT_sum_mul f₀ hRf]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [pbT_rsT_of_le_of_le_preimage _ _ hRf hWθ, rsT_pbT_of_le_preimage f₀ _ hRθ hR']

end GlobalTheory.KS.EndClass

open GlobalTheory.KS.EndClass in

theorem GlobalTheory.KS.cohom_ksCoc_of_endomorphism : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ (f : X ⟶ X) (f₀ : A₀ ⟶ A₀) (F : Matrix (Fin g) (Fin g) K), KSCoc A₀.hom p m D W dd d θ → IsMonHom f₀ → f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → ∀ x, Cohom f₀.left _ (lc A₀.hom (F x) θ) (θ x) := by
  intro K _ A₀ _ g v dd hs hv hdd R _ x₀ X p m hpb I W D d θ f f₀ F hc hf₀ hp hm hF x
  have hT : ∀ a, IsTangent (v a) := by
    unfold IsLieBasis at hv
    exact hv.1
  have hb : IsBasis A₀.hom p m dd := GlobalTheory.T.invariantVectorFields_basis_verticalDerivations K A₀ g v dd hs hv hdd R x₀ X p m hpb
  have hres : ∀ a O O' (s : Γ(A₀.left, O)), O' ≤ O → dd a O' (rsT s O') = rsT (dd a O s) O' :=
    fun a O O' s h => ((GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₀ (v a) (hT a)).2 (dd a) (hdd a)).2.2.1 O O' s h
  have hend : ∀ j (O : A₀.left.Opens) (s : Γ(A₀.left, O)), dd j (f₀.left ⁻¹ᵁ O) ((f₀.left.app O).hom s) =
      ∑ a, constFn A₀.hom _ (F a j) * (f₀.left.app O).hom (dd a O s) :=
    fun j O s => GlobalTheory.T.invariantVectorFields_along_groupHom K A₀ A₀ f₀ g v dd (v j) (dd j) (fun i => F i j) hf₀ hT (hT j) hdd (hdd j) (hF j) O s
  exact cohom_of_basis hb hc f f₀.left hp (Over.w f₀) hm F hres hend x
