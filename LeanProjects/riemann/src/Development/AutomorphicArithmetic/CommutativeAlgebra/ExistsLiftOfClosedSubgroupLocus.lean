import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SubRepPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSchemeGrpObjOfMonoFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace UpperTheory.ProductProjectionSubgroup

variable {S : Scheme.{0}}

private noncomputable def pr1 (Y G : Over S) : (Y ⊗ G).left ⟶ Y.left := pullback.fst Y.hom G.hom

private noncomputable def pr2 (Y G : Over S) : (Y ⊗ G).left ⟶ G.left := pullback.snd Y.hom G.hom

private theorem pr_cond (Y G : Over S) : pr1 Y G ≫ Y.hom = pr2 Y G ≫ G.hom := pullback.condition

private theorem pr_ext {Y G : Over S} {Z : Scheme.{0}} {f f' : Z ⟶ (Y ⊗ G).left}
    (h₁ : f ≫ pr1 Y G = f' ≫ pr1 Y G) (h₂ : f ≫ pr2 Y G = f' ≫ pr2 Y G) : f = f' :=
  pullback.hom_ext h₁ h₂

private theorem lift_comp_pr1 {Y G T : Over S} (t : T ⟶ Y) (a : T ⟶ G) :
    (lift t a).left ≫ pr1 Y G = t.left :=
  pullback.lift_fst t.left a.left (by rw [Over.w t, Over.w a])

private theorem lift_comp_pr2 {Y G T : Over S} (t : T ⟶ Y) (a : T ⟶ G) :
    (lift t a).left ≫ pr2 Y G = a.left :=
  pullback.lift_snd t.left a.left (by rw [Over.w t, Over.w a])

private noncomputable abbrev subH {Y G : Over S} (U : (Y ⊗ G).left.Opens) : Over Y.left :=
  Over.mk (U.ι ≫ pr1 Y G)

private theorem sub_sq {Y A G : Over S} (inc : G ⟶ A) (U : (Y ⊗ G).left.Opens) :
    (U.ι ≫ pr2 Y G ≫ inc.left) ≫ A.hom = (U.ι ≫ pr1 Y G) ≫ Y.hom := by
  simp only [Category.assoc, Over.w inc, pr_cond]

variable {Y A G : Over S} [GrpObj A] [GrpObj G] {A₀ : Over Y.left} [GrpObj A₀]
  {φ₀ : A₀.left ⟶ A.left}

private noncomputable def subJ (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) : subH U ⟶ A₀ :=
  Over.homMk (hP.1.lift (U.ι ≫ pr2 Y G ≫ inc.left) (U.ι ≫ pr1 Y G) (sub_sq inc U))
    (hP.1.lift_snd _ _ _)

private theorem subJ_fst (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) : (subJ hP inc U).left ≫ φ₀ = U.ι ≫ pr2 Y G ≫ inc.left :=
  hP.1.lift_fst _ _ _

private theorem subJ_snd (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) : (subJ hP inc U).left ≫ A₀.hom = U.ι ≫ pr1 Y G :=
  hP.1.lift_snd _ _ _

private theorem subJ_mono (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [Mono inc.left]
    (U : (Y ⊗ G).left.Opens) : Mono (subJ hP inc U) := by
  have : Mono (subJ hP inc U).left := by
    constructor
    intro Z x y e
    rw [← cancel_mono U.ι]
    apply pr_ext
    · have := congrArg (· ≫ A₀.hom) e
      simpa only [Category.assoc, subJ_snd] using this
    · rw [← cancel_mono inc.left]
      have := congrArg (· ≫ φ₀) e
      simpa only [Category.assoc, subJ_fst] using this
  exact Over.mono_of_mono_left _

private theorem subJ_iff (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) (T' : Over S) (t : T' ⟶ Y) (g : Over.mk t.left ⟶ A₀) :
    (∃ h : Over.mk t.left ⟶ subH U, h ≫ subJ hP inc U = g) ↔
      ∃ a : T' ⟶ G, a.left ≫ inc.left = g.left ≫ φ₀ ∧ Set.range (lift t a).left ⊆ U := by
  constructor
  · rintro ⟨h, rfl⟩
    have hh : h.left ≫ U.ι ≫ pr1 Y G = t.left := Over.w h
    have e : (h.left ≫ U.ι ≫ pr2 Y G) ≫ G.hom = T'.hom := by
      have e' : (h.left ≫ U.ι ≫ pr1 Y G) ≫ Y.hom = T'.hom := by rw [hh, Over.w t]
      simpa only [Category.assoc, pr_cond] using e'
    refine ⟨Over.homMk (h.left ≫ U.ι ≫ pr2 Y G) e, ?_, ?_⟩
    · show (h.left ≫ U.ι ≫ pr2 Y G) ≫ inc.left = (h ≫ subJ hP inc U).left ≫ φ₀
      simp only [Over.comp_left, Category.assoc, subJ_fst]
    · have : (lift t (Over.homMk (h.left ≫ U.ι ≫ pr2 Y G) e)).left = h.left ≫ U.ι := by
        apply pr_ext
        · rw [lift_comp_pr1, Category.assoc, hh]
        · rw [lift_comp_pr2]
          simp only [Category.assoc, Over.homMk_left]
      rw [this]
      rintro _ ⟨x, rfl⟩
      show _ ∈ (U : Set (Y ⊗ G).left)
      rw [← U.range_ι]
      exact ⟨h.left x, by simp⟩
  · rintro ⟨a, ha, hr⟩
    have hr' : Set.range (lift t a).left ⊆ Set.range U.ι := by
      rw [U.range_ι]; exact hr
    let s := IsOpenImmersion.lift U.ι (lift t a).left hr'
    have hs : s ≫ U.ι = (lift t a).left := IsOpenImmersion.lift_fac _ _ _
    have h1 : s ≫ U.ι ≫ pr1 Y G = t.left := by
      rw [← Category.assoc, hs, lift_comp_pr1]
    refine ⟨Over.homMk s h1, ?_⟩
    apply SubRep.pull_ext hP
    show (s ≫ (subJ hP inc U).left) ≫ φ₀ = _
    rw [Category.assoc, subJ_fst, ← ha, ← Category.assoc, ← Category.assoc, hs, lift_comp_pr2]

private theorem fac_iff (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) (K : Over Y.left) (g : K ⟶ A₀) :
    (∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g) ↔
      ∃ a : Over.mk (K.hom ≫ Y.hom) ⟶ G, a.left ≫ inc.left = g.left ≫ φ₀ ∧
        Set.range (lift (Over.homMk K.hom : Over.mk (K.hom ≫ Y.hom) ⟶ Y) a).left ⊆ U :=
  subJ_iff hP inc U (Over.mk (K.hom ≫ Y.hom)) (Over.homMk K.hom) g

private theorem fac_one (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = 1 := by
  refine (fac_iff hP inc U K 1).2 ⟨1, ?_, (hc _ _).1⟩
  have e := SubRep.pull_one hP (Over.mk (K.hom ≫ Y.hom)) K.hom rfl
  refine Eq.trans ?_ e.symm
  show ((1 : Over.mk (K.hom ≫ Y.hom) ⟶ G) ≫ inc).left = _
  rw [one_comp]

private theorem fac_sub (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) (g g' : K ⟶ A₀)
    (h : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g)
    (h' : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g') :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g * g'⁻¹ := by
  obtain ⟨a, ea, ra⟩ := (fac_iff hP inc U K g).1 h
  obtain ⟨b, eb, rb⟩ := (fac_iff hP inc U K g').1 h'
  refine (fac_iff hP inc U K _).2 ⟨a * b⁻¹, ?_, (hc _ _).2 a b ra rb⟩
  have i2 := SubRep.pull_inv hP (Over.mk (K.hom ≫ Y.hom)) K.hom rfl (g := g') (a := b ≫ inc) eb.symm
  have m := SubRep.pull_mul hP (Over.mk (K.hom ≫ Y.hom)) K.hom rfl (g := g) (a := a ≫ inc)
    (a' := (b ≫ inc)⁻¹) ea.symm i2
  refine Eq.trans ?_ m.symm
  show ((a * b⁻¹) ≫ inc).left = _
  have hi : b⁻¹ ≫ inc = (b ≫ inc)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_comp, inv_mul_cancel, one_comp])
  rw [mul_comp, hi]

private theorem fac_inv (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) (g : K ⟶ A₀)
    (h : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g) :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g⁻¹ := by
  have := fac_sub hP inc U hc K 1 g (fac_one hP inc U hc K) h
  rwa [_root_.one_mul] at this

private theorem fac_mul (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) (g g' : K ⟶ A₀)
    (h : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g)
    (h' : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g') :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g * g' := by
  have := fac_sub hP inc U hc K g g'⁻¹ h (fac_inv hP inc U hc K g' h')
  rwa [inv_inv] at this

end UpperTheory.ProductProjectionSubgroup

open UpperTheory.ProductProjectionSubgroup in
theorem UpperTheory.exists_lift_of_closed_subgroup_locus :
    ∀ {S : Scheme.{0}} (Y A G : Over S) [GrpObj A] [GrpObj G] (inc : G ⟶ A) [IsFinite G.hom] [Etale G.hom] (U : (Y ⊗ G).left.Opens), Mono inc → IsMonHom inc → IsClosed (U : Set (Y ⊗ G).left) → (∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧ ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U → Set.range (lift t (a * b⁻¹)).left ⊆ U) → ∀ (A₀ : Over Y.left) [GrpObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (j : H ⟶ A₀), IsMonHom j ∧ Mono j ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ (T' : Over S) (t : T' ⟶ Y) (g : Over.mk t.left ⟶ A₀), (∃ h : Over.mk t.left ⟶ H, h ≫ j = g) ↔ ∃ a : T' ⟶ G, a.left ≫ inc.left = g.left ≫ φ₀ ∧ Set.range (lift t a).left ⊆ U := by
  intro S Y A G _ _ inc _ _ U hm hmon hU hc A₀ _ φ₀ hP
  have hmL : Mono inc.left := Over.mono_left_of_mono inc
  have hmj := subJ_mono hP inc U
  have hcl : IsClosedImmersion U.ι := .of_isPreimmersion _ (by simpa using hU)
  have hf1 : IsFinite (pr1 Y G) := inferInstanceAs (IsFinite (pullback.fst Y.hom G.hom))
  have he1 : Etale (pr1 Y G) := inferInstanceAs (Etale (pullback.fst Y.hom G.hom))
  have hf : IsFinite (subH U).hom := inferInstanceAs (IsFinite (U.ι ≫ pr1 Y G))
  have he : Etale (subH U).hom := inferInstanceAs (Etale (U.ι ≫ pr1 Y G))
  obtain ⟨m, hm'⟩ := fac_mul hP inc U hc (subH U ⊗ subH U) (fst _ _ ≫ subJ hP inc U)
    (snd _ _ ≫ subJ hP inc U) ⟨_, rfl⟩ ⟨_, rfl⟩
  obtain ⟨e, he'⟩ := fac_one hP inc U hc (𝟙_ (Over Y.left))
  obtain ⟨v, hv⟩ := fac_inv hP inc U hc (subH U) (subJ hP inc U) ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨gH, hj⟩ := GlobalTheory.T.exists_grpObj_isMonHom_of_mono_factor Y.left A₀ (subH U) (subJ hP inc U) hmj
    ⟨m, by rw [hm', Hom.mul_def, lift_fst_comp_snd_comp]⟩
    ⟨e, by rw [he', Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]⟩
    ⟨v, by rw [hv, Hom.inv_def]⟩
  exact ⟨subH U, gH, subJ hP inc U, hj, hmj, hf, he, subJ_iff hP inc U⟩
