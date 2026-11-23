import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpSpread

open GrpDense

variable {Z U : Scheme.{0}} {j : U ⟶ Z}

theorem hom_ext_of_points (j : U ⟶ Z) [QuasiCompact j] [IsSchemeTheoreticallyDominant j] {X Y : Over Z}
    [Flat X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have hsd : IsSchemeTheoreticallyDominant (pullback.fst X.hom j) := inferInstance
  let t : Over.mk ((Over.mk (pullback.snd X.hom j) : Over U).hom ≫ j) ⟶ X :=
    Over.homMk (pullback.fst X.hom j) pullback.condition
  have ht : t ≫ f = t ≫ g := h _ t
  have hdom : IsSchemeTheoreticallyDominant
      ((equalizer.lift t ht).left ≫ (equalizer.ι f g).left) := by
    rw [← Over.comp_left, equalizer.lift_ι]
    exact hsd
  have hker : (equalizer.ι f g).left.ker = ⊥ :=
    le_bot_iff.mp ((Scheme.Hom.le_ker_comp _ _).trans hdom.ker_eq_bot.le)
  have : IsIso (equalizer.ι f g).left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  ext1
  rw [← cancel_epi (equalizer.ι f g).left, ← Over.comp_left, ← Over.comp_left, equalizer.condition]

variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}

def sq (w : φ ≫ G.hom = A.hom ≫ j) : (A ⊗ A).left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left

theorem isSquare_sq (w : φ ≫ G.hom = A.hom ≫ j) : IsSquare φ (sq w) := by
  constructor
  · simp only [sq]
    rw [← Over.comp_left, lift_fst]
    rfl
  · simp only [sq]
    rw [← Over.comp_left, lift_snd]
    rfl

theorem sq_ext {W : Scheme.{0}} {a b : W ⟶ (G ⊗ G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := by
  have hab : a ≫ (G ⊗ G).hom = b ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← Category.assoc, h₁]
  let a' : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk a rfl
  let b' : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk b hab.symm
  have e : a' = b' := CartesianMonoidalCategory.hom_ext _ _
    (Over.OverMorphism.ext (by simpa [a', b'] using h₁))
    (Over.OverMorphism.ext (by simpa [a', b'] using h₂))
  exact congrArg CommaMorphism.left e

theorem eq_sq (w : φ ≫ G.hom = A.hom ≫ j) {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) :
    φ₂ = sq w := sq_ext (h.1.trans (isSquare_sq w).1.symm) (h.2.trans (isSquare_sq w).2.symm)

theorem isPullback_sq (hA : IsPullback φ A.hom G.hom j) :
    IsPullback (sq hA.w) (A ⊗ A).hom (G ⊗ G).hom j := by
  have hs := isSquare_sq hA.w
  have comm : sq hA.w ≫ (G ⊗ G).hom = (A ⊗ A).hom ≫ j := by
    rw [← Over.w (fst G G), ← Category.assoc, hs.1, Category.assoc, hA.w, ← Category.assoc,
      Over.w (fst A A)]
  let u : ∀ (s : PullbackCone (G ⊗ G).hom j) (p : G ⊗ G ⟶ G), s.pt ⟶ A.left := fun s p =>
    hA.lift (s.fst ≫ p.left) s.snd (by rw [Category.assoc, Over.w p, s.condition])
  let L : ∀ s : PullbackCone (G ⊗ G).hom j, s.pt ⟶ (A ⊗ A).left := fun s =>
    (lift (Over.homMk (u s (fst G G)) (hA.lift_snd _ _ _) : Over.mk s.snd ⟶ A)
      (Over.homMk (u s (snd G G)) (hA.lift_snd _ _ _) : Over.mk s.snd ⟶ A)).left
  have L1 : ∀ s, L s ≫ (fst A A).left = u s (fst G G) := fun s => by
    simp only [L]
    rw [← Over.comp_left, lift_fst]
    rfl
  have L2 : ∀ s, L s ≫ (snd A A).left = u s (snd G G) := fun s => by
    simp only [L]
    rw [← Over.comp_left, lift_snd]
    rfl
  have fl : ∀ s : PullbackCone (G ⊗ G).hom j, L s ≫ sq hA.w = s.fst := fun s => by
    apply sq_ext
    · rw [Category.assoc, hs.1, ← Category.assoc, L1]
      exact hA.lift_fst _ _ _
    · rw [Category.assoc, hs.2, ← Category.assoc, L2]
      exact hA.lift_fst _ _ _
  have fr : ∀ s : PullbackCone (G ⊗ G).hom j, L s ≫ (A ⊗ A).hom = s.snd := fun s => by
    rw [← Over.w (fst A A), ← Category.assoc, L1]
    exact hA.lift_snd _ _ _
  have un : ∀ (s : PullbackCone (G ⊗ G).hom j) (m : s.pt ⟶ (A ⊗ A).left),
      m ≫ sq hA.w = s.fst → m ≫ (A ⊗ A).hom = s.snd → m = L s := fun s m h1 h2 => by
    apply sq_ext
    · rw [L1]
      apply hA.hom_ext
      · rw [hA.lift_fst, Category.assoc, ← hs.1, ← Category.assoc, h1]
      · rw [hA.lift_snd, Category.assoc, Over.w (fst A A), h2]
    · rw [L2]
      apply hA.hom_ext
      · rw [hA.lift_fst, Category.assoc, ← hs.2, ← Category.assoc, h1]
      · rw [hA.lift_snd, Category.assoc, Over.w (snd A A), h2]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm L fl fr un)

private theorem flat_tensor_hom {S : Scheme.{0}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

private theorem flat_tensorUnit_hom {S : Scheme.{0}} : Flat (𝟙_ (Over S)).hom := by
  show Flat (𝟙 S)
  have : IsOpenImmersion (𝟙 S) := inferInstance
  infer_instance

theorem exists_grpObj (j : U ⟶ Z) [QuasiCompact j] [IsSchemeTheoreticallyDominant j] [Flat G.hom]
    [IsSeparated G.hom] [GrpObj A] [IsCommMonObj A] (h : IsPullback φ A.hom G.hom j)
    (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G)
    (hm : sq h.w ≫ m.left = (μ[A]).left ≫ φ) (hi : φ ≫ i.left = (ι[A]).left ≫ φ)
    (he : j ≫ e.left = (η[A]).left ≫ φ) : ∃ _ : GrpObj G, IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  have hm' : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ :=
    fun φ₂ hφ => by rw [eq_sq h.w hφ, hm]
  have pmul : ∀ {T : Over U} (x y : T ⟶ A),
      lift (pushPt h.w x) (pushPt h.w y) ≫ m = pushPt h.w (x * y) :=
    fun x y => GrpDense.pushPt_mul h.w hm' x y
  have pinv : ∀ {T : Over U} (x : T ⟶ A), pushPt h.w x ≫ i = pushPt h.w x⁻¹ :=
    fun x => GrpDense.pushPt_inv h.w hi x
  have pone : ∀ (T : Over U), toUnit _ ≫ e = pushPt h.w (1 : T ⟶ A) :=
    fun T => GrpDense.pushPt_one h.w he T
  have psurj : ∀ (T : Over U) (x₀ : Over.mk (T.hom ≫ j) ⟶ G), ∃ x : T ⟶ A, pushPt h.w x = x₀ :=
    GrpDense.pushPt_surjective h
  have : Flat (𝟙_ (Over Z)).hom := flat_tensorUnit_hom
  have : Flat (G ⊗ G).hom := flat_tensor_hom G G
  have : Flat ((G ⊗ G) ⊗ G).hom := flat_tensor_hom _ G
  have : Flat (𝟙_ (Over Z) ⊗ G).hom := flat_tensor_hom _ G
  have : Flat (G ⊗ 𝟙_ (Over Z)).hom := flat_tensor_hom G _
  letI inst : GrpObj G :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T (t ≫ snd _ _)
        have ht : t ≫ e ▷ G = lift (pushPt h.w 1) (pushPt h.w x) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, toUnit_unique (t ≫ fst _ _) (toUnit _),
              pone, lift_fst]
          · rw [Category.assoc, whiskerRight_snd, hx, lift_snd]
        rw [← Category.assoc, ht, pmul, _root_.one_mul, hx, leftUnitor_hom]
      mul_one := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T (t ≫ fst _ _)
        have ht : t ≫ G ◁ e = lift (pushPt h.w x) (pushPt h.w 1) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [Category.assoc, whiskerLeft_fst, hx, lift_fst]
          · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, toUnit_unique (t ≫ snd _ _) (toUnit _),
              pone, lift_snd]
        rw [← Category.assoc, ht, pmul, _root_.mul_one, hx, rightUnitor_hom]
      mul_assoc := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := psurj T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := psurj T (t ≫ snd _ _)
        have ht : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          apply CartesianMonoidalCategory.hom_ext
          · apply CartesianMonoidalCategory.hom_ext
            · simp only [Category.assoc, lift_fst]
              exact hx.symm
            · simp only [Category.assoc, lift_fst_assoc, lift_snd]
              exact hy.symm
          · simp only [lift_snd]
            exact hz.symm
        rw [ht, lift_whiskerRight_assoc, pmul, pmul, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
          pmul, pmul, _root_.mul_assoc]
      left_inv := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T t
        rw [← hx, ← Category.assoc, comp_lift, pinv, Category.comp_id, pmul, _root_.inv_mul_cancel,
          ← Category.assoc, toUnit_unique (pushPt h.w x ≫ toUnit _) (toUnit _), pone]
      right_inv := by
        apply hom_ext_of_points j
        intro T t
        obtain ⟨x, hx⟩ := psurj T t
        rw [← hx, ← Category.assoc, comp_lift, pinv, Category.comp_id, pmul, _root_.mul_inv_cancel,
          ← Category.assoc, toUnit_unique (pushPt h.w x ≫ toUnit _) (toUnit _), pone] }
  refine ⟨inst, ⟨?_⟩, ⟨h, ?_⟩⟩
  · apply hom_ext_of_points j
    intro T t
    obtain ⟨x, hx⟩ := psurj T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := psurj T (t ≫ snd _ _)
    have ht : t = lift (pushPt h.w x) (pushPt h.w y) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [hx, lift_fst]
      · rw [hy, lift_snd]
    show t ≫ (β_ G G).hom ≫ m = t ≫ m
    rw [ht, lift_braiding_hom_assoc, pmul, pmul, _root_.mul_comm]
  · intro T x y x₀ y₀ hx hy
    have ex : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    have ey : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    rw [ex, ey]
    show (lift (pushPt h.w x) (pushPt h.w y) ≫ m).left = _
    rw [pmul]
    rfl

theorem exists_fg_descent {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {B B' X : Scheme.{0}}
    (pB : B ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] (p : X ⟶ Sp k) [LocallyOfFinitePresentation p]
    {q' : B' ⟶ Sp V} {b : B' ⟶ B} (hb : IsPullback b q' pB (spMap (algebraMap k V))) (f : B' ⟶ X)
    (hf : f ≫ p = b ≫ pB) :
    ∃ R : Subalgebra k V, R.FG ∧ ∀ (R' : Subalgebra k V), R ≤ R' → ∀ (B₁ : Scheme.{0}) (q₁ : B₁ ⟶ Sp R')
      (b₁ : B₁ ⟶ B) (c : B' ⟶ B₁), b₁ ≫ pB = q₁ ≫ spMap (algebraMap k R') → c ≫ b₁ = b →
      c ≫ q₁ = q' ≫ spMap R'.val.toRingHom →
      ∃ g : B₁ ⟶ X, c ≫ g = f ∧ g ≫ p = q₁ ≫ spMap (algebraMap k R') := by
  let φ' : pullback pB (spMap (algebraMap k V)) ⟶ X := hb.isoPullback.inv ≫ f
  have hφ' : φ' ≫ p = pullback.fst _ _ ≫ pB := by
    simp only [φ', Category.assoc, hf, hb.isoPullback_inv_fst_assoc]
  obtain ⟨R, ψ, hR, hψp, hψ⟩ := GlobalTheory.Spread.exists_fg_comp_eq pB p φ' hφ'
  refine ⟨R, hR, fun R' hRR' B₁ q₁ b₁ c h1 h2 h3 => ?_⟩
  have cond : b₁ ≫ pB = (q₁ ≫ spMap (Subalgebra.inclusion hRR').toRingHom) ≫ spMap (algebraMap k R) := by
    rw [h1, Category.assoc, GlobalTheory.Spread.spMap_algHom_comp]
  refine ⟨pullback.lift b₁ _ cond ≫ ψ, ?_, ?_⟩
  · have e : (R'.val.toRingHom).comp (Subalgebra.inclusion hRR').toRingHom = R.val.toRingHom := by
      ext; rfl
    have key : c ≫ pullback.lift b₁ _ cond = hb.isoPullback.hom ≫ GlobalTheory.Spread.bcMap pB R.val := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, GlobalTheory.Spread.bcMap_fst, hb.isoPullback_hom_fst, h2]
      · simp only [Category.assoc, pullback.lift_snd, GlobalTheory.Spread.bcMap_snd, hb.isoPullback_hom_snd_assoc]
        rw [← Category.assoc, h3, Category.assoc, ← spMap_comp, e]
    rw [← Category.assoc, key, Category.assoc, hψ, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, hψp, pullback.lift_fst_assoc, h1]

end GlobalTheory.GrpSpread

namespace GlobalTheory

open GrpSpread

theorem grpObj_descends_to_fg_subalgebra :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (X : Scheme.{0}) (p : X ⟶ Sp k) (φ : A.left ⟶ X) (F : Finset V), Smooth p → IsSeparated p → QuasiCompact p → IsPullback φ A.hom p (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (ψ : A.left ⟶ A₀.left), (F : Set V) ⊆ R ∧ R.FG ∧ Smooth A₀.hom ∧ IsSeparated A₀.hom ∧ QuasiCompact A₀.hom ∧ IsGrpPullback A A₀ (spMap R.val.toRingHom) ψ := by
  intro k V _ _ _ A _ _ X p φ F hsm hsep hqc hA
  let G : Over (Sp k) := Over.mk p
  have hAG : IsPullback φ A.hom G.hom (spMap (algebraMap k V)) := hA
  have : QuasiCompact (G ⊗ G).hom := by
    rw [Over.tensorObj_hom]
    show QuasiCompact (pullback.fst p p ≫ p)
    infer_instance
  have : QuasiSeparated (G ⊗ G).hom := by
    rw [Over.tensorObj_hom]
    show QuasiSeparated (pullback.fst p p ≫ p)
    infer_instance
  have : LocallyOfFinitePresentation p := inferInstance

  have hf₁ : ((μ[A]).left ≫ φ) ≫ p = sq hAG.w ≫ (G ⊗ G).hom := by
    rw [Category.assoc, hA.w, ← Category.assoc, Over.w (μ[A]), (isPullback_sq hAG).w]
  obtain ⟨R₁, hR₁, H₁⟩ := exists_fg_descent (G ⊗ G).hom p (isPullback_sq hAG) _ hf₁
  have hf₂ : ((ι[A]).left ≫ φ) ≫ p = φ ≫ p := by
    rw [Category.assoc, hA.w, ← Category.assoc, Over.w (ι[A])]
  obtain ⟨R₂, hR₂, H₂⟩ := exists_fg_descent p p hA _ hf₂
  have hf₃ : ((η[A]).left ≫ φ) ≫ p = spMap (algebraMap k V) ≫ 𝟙 (Sp k) := by
    rw [Category.assoc, hA.w, ← Category.assoc, Over.w (η[A]), Category.comp_id]
    exact Category.id_comp _
  obtain ⟨R₃, hR₃, H₃⟩ := exists_fg_descent (𝟙 (Sp k)) p
    (IsPullback.id_vert (spMap (algebraMap k V))) ((η[A]).left ≫ φ) hf₃
  let R : Subalgebra k V := R₁ ⊔ R₂ ⊔ R₃ ⊔ Algebra.adjoin k (F : Set V)
  have hRfg : R.FG := ((hR₁.sup hR₂).sup hR₃).sup (Subalgebra.fg_adjoin_finset F)
  have le₁ : R₁ ≤ R := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have le₂ : R₂ ≤ R := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have le₃ : R₃ ≤ R := le_sup_right.trans le_sup_left
  have hF : (F : Set V) ⊆ R := fun x hx => (le_sup_right : Algebra.adjoin k (F : Set V) ≤ R)
    (Algebra.subset_adjoin hx)

  obtain ⟨A₀, f₀, h₀, hsm₀, hse₀, hqc₀⟩ : ∃ (A₀ : Over (Sp R)) (f₀ : A₀.left ⟶ X),
      IsPullback f₀ A₀.hom p (spMap (algebraMap k R)) ∧ Smooth A₀.hom ∧ IsSeparated A₀.hom ∧
        QuasiCompact A₀.hom :=
    ⟨Over.mk (pullback.snd p _), pullback.fst p _, IsPullback.of_hasPullback _ _,
      by dsimp; infer_instance, by dsimp; infer_instance, by dsimp; infer_instance⟩
  have h₀G : IsPullback f₀ A₀.hom G.hom (spMap (algebraMap k R)) := h₀

  have hP := GlobalTheory.Spread.isPullback_bcMap (𝟙 (Sp k)) R.val
  have : Flat (𝟙 (Sp k)) := by
    have : IsOpenImmersion (𝟙 (Sp k)) := inferInstance
    infer_instance
  have := GlobalTheory.Spread.isSchemeTheoreticallyDominant_bcMap (𝟙 (Sp k)) R.val Subtype.val_injective
  have eJ : spMap R.val.toRingHom = inv (pullback.snd (𝟙 (Sp k)) (spMap (algebraMap k V))) ≫
      GlobalTheory.Spread.bcMap (𝟙 (Sp k)) R.val ≫ pullback.snd _ _ := by
    rw [hP.w, IsIso.inv_hom_id_assoc]
  have : IsSchemeTheoreticallyDominant (spMap R.val.toRingHom) := by
    rw [eJ]
    infer_instance
  have : QuasiCompact (spMap R.val.toRingHom) := by
    rw [eJ]
    infer_instance
  have eV : spMap R.val.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k V) :=
    GlobalTheory.Spread.spMap_algHom_comp R.val
  obtain ⟨ψ, hψ₁, hψ₂⟩ : ∃ ψ : A.left ⟶ A₀.left, ψ ≫ f₀ = φ ∧ ψ ≫ A₀.hom = A.hom ≫ spMap R.val.toRingHom :=
    ⟨h₀.lift φ (A.hom ≫ spMap R.val.toRingHom) (by rw [hA.w, Category.assoc, eV]),
      h₀.lift_fst _ _ _, h₀.lift_snd _ _ _⟩
  have hψ : IsPullback ψ A.hom A₀.hom (spMap R.val.toRingHom) := by
    refine IsPullback.of_right ?_ hψ₂ h₀
    rw [hψ₁, eV]
    exact hA

  have c₂ : sq hψ.w ≫ sq h₀G.w = sq hAG.w := by
    apply sq_ext
    · rw [Category.assoc, (isSquare_sq h₀G.w).1, ← Category.assoc, (isSquare_sq hψ.w).1, Category.assoc,
        hψ₁, (isSquare_sq hAG.w).1]
    · rw [Category.assoc, (isSquare_sq h₀G.w).2, ← Category.assoc, (isSquare_sq hψ.w).2, Category.assoc,
        hψ₁, (isSquare_sq hAG.w).2]
  obtain ⟨g₁, hg₁, hg₁p⟩ := H₁ R le₁ (A₀ ⊗ A₀).left (A₀ ⊗ A₀).hom (sq h₀G.w) (sq hψ.w)
    (isPullback_sq h₀G).w c₂ (isPullback_sq hψ).w
  let m₀ : A₀ ⊗ A₀ ⟶ A₀ := Over.homMk (h₀.lift g₁ (A₀ ⊗ A₀).hom hg₁p) (h₀.lift_snd _ _ _)
  have hm : sq hψ.w ≫ m₀.left = (μ[A]).left ≫ ψ := by
    apply h₀.hom_ext
    · simp only [m₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_fst, hg₁, Category.assoc, hψ₁]
    · simp only [m₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_snd, (isPullback_sq hψ).w, Category.assoc, hψ₂,
        ← Category.assoc, Over.w (μ[A])]

  obtain ⟨g₂, hg₂, hg₂p⟩ := H₂ R le₂ A₀.left A₀.hom f₀ ψ h₀.w hψ₁ hψ₂
  let i₀ : A₀ ⟶ A₀ := Over.homMk (h₀.lift g₂ A₀.hom hg₂p) (h₀.lift_snd _ _ _)
  have hi : ψ ≫ i₀.left = (ι[A]).left ≫ ψ := by
    apply h₀.hom_ext
    · simp only [i₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_fst, hg₂, Category.assoc, hψ₁]
    · simp only [i₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_snd, hψ₂, Category.assoc, hψ₂, ← Category.assoc,
        Over.w (ι[A])]

  obtain ⟨g₃, hg₃, hg₃p⟩ := H₃ R le₃ (Sp R) (𝟙 _) (spMap (algebraMap k R)) (spMap R.val.toRingHom)
    (by rw [Category.comp_id, Category.id_comp]) eV (by rw [Category.comp_id, Category.id_comp])
  let e₀ : 𝟙_ (Over (Sp R)) ⟶ A₀ := Over.homMk (h₀.lift g₃ (𝟙 (Sp R)) hg₃p) (h₀.lift_snd _ _ _)
  have he : spMap R.val.toRingHom ≫ e₀.left = (η[A]).left ≫ ψ := by
    apply h₀.hom_ext
    · simp only [e₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_fst, hg₃, Category.assoc, hψ₁]
    · simp only [e₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_snd, Category.comp_id, Category.assoc, hψ₂,
        ← Category.assoc, Over.w (η[A])]
      exact (Category.id_comp _).symm
  obtain ⟨inst, hcomm, hgp⟩ := exists_grpObj (spMap R.val.toRingHom) hψ m₀ i₀ e₀ hm hi he
  exact ⟨R, A₀, inst, hcomm, ψ, hF, hRfg, hsm₀, hse₀, hqc₀, hgp⟩

end GlobalTheory
