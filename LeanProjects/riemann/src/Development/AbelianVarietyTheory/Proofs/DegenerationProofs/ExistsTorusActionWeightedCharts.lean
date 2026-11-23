import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpan
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionAbelianPartBundleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfWeightEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionNeZeroAtStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointTranslatePure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisUniqueMinAndSumsSeparated
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FibTorus
open GlobalTheory.ZJ

theorem block {k I J C : Type} [Field k] [Fintype I] [Fintype J] (m : Matrix J J k) (hm : IsUnit m.det)
    (e : I ≃ J) (w' : I → C) (w : J → C) (h : ∀ i j, m (e i) j ≠ 0 → w' i = w j) (c : C) (a : J → k)
    (ha : ∀ j, a j ≠ 0 → w j = c) :
    ∃ b : {i // w' i = c} → k, ∀ j, a j = ∑ i, b i * m (e i.1) j := by
  let b := Matrix.vecMul a m⁻¹
  have hb : Matrix.vecMul b m = a := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hm, Matrix.vecMul_one]
  refine ⟨fun i => b (e i.1), fun j => ?_⟩
  by_cases hj : w j = c
  · have h1 : a j = ∑ i, b (e i) * m (e i) j := by
      rw [← hb, Matrix.vecMul, dotProduct]
      exact (e.sum_comp fun i => b i * m i j).symm
    rw [h1, ← Fintype.sum_subtype_add_sum_subtype (fun i => w' i = c)]
    rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ w' i = c})), add_zero]
    intro i _
    have : m (e i.1) j = 0 := by
      by_contra hne
      exact i.2 ((h _ _ hne).trans hj)
    rw [this, mul_zero]
  · have h1 : a j = 0 := by
      by_contra hne
      exact hj (ha j hne)
    rw [h1, Finset.sum_eq_zero]
    intro i _
    have : m (e i.1) j = 0 := by
      by_contra hne
      exact hj ((h _ _ hne).symm.trans i.2)
    rw [this, mul_zero]

def cst {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem constFn_eq {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) (a : k) :
    constFn p U a = cst p U a := rfl

theorem isLin_comp {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X} {I J : Type} [Fintype I]
    [Fintype J] {F : J → H.Sec} {F' : I → H.Sec} {m : I → J → k} (hF : ∀ i, IsLin p F (m i) (F' i))
    {a : J → k} {b : I → k} (hab : ∀ j, a j = ∑ i, b i * m i j) {φ : H.Sec} (h : IsLin p F a φ) :
    IsLin p F' b φ := by
  intro l
  rw [h l]
  simp only [fun i => hF i l, hab, constFn_eq, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    _root_.mul_assoc]
  exact Finset.sum_comm

theorem cf_mul {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
    {f : A →+* R} {m : Multiplicative X →* R}
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
    (χ : X) (b : A) (s : R) : WtPart.cf hb χ (f b * s) = b * WtPart.cf hb χ s := by
  obtain ⟨a, rfl⟩ := hb.2 s
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, mul_zero, WtPart.cf_zero]
  | add x y hx hy => simp only [map_add, mul_add, WtPart.cf_add, hx, hy]
  | single ψ c =>
    rw [AddMonoidAlgebra.liftNCRingHom_single, ← _root_.mul_assoc, ← map_mul, WtPart.cf_mono, WtPart.cf_mono,
      mul_ite, mul_zero]

variable {k : Type} [Field k] (Φ : FibPre k)

theorem app_constFn (U : Φ.E.B.left.Opens) (a : k) :
    (Φ.D.q.left.app U).hom (constFn Φ.E.B.hom U a) = constFn Φ.G.hom (Φ.D.q.left ⁻¹ᵁ U) a := by
  rw [constFn_eq, constFn_eq, ← Over.w Φ.D.q]
  unfold cst
  rw [RingHom.comp_apply, RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]

theorem wt_lin {d : ℕ} {J : Type} [Fintype J] {F : J → (Φ.H d).Sec} {a : J → k} {φ : (Φ.H d).Sec}
    (h : IsLin Φ.G.hom F a φ) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.wt φ α l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l := by
  unfold FibPre.wt
  rw [h l]
  refine (WtPart.cf_sum (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans ?_ (cf_mul (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α _ _)
  rw [app_constFn]
  rfl

theorem wt_eq_zero {d : ℕ} {φ : (Φ.H d).Sec} {α β : Φ.E.X} (h : Φ.Pure α φ) (hne : β ≠ α) (l : Φ.N₀.ι) :
    Φ.wt φ β l = 0 := by
  by_contra h0
  exact hne (h ⟨l, h0⟩)

theorem pure_lin {d : ℕ} {J : Type} [Fintype J] {F : J → (Φ.H d).Sec} {a : J → k} {φ : (Φ.H d).Sec}
    (h : IsLin Φ.G.hom F a φ) {α : Φ.E.X} (ha : ∀ i, a i ≠ 0 → Φ.Pure α (F i)) : Φ.Pure α φ := by
  rintro β ⟨l, hl⟩
  by_contra hne
  apply hl
  rw [wt_lin Φ h]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : a i = 0
  · rw [hi, constFn_eq, map_zero, zero_mul]
  · rw [wt_eq_zero Φ (ha i hi) hne, mul_zero]

def OnlyShort {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (N : ℕ) (α : X) : Prop :=
  ∀ ν : X, ν ≠ 0 → q α < q (α + N • ν)

theorem OnlyShort.short {X : Type} [AddCommGroup X] {q : QuadraticMap ℤ X ℝ} {N : ℕ} {α : X}
    (h : OnlyShort q N α) : Short q N α := fun ν => by
  by_cases hν : ν = 0
  · rw [hν, smul_zero, add_zero]
  · exact (h ν hν).le

theorem OnlyShort.eq {X : Type} [AddCommGroup X] {q : QuadraticMap ℤ X ℝ} {N : ℕ} {α β : X}
    (h : OnlyShort q N α) (hβ : Short q N β) {ν : X} (e : β = α + N • ν) : β = α := by
  by_cases hν : ν = 0
  · rw [e, hν, smul_zero, add_zero]
  · have h1 := hβ (-ν)
    rw [e, smul_neg, add_neg_cancel_right] at h1
    exact absurd (h ν hν) (not_lt.2 h1)

theorem onlyShort_zero {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {N : ℕ} (hN : N ≠ 0) : OnlyShort q N 0 := by
  intro ν hν
  rw [zero_add, map_zero]
  by_contra hle
  have hx : (N • ν : X) ≠ 0 := by
    rw [← natCast_zsmul]
    exact smul_ne_zero (Int.natCast_ne_zero.2 hN) hν
  have hfin : {x | ¬ 1 ≤ q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_ge_atTop 1)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • (N • ν))
    (smul_left_injective ℤ hx) (fun n => ?_) hfin
  change ¬ 1 ≤ q (n • (N • ν))
  rw [QuadraticMap.map_smul, zsmul_eq_mul]
  have : ((n * n : ℤ) : ℝ) * q (N • ν) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast mul_self_nonneg n) (not_lt.1 hle)
  linarith

section Span
variable {Φ} {N : ℕ} {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X}
  {F : J → (Φ.H 1).Sec} (hG : Φ.Good N q cls F) {α : Φ.E.X} (hα : OnlyShort q N α)
include hG hα

theorem pure_of_cls {i : J} (hi : ∃ n, α = cls i + N • n) : Φ.Pure α (F i) := by
  intro β hβ
  obtain ⟨hs, ν, hν⟩ := hG.supp i β hβ
  obtain ⟨n, hn⟩ := hi
  refine hα.eq hs (ν := ν - n) ?_
  rw [hν, hn, smul_sub]
  abel

theorem exists_isLin {φ : (Φ.H 1).Sec} (hφ : Φ.Pure α φ) :
    ∃ a : J → k, (∀ i, a i ≠ 0 → ∃ n, α = cls i + N • n) ∧ IsLin Φ.G.hom F a φ := by
  obtain ⟨a, ha, hw⟩ := hG.onto α hα.short φ hφ
  obtain ⟨ψ, hψ, -⟩ := SecRatio.existsUnique_isLin Φ.G.hom F a
  refine ⟨a, ha, ?_⟩
  suffices φ = ψ from this ▸ hψ
  refine WtPart.sec_ext Φ _ _ fun β l => ?_
  by_cases hβ : β = α
  · rw [hβ, hw, wt_lin Φ hψ]
  · rw [wt_eq_zero Φ hφ hβ, wt_eq_zero Φ (pure_lin Φ hψ fun i hi => pure_of_cls hG hα (ha i hi)) hβ]

end Span

theorem ap_res {Y Z : Scheme.{0}} (m : Z ⟶ Y) {U W : Y.Opens} (h : W ≤ U)
    (hm : ⊤ ≤ m ⁻¹ᵁ W) (hg : ⊤ ≤ m ⁻¹ᵁ U) (u : Γ(Y, U)) :
    (m.appLE W ⊤ hm).hom (resG Y h u) = (m.appLE U ⊤ hg).hom u :=
  congrArg (fun φ => φ.hom u) (Scheme.Hom.map_appLE m hm (homOfLE h).op)

theorem ap_comp {X Y Z : Scheme.{0}} (j : Z ⟶ Y) (m : Y ⟶ X) (n : Z ⟶ X) (e : n = j ≫ m) {U : X.Opens}
    (hm : ⊤ ≤ m ⁻¹ᵁ U) (hn : ⊤ ≤ n ⁻¹ᵁ U) (u : Γ(X, U)) :
    j.appTop.hom ((m.appLE U ⊤ hm).hom u) = (n.appLE U ⊤ hn).hom u := by
  subst e
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact congrArg (fun φ => φ.hom u) (Scheme.Hom.appLE_comp_appLE j m U ⊤ ⊤ _ _)

theorem eq_of_cover {Y : Scheme.{0}} {I : Type} (U : I → Y.Opens) (hU : ⨆ l, U l = ⊤) {u v : Γ(Y, ⊤)}
    (h : ∀ l, (U l).ι.appTop.hom u = (U l).ι.appTop.hom v) : u = v := by
  refine Y.sheaf.eq_of_locally_eq' U ⊤ (fun l => homOfLE le_top) hU.ge _ _ fun l => ?_
  apply (FunDescent.res_bijective (U l)).1
  have e : ∀ w : Γ(Y, ⊤), (FunDescent.res (U l)).hom (resG Y le_top w) = (U l).ι.appTop.hom w := fun w => by
    refine (ap_res (U l).ι le_top _ le_top w).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  exact (e u).trans ((h l).trans (e v).symm)

theorem hasWt_of_cover {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) {I : Type} (U : I → H.left.Opens) (hU : ⨆ l, U l = ⊤) {V : H.left.Opens}
    {u : Γ(H.left, V)} {χ : X}
    (h : ∀ (l : I) (Y : Over S) (t : Y ⟶ splitTorus S X) (g : Y ⟶ H) (h : ⊤ ≤ g.left ⁻¹ᵁ V)
      (h' : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V), ⊤ ≤ g.left ⁻¹ᵁ U l →
      (((t ≫ i) * g).left.appLE V ⊤ h').hom u =
        t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE V ⊤ h).hom u) : HasWt i V u χ := by
  intro Y t g h₁ h₂
  refine eq_of_cover (fun l => g.left ⁻¹ᵁ U l)
    (by rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]) fun l => ?_
  let Y' : Over S := Over.mk ((g.left ⁻¹ᵁ U l).ι ≫ Y.hom)
  let j : Y' ⟶ Y := Over.homMk (g.left ⁻¹ᵁ U l).ι rfl
  have e : ((j ≫ t) ≫ i) * (j ≫ g) = j ≫ ((t ≫ i) * g) := by
    rw [Category.assoc, MonObj.comp_mul]
  have k₁ : ⊤ ≤ (j ≫ g).left ⁻¹ᵁ V := fun y _ => h₁ (x := j.left y) trivial
  have k₂ : ⊤ ≤ (((j ≫ t) ≫ i) * (j ≫ g)).left ⁻¹ᵁ V := by
    rw [e]
    exact fun y _ => h₂ (x := j.left y) trivial
  have := h l Y' (j ≫ t) (j ≫ g) k₁ k₂ (fun y _ => y.2)
  change j.left.appTop.hom _ = j.left.appTop.hom _
  rw [map_mul, ap_comp j.left _ _ (congrArg Over.Hom.left e) h₂ k₂, ap_comp j.left _ _ rfl h₁ k₁, this]
  congr 1

theorem ap_ratio {X Y : Scheme.{0}} {H : LB X} {s t : H.Sec} {W : X.Opens} {r : Γ(X, W)} (hr : IsRatio s t W r)
    (g : Y ⟶ X) (l : H.ι) (h : ⊤ ≤ g ⁻¹ᵁ W) (hl : ⊤ ≤ g ⁻¹ᵁ H.U l) :
    (g.appLE _ ⊤ hl).hom (s.f l) = (g.appLE _ ⊤ h).hom r * (g.appLE _ ⊤ hl).hom (t.f l) := by
  have h' : ⊤ ≤ g ⁻¹ᵁ (W ⊓ H.U l) := le_inf h hl
  have := congrArg (g.appLE _ ⊤ h').hom (hr l)
  rwa [map_mul, ap_res g _ h' hl, ap_res g _ h' hl, ap_res g _ h' h] at this

theorem hasWt_ratio {d : ℕ} {φ ψ : (Φ.H d).Sec} {α : Φ.E.X} (hφ : Φ.Pure α φ) (hψ : Φ.Pure 0 ψ)
    {W : Φ.G.left.Opens} (hW : W ≤ nonzeroLocus ψ) {r : Γ(Φ.G.left, W)} (hr : IsRatio φ ψ W r) :
    HasWt Φ.D.i W r α := by
  refine hasWt_of_cover Φ.D.i (Φ.H d).U (Φ.H_isLB d).cover fun l Y t g h h' hl => ?_
  have hl' := TorusTranslate.translate_le Φ.D t g (Φ.N₀.U l) hl
  have e₁ := TorusTranslate.translate_pure Φ.D t g (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α (φ.f l)
    (fun β hβ => wt_eq_zero Φ hφ hβ l) hl hl'
  have e₂ := TorusTranslate.translate_pure Φ.D t g (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) 0 (ψ.f l)
    (fun β hβ => wt_eq_zero Φ hψ hβ l) hl hl'
  rw [charUnit_zero_val, map_one, _root_.one_mul] at e₂
  have e₃ := ap_ratio hr g.left l h hl
  have e₄ := ap_ratio hr ((t ≫ Φ.D.i) * g).left l h' hl'
  have hu : IsUnit ((g.left.appLE _ ⊤ hl).hom (ψ.f l)) := by
    have h' : ⊤ ≤ g.left ⁻¹ᵁ (W ⊓ (Φ.H d).U l) := le_inf h hl
    have := (SecRatio.isUnit_res ψ l (inf_le_left.trans hW) (inf_le_right : W ⊓ (Φ.H d).U l ≤ _)).map
      (g.left.appLE _ ⊤ h').hom
    rwa [ap_res g.left _ h' hl] at this
  apply hu.mul_right_cancel
  exact (congrArg _ e₂.symm).trans (e₄.symm.trans (e₁.trans ((congrArg _ e₃).trans (_root_.mul_assoc _ _ _).symm)))

theorem exists_app_eq {V : Φ.E.B.left.Opens} {u : Γ(Φ.G.left, Φ.D.q.left ⁻¹ᵁ V)}
    (hu : HasWt Φ.D.i _ u 0) : ∃ a, (Φ.D.q.left.app V).hom a = u := by
  have := Φ.D.q_affine
  refine (invariant_functions_descend _ _ _ _ Φ.D.q Φ.D.i Φ.D.q_hom Φ.D.i_hom Φ.D.q_flat Φ.D.q_surjective
    inferInstance Φ.D.isKernel V).2.2 u fun Z t g h₁ h₂ => ?_
  rw [hu Z t g h₂ h₁, charUnit_zero_val, map_one, _root_.one_mul]

section Change
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X X' : Type} [AddCommGroup X] [AddCommGroup X']
  {i : splitTorus S X ⟶ H} {V : H.left.Opens}
open SplitTorusPow

theorem stable_map (f : X →+ X') (h : Stable i V) : Stable (torusMap S f ≫ i) V := by
  intro Y t g hg
  rw [← Category.assoc]
  exact h Y _ g hg

theorem hasWt_map (f : X →+ X') {u : Γ(H.left, V)} {χ : X} (h : HasWt i V u χ) :
    HasWt (torusMap S f ≫ i) V u (f χ) := by
  intro Y t g h₁ h₂
  have := h Y (t ≫ torusMap S f) g h₁ (by rwa [Category.assoc])
  rw [Over.comp_left, FunDescent.comp_appTop_apply, torusMap_char] at this
  rw [← this]
  simp only [Category.assoc]

theorem torusMap_comp_symm (f : X ≃+ X') :
    torusMap S f.symm.toAddMonoidHom ≫ torusMap S f.toAddMonoidHom = 𝟙 _ := by
  apply (splitTorusPointsEquiv S X _).injective
  rw [points_comp_torusMap, ← Category.id_comp (torusMap S f.symm.toAddMonoidHom), points_comp_torusMap]
  ext x
  simp

end Change

theorem isRatio_app {s t : Φ.N₀.Sec} {s' t' : (Φ.H 1).Sec}
    (hs : ∀ l, s'.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (s.f l))
    (ht : ∀ l, t'.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l)) {V : Φ.E.B.left.Opens} {r : Γ(Φ.E.B.left, V)}
    (hr : IsRatio s t V r) : IsRatio s' t' (Φ.D.q.left ⁻¹ᵁ V) ((Φ.D.q.left.app V).hom r) := by
  intro l
  have := congrArg (Φ.D.q.left.app _).hom (hr l)
  rw [map_mul, ← WtPart.rapp, ← WtPart.rapp, ← WtPart.rapp] at this
  rw [hs, ht]
  exact this

theorem gen {I : Type} {s : I → Φ.N₀.Sec} (hs : ImmBy Φ.E.B.hom Φ.N₀ s Set.univ) {s' : I → (Φ.H 1).Sec}
    (hf : ∀ i l, (s' i).f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom ((s i).f l)) (a : I)
    {W : Φ.G.left.Opens} (hW : W = Φ.D.q.left ⁻¹ᵁ nonzeroLocus (s a)) (hW' : W ≤ nonzeroLocus (s' a))
    {r : I → Γ(Φ.G.left, W)} (hr : ∀ j, IsRatio (s' j) (s' a) W (r j)) {u : Γ(Φ.G.left, W)}
    (hu : HasWt Φ.D.i W u 0) :
    u ∈ Subring.closure (Set.range (Φ.G.hom.appLE ⊤ W le_top).hom ∪ Set.range r) := by
  subst hW
  obtain ⟨v, rfl⟩ := exists_app_eq Φ hu
  obtain ⟨-, r₀, hr₀, hc⟩ := hs.2 a trivial
  have hv : v ∈ Subring.closure _ := hc.ge trivial
  refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ hv)
  rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
  · refine Subring.subset_closure (Or.inl ?_)
    rw [app_constFn]
    exact ⟨_, rfl⟩
  · refine Subring.subset_closure (Or.inr ⟨j, ?_⟩)
    exact (SecRatio.existsUnique_isRatio (Φ.H_isLB 1) _ _ _ hW').unique (hr j)
      (isRatio_app Φ (hf j) (hf a) (hr₀ j))

theorem exists_mem_of_isLin {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X} {I : Type}
    [Fintype I] {F : I → H.Sec} {b : I → k} {φ : H.Sec} (h : IsLin p F b φ) {x : X} (hx : x ∈ nonzeroLocus φ) :
    ∃ i, x ∈ nonzeroLocus (F i) := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hl' : x ∈ H.U l := X.basicOpen_le _ hl
  by_contra hn
  have h1 := (Scheme.mem_basicOpen X _ x hl').1 hl
  rw [h l, map_sum] at h1
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun i _ => ?_) h1
  rw [map_mul]
  refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => hn ⟨i, ?_⟩)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, (Scheme.mem_basicOpen X _ x hl').2 hu⟩

theorem mem_basicOpen_ratio {X : Scheme.{0}} {H : LB X} {s t : H.Sec} {W : X.Opens} {r : Γ(X, W)}
    (hr : IsRatio s t W r) {x : X} (hx : x ∈ W) (hs : x ∈ nonzeroLocus s) : x ∈ X.basicOpen r := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  have e := congrArg X.basicOpen (hr l)
  rw [Scheme.basicOpen_mul] at e
  erw [X.basicOpen_res (s.f l) (homOfLE _).op, X.basicOpen_res r (homOfLE _).op] at e
  exact (e.le ⟨⟨hx, X.basicOpen_le _ hl⟩, hl⟩).1.2

theorem eq_top_of_points [IsAlgClosed k] (U : Φ.G.left.Opens) (h : ∀ x : Φ.Pt, ⊤ ≤ x.left ⁻¹ᵁ U) : U = ⊤ := by
  have hG := isSemiAbelian_of_isGt _ Φ.E Φ.G ⟨Φ.D⟩
  have := hG.smooth
  have := hG.quasiCompact
  have : CompactSpace Φ.G.left := QuasiCompact.compactSpace_of_compactSpace Φ.G.hom
  by_contra hne
  have hn : ((U : Set Φ.G.left)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact fun e => hne (TopologicalSpace.Opens.ext e)
  obtain ⟨x, hxU, hx⟩ := U.isOpen.isClosed_compl.exists_closed_singleton hn
  have h0 := h (Over.homMk (pointOfClosedPoint (K := k) Φ.G.hom x hx) (pointOfClosedPoint_comp (K := k) Φ.G.hom x hx))
  have : pointOfClosedPoint (K := k) Φ.G.hom x hx (IsLocalRing.closedPoint k) ∈ U :=
    h0 (x := IsLocalRing.closedPoint k) trivial
  exact hxU ((pointOfClosedPoint_apply (K := k) Φ.G.hom x hx (IsLocalRing.closedPoint k)) ▸ this)

theorem exists_split : Out.Laws → Out.Laws2 → ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F F' : J → (Φ.H 1).Sec) (π : Φ.Pol N) (m : Matrix J J k) (Ch : GlobalTheory.ZJ.Charts Φ.G.left) (e : Ch.I ≃ J) (cl : Φ.E.X → Ch.Cl), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → IsUnit m.det → (∀ i, IsLin Φ.G.hom F (m i) (F' i)) → (∀ α β, cl α = cl β ↔ ∃ n, α = β + N • n) → cl 0 = Ch.c₀ → (∀ i j, m (e i) j ≠ 0 → Ch.wt i = cl (cls j)) → (∀ i, Ch.W i = nonzeroLocus (F' (e i.1)) ∧ ∀ j, IsRatio (F' (e j)) (F' (e i.1)) (Ch.W i) (Ch.r i j)) → ∃ c : Fin (Module.finrank ℤ Φ.E.X) → Ch.Cl, GlobalTheory.ZJ.Charts.Split (H := Φ.G) Ch c := by
  intro hL hL2 k _ _ Φ g N N' q J _ cls F F' π m Ch e cl hB hG hg hm hlin hcl hc₀ hwt hW
  have : Fintype Ch.I := Fintype.ofFinite _
  obtain ⟨b, hb, -⟩ := exists_basis_unique_min_and_sums_separated Φ.E.X q hG.pos _ g N N' _ rfl (by omega)
    hB.lll hB.sep
  have h0 : OnlyShort q N 0 := onlyShort_zero hG.pos (by have := hB.four; omega)
  have hb' : ∀ n, OnlyShort q N (b n) := fun n x hx => (hb n x hx).1
  have pure : ∀ α, OnlyShort q N α → ∀ i, Ch.wt i = cl α → Φ.Pure α (F' (e i)) := fun α hα i hi =>
    pure_lin Φ (hlin _) fun j hj => pure_of_cls hG hα ((hcl _ _).1 (hi.symm.trans (hwt i j hj)))
  have span : ∀ α, OnlyShort q N α → ∀ c, cl α = c → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ →
      ∃ a : {i // Ch.wt i = c} → k, IsLin Φ.G.hom (fun i : {i // Ch.wt i = c} => F' (e i.1)) a φ := by
    intro α hα c hc φ hφ
    obtain ⟨a, ha, hl⟩ := exists_isLin hG hα hφ
    obtain ⟨a', ha'⟩ := block m hm e Ch.wt (fun j => cl (cls j)) hwt c a
      fun j hj => ((hcl _ _).2 (ha j hj)).symm.trans hc
    exact ⟨a', isLin_comp (F := F) (m := fun (i : {i // Ch.wt i = c}) j => m (e i.1) j) (fun i => hlin (e i.1)) ha' hl⟩
  have pure0 : ∀ i : {i // Ch.wt i = Ch.c₀}, Φ.Pure 0 (F' (e i.1)) := fun i => pure 0 h0 _ (i.2.trans hc₀.symm)
  choose s hs₁ hs₂ hs₃ using fun i => (FibPre.pure_zero k Φ).2 _ (pure0 i)
  have hs : ImmBy Φ.E.B.hom Φ.N₀ s Set.univ := by
    obtain ⟨n, t, ht⟩ := GlobalTheory.T.exists_closedImmersion_abelianPart_bundle hL hL2 k Φ N hB.four π
    have := Φ.E.isAbelian.proper
    refine SpanImm.immBy_of_span k _ _ _ Φ.isLB _ _ t s ht fun i => ?_
    obtain ⟨φ, hφ, hw⟩ := (FibPre.pure_zero k Φ).1 (t i)
    obtain ⟨a, ha⟩ := span 0 h0 _ hc₀ φ hφ
    refine ⟨a, fun l => ?_⟩
    rw [← hw, wt_lin Φ ha]
    simp only [hs₁]
  let f : Φ.E.X ≃+ (Fin (Module.finrank ℤ Φ.E.X) → ℤ) := b.equivFun.toAddEquiv
  have hf : ∀ n, f.toAddMonoidHom (b n) = Pi.single n 1 := fun n => by
    ext n'
    simp [f, Pi.single_apply, Finsupp.single_apply, eq_comm]
  have := Φ.D.i_hom
  have := SplitTorusPow.isMonHom_torusMap (S := Sp k) f.toAddMonoidHom
  refine ⟨fun n => cl (b n), (isSemiAbelian_of_isGt _ Φ.E Φ.G ⟨Φ.D⟩).geomConnected,
    SplitTorusPow.torusMap (Sp k) f.toAddMonoidHom ≫ Φ.D.i, inferInstance, fun a => ?_, fun a j hj => ?_,
    fun a j n hj => ?_, fun n x => ?_, fun a u hu => ?_⟩
  · refine stable_map _ ?_
    rw [(hW a).1, hs₃]
    exact fun Y t g => TorusTranslate.translate_le Φ.D t g _
  · have := hasWt_map f.toAddMonoidHom (hasWt_ratio Φ (pure0 ⟨j, hj⟩) (pure0 a) (hW a).1.le ((hW a).2 j))
    rwa [map_zero] at this
  · have := hasWt_map f.toAddMonoidHom (hasWt_ratio Φ (pure _ (hb' n) j hj) (pure0 a) (hW a).1.le ((hW a).2 j))
    rwa [hf] at this
  · have hU := eq_top_of_points Φ (⨆ j : {i // Ch.wt i = cl (b n)}, nonzeroLocus (F' (e j.1))) fun y => by
      obtain ⟨φ, hφ, hy⟩ := GlobalTheory.T.exists_pureWeight_section_ne_zero_at hL hL2 k Φ N hB.four π (b n) y
      obtain ⟨a, ha⟩ := span _ (hb' n) _ rfl φ hφ
      exact fun z hz => TopologicalSpace.Opens.mem_iSup.2 (exists_mem_of_isLin ha (hy hz))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU.ge (show x ∈ ⊤ from trivial))
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (Ch.cover.ge (show x ∈ ⊤ from trivial))
    exact ⟨a, j.1, j.2, mem_basicOpen_ratio ((hW a).2 j.1) ha hj⟩
  · have hu' := hasWt_map f.symm.toAddMonoidHom hu
    rw [← Category.assoc, torusMap_comp_symm, Category.id_comp, map_zero] at hu'
    refine Subring.closure_mono (Set.union_subset_union_right _ ?_)
      (gen Φ hs hs₂ a ((hW a).1.trans (hs₃ a)) (hW a).1.le (r := fun j => Ch.r a j.1) (fun j => (hW a).2 j.1) hu')
    rintro _ ⟨j, rfl⟩
    exact ⟨j.1, j.2, rfl⟩

end GlobalTheory.ZH.FibTorus
end
