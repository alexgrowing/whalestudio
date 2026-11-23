import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

noncomputable section

namespace GlobalTheory

section Geometry

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {σ : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G σ φ)

def adjPair2 {T : Over S'} (a b : T ⟶ G') : T.left ⟶ (G ⊗ G).left := (lift (pushHom gp T a) (pushHom gp T b)).left

def adjPair3 {T : Over S'} (a b c : T ⟶ G') : T.left ⟶ (G3 G).left :=
  (lift (pushHom gp T a) (lift (pushHom gp T b) (pushHom gp T c))).left

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem adjPair3_comp {T T' : Over S'} (r : T' ⟶ T) (a b c : T ⟶ G') :
    r.left ≫ adjPair3 gp a b c = adjPair3 gp (r ≫ a) (r ≫ b) (r ≫ c) := by
  let U : Over.mk (T'.hom ≫ σ) ⟶ Over.mk (T.hom ≫ σ) := Over.homMk r.left (by
    show r.left ≫ T.hom ≫ σ = T'.hom ≫ σ
    rw [← Category.assoc, Over.w r])
  have e : ∀ a : T ⟶ G', U ≫ pushHom gp T a = pushHom gp T' (r ≫ a) := fun a =>
    Over.OverMorphism.ext (Category.assoc r.left a.left φ).symm
  show (U ≫ lift (pushHom gp T a) (lift (pushHom gp T b) (pushHom gp T c))).left = _
  rw [comp_lift, comp_lift, e, e, e]; rfl

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem adjPair3_eq {Z : Scheme.{0}} {k : Z ⟶ S'} {h : Z ⟶ S} (hh : h = k ≫ σ) (a b c : Over.mk k ⟶ G')
    (A B C : Over.mk h ⟶ G) (ha : A.left = a.left ≫ φ) (hb : B.left = b.left ≫ φ) (hc : C.left = c.left ≫ φ) :
    (lift A (lift B C)).left = adjPair3 gp a b c := by
  subst hh
  obtain rfl : A = pushHom gp (Over.mk k) a := Over.OverMorphism.ext ha
  obtain rfl : B = pushHom gp (Over.mk k) b := Over.OverMorphism.ext hb
  obtain rfl : C = pushHom gp (Over.mk k) c := Over.OverMorphism.ext hc
  rfl

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem adjPair2_eq {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (sq : IsSquare φ φ₂) {T : Over S'} (a b : T ⟶ G') :
    (lift a b).left ≫ φ₂ = adjPair2 gp a b := by
  refine pullback.hom_ext (f := G.hom) (g := G.hom) ?_ ?_
  · have e₁ : (lift a b).left ≫ (fst G' G').left = a.left := congrArg (fun q => q.left) (lift_fst a b)
    have e₂ : adjPair2 gp a b ≫ (fst G G).left = a.left ≫ φ :=
      congrArg (fun q => q.left) (lift_fst (pushHom gp T a) (pushHom gp T b))
    show ((lift a b).left ≫ φ₂) ≫ (fst G G).left = adjPair2 gp a b ≫ (fst G G).left
    rw [e₂, Category.assoc, sq.1, ← Category.assoc, e₁]
  · have e₁ : (lift a b).left ≫ (snd G' G').left = b.left := congrArg (fun q => q.left) (lift_snd a b)
    have e₂ : adjPair2 gp a b ≫ (snd G G).left = b.left ≫ φ :=
      congrArg (fun q => q.left) (lift_snd (pushHom gp T a) (pushHom gp T b))
    show ((lift a b).left ≫ φ₂) ≫ (snd G G).left = adjPair2 gp a b ≫ (snd G G).left
    rw [e₂, Category.assoc, sq.2, ← Category.assoc, e₁]

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem grpPullback_square_product_lift {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (sq : IsSquare φ φ₂) (f f' : G' ⟶ G') {T : Over S'}
    (a b : T ⟶ G') {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ i : Fin 2, h ((lift a b).left ≫ ![(lift (fst G' G' ≫ f) (snd G' G')).left ≫ φ₂,
      (lift (fst G' G') (snd G' G' ≫ f')).left ≫ φ₂] i) ^ (![1, -1] : Fin 2 → ℤ) i =
      h (adjPair2 gp (a ≫ f) b) * (h (adjPair2 gp a (b ≫ f')))⁻¹ := by
  have e₀ : lift a b ≫ lift (fst G' G' ≫ f) (snd G' G') = lift (a ≫ f) b := by simp [comp_lift]
  have e₁ : lift a b ≫ lift (fst G' G') (snd G' G' ≫ f') = lift a (b ≫ f') := by simp [comp_lift]
  rw [Fin.prod_univ_two, ← adjPair2_eq gp sq, ← adjPair2_eq gp sq, ← e₀, ← e₁, Over.comp_left, Over.comp_left,
    Category.assoc, Category.assoc]
  show _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) = _
  rw [zpow_one, zpow_neg_one]; rfl

theorem adjProd_ulift {U : Type} [CommGroup U] (g : ULift.{0} (Fin 3) → U) :
    ∏ i, g i ^ lawε i = g ⟨0⟩ * (g ⟨1⟩)⁻¹ * (g ⟨2⟩)⁻¹ := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _ (fun i => g ⟨i⟩ ^ lawε ⟨i⟩)
    (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (-1 : ℤ) = _
  rw [zpow_one, zpow_neg_one, zpow_neg_one]

omit [IsCommMonObj G'] in
theorem grpPullback_prod_firstLaw_pow {T : Over S'} (a b c : T ⟶ G') {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ i, h (adjPair3 gp a b c ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) i) ^ lawε i =
      h (adjPair2 gp (a * b) c) * (h (adjPair2 gp a c))⁻¹ * (h (adjPair2 gp b c))⁻¹ := by
  rw [adjProd_ulift, adjPair2, adjPair2, adjPair2, map_mul, adjPair3]
  generalize pushHom gp T a = A
  generalize pushHom gp T b = B
  generalize pushHom gp T c = C
  have e₀ : lift A (lift B C) ≫ lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2) = lift (A * B) C := by
    rw [comp_lift]
    congr 1
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
    · simp [x3]
  have e₁ : lift A (lift B C) ≫ lift (x3 G 0) (x3 G 2) = lift A C := by simp [x3, comp_lift]
  have e₂ : lift A (lift B C) ≫ lift (x3 G 1) (x3 G 2) = lift B C := by simp [x3, comp_lift]
  rw [← e₀, ← e₁]
  exact congrArg₂ (· * ·) rfl (congrArg (fun q => (h q.left)⁻¹) e₂)

omit [IsCommMonObj G'] in
theorem grpPullback_prod_secondLaw_pow {T : Over S'} (a b c : T ⟶ G') {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ i, h (adjPair3 gp a b c ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) i) ^ lawε i =
      h (adjPair2 gp a (b * c)) * (h (adjPair2 gp a b))⁻¹ * (h (adjPair2 gp a c))⁻¹ := by
  rw [adjProd_ulift, adjPair2, adjPair2, adjPair2, map_mul, adjPair3]
  generalize pushHom gp T a = A
  generalize pushHom gp T b = B
  generalize pushHom gp T c = C
  have e₀ : lift A (lift B C) ≫ lift (x3 G 0) (padd G (x3 G 1) (x3 G 2)) = lift A (B * C) := by
    rw [comp_lift]
    congr 1
    · simp [x3]
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
  have e₁ : lift A (lift B C) ≫ lift (x3 G 0) (x3 G 1) = lift A B := by simp [x3, comp_lift]
  have e₂ : lift A (lift B C) ≫ lift (x3 G 0) (x3 G 2) = lift A C := by simp [x3, comp_lift]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (fun q => h q.left) e₀) (congrArg (fun q => (h q.left)⁻¹) e₁))
    (congrArg (fun q => (h q.left)⁻¹) e₂)

theorem adjCompare (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') {P : LB (G ⊗ G).left} (hP : P.IsLB)
    {K L : Type} [Fintype K] [Fintype L] {τ : K → ((G' ⊗ G').left ⟶ (G ⊗ G).left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb P τ ε)) (ht : t.IsGen) {ω : L → ((G3 G).left ⟶ (G ⊗ G).left)} {δ : L → ℤ}
    (w : LB.Gen (LB.LinComb P ω δ)) (hw : w.IsGen) (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ : G3 G' ⟶ G')
    (hF : ∀ (U : Type) [CommGroup U] (h : ((G3 G').left ⟶ (G ⊗ G).left) → U),
      (∏ i, h (adjPair3 gp l₁ l₂ l₃ ≫ ω i) ^ δ i) * ((∏ i, h ((lift a₁ b₁).left ≫ τ i) ^ ε i) *
        (∏ i, h ((lift a₂ b₂).left ≫ τ i) ^ ε i)) =
      (∏ i, h (adjPair3 gp k₁ k₂ k₃ ≫ ω i) ^ δ i) * ((∏ i, h ((lift a b).left ≫ τ i) ^ ε i) *
        (∏ i, h ((lift (1 : G3 G' ⟶ G') (1 : G3 G' ⟶ G')).left ≫ τ i) ^ ε i)))
    (h0 : ∀ q ∈ [a, b, a₁, b₁, a₂, b₂, k₁, k₂, k₃, l₁, l₂, l₃],
      (lift 1 (lift 1 1) : 𝟙_ (Over S') ⟶ G3 G') ≫ q = 1)
    {T : Over S'} (ρ : T ⟶ G3 G') {z : T.left} {J} (hJ : Good P z J) :
    val w (adjPair3 gp (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃)) z J * (val t (lift (ρ ≫ a) (ρ ≫ b)).left z J *
      val t (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J) =
    val w (adjPair3 gp (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃)) z J * (val t (lift (ρ ≫ a₁) (ρ ≫ b₁)).left z J *
      val t (lift (ρ ≫ a₂) (ρ ≫ b₂)).left z J) := by
  let e : 𝟙_ (Over S') ⟶ G3 G' := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have ev : ∀ (a₁ b₁ a₂ b₂ l₁ l₂ l₃ : G3 G' ⟶ G') {T' : Over S'} (r : T' ⟶ G3 G') {z : T'.left} {J}, Good P z J →
      val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ w (adjPair3 gp l₁ l₂ l₃))
        (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ t (lift a₁ b₁).left) (LB.pullGen P _ _ t (lift a₂ b₂).left))) r.left z J =
      val w (adjPair3 gp (r ≫ l₁) (r ≫ l₂) (r ≫ l₃)) z J * (val t (lift (r ≫ a₁) (r ≫ b₁)).left z J *
        val t (lift (r ≫ a₂) (r ≫ b₂)).left z J) := fun a₁ b₁ a₂ b₂ l₁ l₂ l₃ T' r z J hJ => by
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, adjPair3_comp, ← Over.comp_left,
      ← Over.comp_left, comp_lift, comp_lift]
  have gn : ∀ (a₁ b₁ a₂ b₂ l₁ l₂ l₃ : G3 G' ⟶ G'), (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ w (adjPair3 gp l₁ l₂ l₃))
      (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ t (lift a₁ b₁).left) (LB.pullGen P _ _ t (lift a₂ b₂).left))).IsGen :=
    fun _ _ _ _ _ _ _ => DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hw _)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
  have key := gen_unique' hP (fun V _ k => ?_) _ e.left he sj (gn a b 1 1 k₁ k₂ k₃) (gn a₁ b₁ a₂ b₂ l₁ l₂ l₃)
    (fun y I hI => ?_) _ ρ.left z J hJ
  · rwa [ev _ _ _ _ _ _ _ ρ hJ, ev _ _ _ _ _ _ _ ρ hJ, MonObj.comp_one] at key
  · simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact hF V k
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h0
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h0
    refine (ev _ _ _ _ _ _ _ e hI).trans (Eq.trans ?_ (ev _ _ _ _ _ _ _ e hI).symm)
    simp only [e]
    rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, MonObj.comp_one]

theorem adjAdd (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') {P : LB (G ⊗ G).left} (β : IsBiext G P)
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (sq : IsSquare φ φ₂) (f f' : G' ⟶ G') [IsMonHom f] [IsMonHom f']
    (t : LB.Gen (LB.LinComb P (K := Fin 2) ![(lift (fst G' G' ≫ f) (snd G' G')).left ≫ φ₂,
      (lift (fst G' G') (snd G' G' ≫ f')).left ≫ φ₂] ![1, -1])) (ht : t.IsGen)
    {T : Over S'} (x x' y : T ⟶ G') {z : T.left} {J} (hJ : Good P z J) :
    val β.law1 (adjPair3 gp x x' (y ≫ f')) z J * (val t (lift (x * x') y).left z J *
        val t (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J) =
      val β.law1 (adjPair3 gp (x ≫ f) (x' ≫ f) y) z J * (val t (lift x y).left z J * val t (lift x' y).left z J) ∧
    val β.law2 (adjPair3 gp y (x ≫ f') (x' ≫ f')) z J * (val t (lift y (x * x')).left z J *
        val t (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J) =
      val β.law2 (adjPair3 gp (y ≫ f) x x') z J * (val t (lift y x).left z J * val t (lift y x').left z J) := by
  let p₀ := x3 G' 0
  let p₁ := x3 G' 1
  let p₂ := x3 G' 2
  let e : 𝟙_ (Over S') ⟶ G3 G' := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have of : ∀ q : G3 G' ⟶ G', e ≫ q = 1 → e ≫ q ≫ f = 1 := fun q hq => by rw [← Category.assoc, hq, MonObj.one_comp]
  have of' : ∀ q : G3 G' ⟶ G', e ≫ q = 1 → e ≫ q ≫ f' = 1 := fun q hq => by rw [← Category.assoc, hq, MonObj.one_comp]
  let ρ : T ⟶ G3 G' := lift x (lift x' y)
  have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  constructor
  · have := adjCompare gp hG hA β.isLB t ht β.law1 β.isGen1 (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ (p₂ ≫ f') (p₀ ≫ f) (p₁ ≫ f) p₂
      (fun V _ k => by
        rw [grpPullback_prod_firstLaw_pow, grpPullback_prod_firstLaw_pow, grpPullback_square_product_lift gp sq, grpPullback_square_product_lift gp sq, grpPullback_square_product_lift gp sq, grpPullback_square_product_lift gp sq,
          MonObj.one_comp, MonObj.one_comp, MonObj.mul_comp]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨o₁, e₂, e₀, e₂, e₁, e₂, e₀, e₁, of' _ e₂, of _ e₀, of _ e₁, e₂⟩) ρ hJ
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this
  · have := adjCompare gp hG hA β.isLB t ht β.law2 β.isGen2 p₂ (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ (p₀ ≫ f') (p₁ ≫ f') (p₂ ≫ f) p₀ p₁
      (fun V _ k => by
        rw [grpPullback_prod_secondLaw_pow, grpPullback_prod_secondLaw_pow, grpPullback_square_product_lift gp sq, grpPullback_square_product_lift gp sq, grpPullback_square_product_lift gp sq, grpPullback_square_product_lift gp sq,
          MonObj.one_comp, MonObj.one_comp, MonObj.mul_comp]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨e₂, o₁, e₂, e₀, e₂, e₁, e₂, of' _ e₀, of' _ e₁, of _ e₂, e₀, e₁⟩) ρ hJ
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this

omit [IsCommMonObj G] [IsCommMonObj G'] in
include gp in

theorem adjPoints {X : Scheme.{0}} (a : X ⟶ S') (b : X ⟶ S) (hb : b = a ≫ σ) :
    ∃ e : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  subst hb
  let ρ : (Over.mk a ⟶ G') →* (Over.mk (a ≫ σ) ⟶ G) := pushHom gp (Over.mk a)
  have hρ : ∀ x, (ρ x).left = x.left ≫ φ := fun _ => rfl
  refine ⟨MulEquiv.ofBijective ρ ⟨fun x y hxy => ?_, fun y => ?_⟩, hρ⟩
  · refine Over.OverMorphism.ext (gp.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    exact (hρ x).symm.trans ((congrArg (fun z => z.left) hxy).trans (hρ y))
  · exact ⟨Over.homMk (gp.1.lift y.left a (Over.w y)) (gp.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hρ _).trans (gp.1.lift_fst _ _ _))⟩

end Geometry

section Main

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem adjBase {R₀ : Type} [CommRing R₀] {O R : LAlg R₀} (s : LHom O R) :
    Spec.map (CommRingCat.ofHom (algebraMap R₀ (R : Type))) =
      Spec.map (CommRingCat.ofHom s.1.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type))) :=
  (Over.w (spMap s.1)).symm

theorem adjEnd {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] (B : BX R₀)
    (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)) (hb : ∀ R, Function.Bijective (e R))
    (hm : ∀ R x y, e R (x + y) = e R x * e R y)
    (hn : ∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)
    (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] (φ : G'.left ⟶ G.left)
    (gp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ)
    (f : G' ⟶ G') [IsMonHom f] : ∃ a : OEnd B O, ∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (a.f s x)).left := by
  choose E hE using fun (R : LAlg R₀) (s : LHom O R) => adjPoints gp _ _ (adjBase s)
  choose F hF using fun (R : LAlg R₀) (s : LHom O R) (x : B.G R) => (hb R).2 (E R s ((E R s).symm (e R x) ≫ f))
  have spec : ∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (F R s x)).left := fun {R} s x x' h => by
    have : e R x = E R s x' := Over.OverMorphism.ext (h.symm.trans (hE R s x').symm)
    rw [hF, this, MulEquiv.symm_apply_apply, hE]
  refine ⟨⟨fun {R} s => AddMonoidHom.mk' (F R s) fun x y => (hb R).1 ?_, fun {R S} s g x => (hb S).1 ?_⟩, spec⟩
  · rw [hm, hF, hF, hF, hm]
    exact (congrArg (fun q => E R s (q ≫ f)) (map_mul (E R s).symm _ _)).trans
      ((congrArg (E R s) (MonObj.mul_comp _ _ _)).trans (map_mul (E R s) _ _))
  · let x' := (E R s).symm (e R x)
    have hx : x'.left ≫ φ = (e R x).left :=
      (hE R s x').symm.trans (congrArg (fun q => q.left) ((E R s).apply_symm_apply _))
    let U : Over.mk (Spec.map (CommRingCat.ofHom (g.comp s).1.toRingHom)) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) :=
      Over.homMk (Spec.map (CommRingCat.ofHom g.1.toRingHom)) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp]; rfl)
    have h₁ := spec (g.comp s) (B.map g x) (U ≫ x') (by
      rw [hn]
      exact (Category.assoc _ _ _).trans (congrArg (U.left ≫ ·) hx))
    refine Over.OverMorphism.ext (h₁.symm.trans ?_)
    show _ = (e S (B.map g (F R s x))).left
    rw [hn, Category.assoc]
    exact (Category.assoc _ _ _).trans (congrArg (U.left ≫ ·) (spec s x x' hx))

theorem exists_oAdj_of_rosatiAdjoint :
  (∀ {R₀ : Type} [CommRing R₀] (B : BX R₀) (b : ∀ R x y, B.P R x y) (t₁ t₂ : ∀ R : LAlg R₀, B.G R → B.G R → B.G R → (R : Type)ˣ),
    (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R x x' y) (b R (x + x') y)) →
    (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R x y y') (b R x (y + y'))) →
    (∀ R (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ), B.IsPairing (N + 1) x y z ↔ (N + 1) • x = 0 ∧ (N + 1) • y = 0 ∧
      z = (t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) / (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) ∧
    ∀ (O : LAlg R₀) (a a' : OEnd B O) (u : ∀ {R : LAlg R₀}, LHom O R → B.G R → B.G R → (R : Type)ˣ),
      (∀ {R : LAlg R₀} (s : LHom O R) x x' y, u s (x + x') y * t₁ R x x' (a'.f s y) = t₁ R (a.f s x) (a.f s x') y * (u s x y * u s x' y)) →
      (∀ {R : LAlg R₀} (s : LHom O R) x y y', u s x (y + y') * t₂ R x (a'.f s y) (a'.f s y') = t₂ R (a.f s x) y y' * (u s x y * u s x y')) →
      ∃ A : OAdj B O, A.a = a ∧ A.ab = a') →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) →
  (ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)) (b : ∀ R x y, B.P R x y)
    (J : ∀ R : LAlg R₀, ((sp (R₀ := R₀) (R : Type)).left ⟶ (G ⊗ G).left) → P.1),
    (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    (∀ R : LAlg R₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P (Z := (sp (R₀ := R₀) (R : Type)).left) (IsLocalRing.closedPoint (R : Type)) (J R)) →
    (∀ (R : LAlg R₀) x x' y, B.add1 (b R x y) (b R x' y) =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (e R x) (lift (e R x') (e R y))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R (x + x') y)) →
    (∀ (R : LAlg R₀) x y y', B.add2 (b R x y) (b R x y') =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift (e R x) (lift (e R y) (e R y'))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R x (y + y'))) →
    ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left),
    ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme G' → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂ →
    ∀ (f f' : G' ⟶ G') [IsMonHom f] [IsMonHom f'], (∃ t : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2)
      ![(lift (fst G' G' ≫ f) (snd G' G')).left ≫ φ₂, (lift (fst G' G') (snd G' G' ≫ f')).left ≫ φ₂] ![1, -1]), t.IsGen) →
    ∃ A : OAdj B O, (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.a.f s x)).left) ∧
      (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ f').left ≫ φ = (e R (A.ab.f s x)).left)) := by
  intro FRM _ hG R₀ _ G _ _ P β B e b J hb hm hn hJ h1 h2 O G' _ _ φ φ₂ hA gp sq f f' _ _ ⟨t, ht⟩
  obtain ⟨a, ha⟩ := adjEnd G B e hb hm hn O G' φ gp f
  obtain ⟨a', ha'⟩ := adjEnd G B e hb hm hn O G' φ gp f'
  choose E hE using fun (R : LAlg R₀) (s : LHom O R) => adjPoints gp _ _ (adjBase s)
  let l := fun (R : LAlg R₀) (s : LHom O R) (x : B.G R) => (E R s).symm (e R x)
  have hl : ∀ R s x, (e R x).left = (l R s x).left ≫ φ := fun R s x =>
    (congrArg (fun q => q.left) ((E R s).apply_symm_apply _)).symm.trans (hE R s _)
  have lm : ∀ R s x y, l R s (x + y) = l R s x * l R s y := fun R s x y =>
    (congrArg (E R s).symm (hm R x y)).trans (map_mul (E R s).symm _ _)
  let v := fun (R : LAlg R₀) (s : LHom O R) (x y : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G') =>
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (Z := (sp (R₀ := R₀) (R : Type)).left) t (lift x y).left
      (IsLocalRing.closedPoint (R : Type)) (J R)
  refine Exists.elim ((FRM B b _ _ h1 h2).2 O a a'
    (fun {R} s x y => Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom
      (v R s (l R s x) (l R s y) * (v R s 1 1)⁻¹)) (fun {R} s x x' y => ?_) (fun {R} s x y y' => ?_)) fun A hA' => ?_
  rotate_left 2
  · obtain ⟨rfl, rfl⟩ := hA'
    exact ⟨A, ha, ha'⟩
  · have k := (adjAdd gp hG hA β sq f f' t ht (l R s x) (l R s x') (l R s y) (hJ R)).1
    rw [← adjPair3_eq gp (adjBase s) _ _ _ _ _ _ (hl R s x) (hl R s x') (ha' s y _ (hl R s y).symm).symm,
      ← adjPair3_eq gp (adjBase s) _ _ _ _ _ _ (ha s x _ (hl R s x).symm).symm (ha s x' _ (hl R s x').symm).symm
        (hl R s y), ← lm] at k
    rw [← map_mul, ← map_mul, ← map_mul]
    refine congrArg _ ?_
    have k' := congrArg Additive.ofMul k
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, v] at k' ⊢
    linear_combination (norm := abel) k'
  · have k := (adjAdd gp hG hA β sq f f' t ht (l R s y) (l R s y') (l R s x) (hJ R)).2
    rw [← adjPair3_eq gp (adjBase s) _ _ _ _ _ _ (hl R s x) (ha' s y _ (hl R s y).symm).symm
        (ha' s y' _ (hl R s y').symm).symm,
      ← adjPair3_eq gp (adjBase s) _ _ _ _ _ _ (ha s x _ (hl R s x).symm).symm (hl R s y) (hl R s y'), ← lm] at k
    rw [← map_mul, ← map_mul, ← map_mul]
    refine congrArg _ ?_
    have k' := congrArg Additive.ofMul k
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, v] at k' ⊢
    linear_combination (norm := abel) k'

end Main

end GlobalTheory
