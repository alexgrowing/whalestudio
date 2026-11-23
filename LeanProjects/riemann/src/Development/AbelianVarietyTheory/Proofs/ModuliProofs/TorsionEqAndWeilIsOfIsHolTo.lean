import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HolTorsion

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}

theorem isHolTo_comp {X Y : Scheme.{0}} {c : E → (Sp ℂ ⟶ X)} (hc : IsHolTo B c) (φ : X ⟶ Y) :
    IsHolTo B fun b => c b ≫ φ := by
  intro U f
  have := hc (φ ⁻¹ᵁ U) ((φ.app U).hom f)
  simpa only [valAt'_comp, ← top_le_preimage_comp] using this

theorem isHolTo_congr {X : Scheme.{0}} {c c' : E → (Sp ℂ ⟶ X)} (hc : IsHolTo B c) (h : ∀ b ∈ B, c' b = c b) :
    IsHolTo B c' := by
  intro U f
  have e : {b ∈ B | ⊤ ≤ c' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ c b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [h b hb]
  rw [e]
  exact ⟨(hc U f).1, (hc U f).2.congr fun b hb => by rw [h b hb.1]⟩

theorem isHolTo_of_isPullback {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)} (ha : IsHolTo B fun w => c w ≫ p)
    (hb : IsHolTo B fun w => c w ≫ q) : IsHolTo B c := by
  intro U f
  refine holFamily_of_affine valAt'_rules B Z c (fun w₀ hw₀ => ?_) U f
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((c w₀ ≫ p ≫ s) (default : PrimeSpectrum ℂ))) isOpen_univ
  have m₁ : (c w₀ ≫ p) (default : PrimeSpectrum ℂ) ∈ s ⁻¹ᵁ U₀ := by
    rw [← Category.assoc] at hx₀
    exact hx₀
  have m₂ : (c w₀ ≫ q) (default : PrimeSpectrum ℂ) ∈ t ⁻¹ᵁ U₀ := by
    rw [H.w, ← Category.assoc] at hx₀
    exact hx₀
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hx₁, l₁⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open m₁ (s ⁻¹ᵁ U₀).isOpen
  obtain ⟨_, ⟨U₂, hU₂, rfl⟩, hx₂, l₂⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open m₂ (t ⁻¹ᵁ U₀).isOpen
  have hU₀ : IsAffineOpen U₀ := hU₀
  have hU₁ : IsAffineOpen U₁ := hU₁
  have hU₂ : IsAffineOpen U₂ := hU₂
  have l₁ : U₁ ≤ s ⁻¹ᵁ U₀ := l₁
  have l₂ : U₂ ≤ t ⁻¹ᵁ U₀ := l₂
  set V : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ U₂ with hVdef
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ V ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U₂ := fun w => by
    rw [hVdef, Scheme.Hom.preimage_inf, le_inf_iff, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hV : IsAffineOpen V := by
    have : IsAffine _ := hU₀
    have : IsAffine _ := hU₁
    have : IsAffine _ := hU₂
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := U₀) (UT := U₂) (UX := U₁) l₂ l₁
      hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := U₀) (UT := U₂) (UX := U₁) l₂ l₁ hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hU₀ hU₂ hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨V, hV, (hiff w₀).2 ⟨(top_le_preimage_iff_mem _ _).2 hx₁, (top_le_preimage_iff_mem _ _).2 hx₂⟩, ?_,
    fun g => ?_⟩
  · convert (ha U₁ 0).1.inter (hb U₂ 0).1 using 1
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hiff]
    tauto
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ((ha U₁ y).2.mono fun w hw => ⟨hw.1, ((hiff w).1 hw.2).1⟩).congr fun w hw =>
          valAt'_appLE (c w) p U₁ V _ y hw.2
      · exact ((hb U₂ y).2.mono fun w hw => ⟨hw.1, ((hiff w).1 hw.2).2⟩).congr fun w hw =>
          valAt'_appLE (c w) q U₂ V _ y hw.2
    | zero => exact (differentiableOn_const (0 : ℂ)).congr fun w _ => valAt'_zero _ _
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => exact (hx.add hy).congr fun w _ => valAt'_add _ _ _ _
    | neg x _ hx => exact hx.neg.congr fun w _ => valAt'_neg _ _ _
    | mul x y _ _ hx hy => exact (hx.mul hy).congr fun w _ => valAt'_mul _ _ _ _

theorem exists_isHolTo_lift {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {a : E → (Sp ℂ ⟶ X)} {a' : E → (Sp ℂ ⟶ Y)} (ha : IsHolTo B a) (ha' : IsHolTo B a')
    (h : ∀ w ∈ B, a w ≫ s = a' w ≫ t) {b₀ : E} (hb₀ : b₀ ∈ B) :
    ∃ c : E → (Sp ℂ ⟶ Z), IsHolTo B c ∧ ∀ w ∈ B, c w ≫ p = a w ∧ c w ≫ q = a' w := by
  classical
  let c : E → (Sp ℂ ⟶ Z) := fun w =>
    if hw : w ∈ B then H.lift (a w) (a' w) (h w hw) else H.lift (a b₀) (a' b₀) (h b₀ hb₀)
  have hc : ∀ w ∈ B, c w ≫ p = a w ∧ c w ≫ q = a' w := fun w hw => by
    simp only [c, dif_pos hw, IsPullback.lift_fst, IsPullback.lift_snd, and_self]
  exact ⟨c, isHolTo_of_isPullback H (isHolTo_congr ha fun w hw => (hc w hw).1)
    (isHolTo_congr ha' fun w hw => (hc w hw).2), hc⟩

theorem mem_of_isClosed {Z : Scheme.{0}} {c : E → (Sp ℂ ⟶ Z)} (hc : IsHolTo B c) (hB : IsPreconnected B)
    (U : Z.Opens) (hU : IsClosed (U : Set Z)) {b₀ : E} (hb₀ : b₀ ∈ B) (h₀ : c b₀ (default : PrimeSpectrum ℂ) ∈ U)
    {b : E} (hb : b ∈ B) : c b (default : PrimeSpectrum ℂ) ∈ U := by
  let U' : Z.Opens := ⟨(U : Set Z)ᶜ, hU.isOpen_compl⟩
  have h := hB.subset_left_of_subset_union (hc U 0).1 (hc U' 0).1
    (Set.disjoint_left.2 fun w h₁ h₂ =>
      (top_le_preimage_iff_mem _ _).1 h₂.2 ((top_le_preimage_iff_mem _ _).1 h₁.2))
    (fun w hw => by
      by_cases hm : c w (default : PrimeSpectrum ℂ) ∈ U
      · exact Or.inl ⟨hw, (top_le_preimage_iff_mem _ _).2 hm⟩
      · exact Or.inr ⟨hw, (top_le_preimage_iff_mem _ _).2 hm⟩)
    ⟨b₀, hb₀, hb₀, (top_le_preimage_iff_mem _ _).2 h₀⟩
  exact (top_le_preimage_iff_mem _ _).1 (h hb).2

theorem valAt'_eq_of_pow_eq_one {Z : Scheme.{0}} {c : E → (Sp ℂ ⟶ Z)} (hc : IsHolTo B c) (hB : IsPreconnected B)
    {e : Γ(Z, ⊤)} {k : ℕ} (hk : 0 < k) (he : e ^ k = 1) {b₀ b : E} (hb₀ : b₀ ∈ B) (hb : b ∈ B) :
    valAt' (c b) ⊤ e = valAt' (c b₀) ⊤ e := by
  have hcont : ContinuousOn (fun w => valAt' (c w) ⊤ e) B :=
    (hc ⊤ e).2.continuousOn.mono fun w hw => ⟨hw, le_top⟩
  have hfin : (Polynomial.nthRootsFinset k (1 : ℂ) : Set ℂ).Finite := Finset.finite_toSet _
  refine hB.constant_of_mapsTo hfin.isDiscrete hcont (fun w _ => ?_) hb hb₀
  rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hk, ← valAt'_pow _ le_top, he, valAt'_one _ le_top]

theorem comp_eq_of_unramified {N X : Scheme.{0}} (q : N ⟶ X) [FormallyUnramified q] [LocallyOfFiniteType q]
    [IsSeparated q] {c : E → (Sp ℂ ⟶ pullback q q)} (hc : IsHolTo B c) (hB : IsPreconnected B) {b₀ b : E}
    (hb₀ : b₀ ∈ B) (hb : b ∈ B) (h₀ : c b₀ ≫ pullback.fst q q = c b₀ ≫ pullback.snd q q) :
    c b ≫ pullback.fst q q = c b ≫ pullback.snd q q := by
  have e₀ : c b₀ = (c b₀ ≫ pullback.fst q q) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · simp
    · simp [h₀]
  have hm : c b (default : PrimeSpectrum ℂ) ∈ (pullback.diagonal q).opensRange := by
    refine mem_of_isClosed hc hB _ (pullback.diagonal q).isClosedEmbedding.isClosed_range hb₀ ?_ hb
    rw [e₀]
    exact ⟨_, rfl⟩
  have hr : Set.range (c b) ⊆ Set.range (pullback.diagonal q) := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact hm
  rw [← IsOpenImmersion.lift_fac (pullback.diagonal q) (c b) hr, Category.assoc, Category.assoc,
    pullback.diagonal_fst, pullback.diagonal_snd]

theorem pow_eq_one_of_weilIs (hW : Out.WeilSt) {X : Scheme.{0}} [IsLocallyNoetherian X] (P : Out.PolAV X) (k : ℕ)
    {T : Over X} {u v : T ⟶ P.A} (hu : u ^ k = 1) (hv : v ^ k = 1) {e : Γ(T.left, ⊤)ˣ}
    (he : Out.WeilIs P.A P.L k u v e) : e ^ k = 1 := by
  obtain ⟨h₁, h₂, -⟩ := hW X P k T
  obtain ⟨d, hd, hd'⟩ := h₁ 1 v (one_pow k) hv
  have hdd := h₂ 1 1 v d d hd hd
  rw [_root_.mul_one] at hdd
  obtain rfl : d = 1 := mul_eq_left.1 (hd' _ hdd)
  have key : ∀ n : ℕ, Out.WeilIs P.A P.L k (u ^ n) v (e ^ n) := fun n => by
    induction n with
    | zero => simpa only [pow_zero] using hd
    | succ n ih => simpa only [pow_succ] using h₂ _ _ _ _ _ ih he
  have hk := key k
  rw [hu] at hk
  exact hd' _ hk

theorem val_map_appTop {Z : Scheme.{0}} (z : Sp ℂ ⟶ Z) (e : Γ(Z, ⊤)) :
    z.appTop.hom e = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (valAt' z ⊤ e) := by
  rw [valAt'_eq_valAt z (U := ⊤) le_top]
  unfold valAt
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.HolTorsion

namespace GlobalTheory

open HolTorsion in

theorem torsion_eq_and_weilIs_of_isHolTo : Out.Laws → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (m k : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ P.A) (c : ℂˣ) (b₀ : Fin m → ℂ), 0 < k → IsUnit (k : Γ(X, ⊤)) → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ = x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs P.A P.L k (x b₀) (x' b₀) (unitOn c) → ∀ b ∈ B, Out.WeilIs P.A P.L k (x b) (x' b) (unitOn c))) := by
  intro hL X _ P m k B y x x' c b₀ hk hku _ hB hb₀ hx hx' htor
  obtain ⟨hfin, -, -, het, -⟩ := hL.mulN X P k hk
  have het := het hku
  let o : X ⟶ P.A.left := (η[P.A] : 𝟙_ (Over X) ⟶ P.A).left
  have ho : o ≫ P.A.hom = 𝟙 X := Over.w (η[P.A] : 𝟙_ (Over X) ⟶ P.A)

  have hkill : ∀ (T : Over X) (u : T ⟶ P.A), u ^ k = 1 ↔ u.left ≫ (Out.mulA P.A k).left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ (Out.mulA P.A k).left = (u ^ k).left := by
      rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ P.A).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst (Out.mulA P.A k).left o
  let q := pullback.snd (Out.mulA P.A k).left o
  have H : IsPullback p q (Out.mulA P.A k).left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ P.A.hom = q := by
    rw [← Over.w (Out.mulA P.A k), ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx P.A.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  refine ⟨fun h₀ b hb => ?_, fun h₀ b hb => ?_⟩
  · have e₀ : a b₀ = a' b₀ := H.hom_ext (by rw [(hab b₀ hb₀).1, (hab' b₀ hb₀).1, h₀])
      (by rw [(hab b₀ hb₀).2, (hab' b₀ hb₀).2])
    have e := comp_eq_of_unramified q hz hB hb₀ hb (by rw [(hzb b₀ hb₀).1, (hzb b₀ hb₀).2, e₀])
    rw [(hzb b hb).1, (hzb b hb).2] at e
    apply Over.OverMorphism.ext
    rw [← (hab b hb).1, ← (hab' b hb).1, e]
  · let T : Over X := Over.mk (pullback.fst q q ≫ q)
    let u : T ⟶ P.A := Over.homMk (pullback.fst q q ≫ p) (by
      show (pullback.fst q q ≫ p) ≫ P.A.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq])
    let v : T ⟶ P.A := Over.homMk (pullback.snd q q ≫ p) (by
      show (pullback.snd q q ≫ p) ≫ P.A.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq, pullback.condition])
    have hu : u ^ k = 1 := (hkill T u).2 (by
      show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, Category.assoc])
    have hv : v ^ k = 1 := (hkill T v).2 (by
      show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, pullback.condition, Category.assoc])
    obtain ⟨e, he, -⟩ := (hL.weil X P k T).1 u v hu hv
    have hek : e.val ^ k = 1 :=
      congrArg Units.val (pow_eq_one_of_weilIs hL.weil P k hu hv he)
    have hpull : ∀ w ∈ B, Out.WeilIs P.A P.L k (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
      intro w hw
      let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
        show z w ≫ pullback.fst q q ≫ q = y w
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
      have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
        show z w ≫ pullback.fst q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
      have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
        show z w ≫ pullback.snd q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
      have := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h he
      rw [e₁, e₂] at this
      exact this
    have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn c :=
      ((hL.weil X P k _).1 _ _ (htor b₀ hb₀).1 (htor b₀ hb₀).2).unique (hpull b₀ hb₀) h₀
    have e₁ : Units.map (z b).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
      Units.ext ((val_map_appTop (z b) e.val).trans
        ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hk hek hb₀ hb)).trans (val_map_appTop (z b₀) e.val).symm))
    have := hpull b hb
    rw [e₁, e₀] at this
    exact this

end GlobalTheory
