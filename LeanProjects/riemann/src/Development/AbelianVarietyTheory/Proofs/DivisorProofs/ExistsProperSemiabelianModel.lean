import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianIsoOfExtensionIsoStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsSemiAbelianIsGt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumBaseChangeMapsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushHomBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdDim.UnivExt

theorem exists_pow {S : Scheme.{0}} (A : Over S) (hA : IsProper A.hom) : ∀ n : ℕ,
    ∃ (Y : Over S) (p : Fin n → (Y ⟶ A)), IsProper Y.hom ∧
      ∀ (T : Over S) (c : Fin n → (T ⟶ A)), ∃ x : T ⟶ Y, ∀ i, x ≫ p i = c i
  | 0 => ⟨𝟙_ _, Fin.elim0, inferInstanceAs (IsProper (𝟙 S)), fun T _ => ⟨toUnit T, fun i => i.elim0⟩⟩
  | n + 1 => by
    obtain ⟨Y, p, hY, H⟩ := exists_pow A hA n
    refine ⟨A ⊗ Y, Fin.cons (fst A Y) fun i => snd A Y ≫ p i,
      inferInstanceAs (IsProper (pullback.fst A.hom Y.hom ≫ A.hom)), fun T c => ?_⟩
    obtain ⟨x, hx⟩ := H T fun i => c i.succ
    refine ⟨lift (c 0) x, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp [hx]

theorem const_left {S : Scheme.{0}} {G : Over S} (T : Over S) (x : 𝟙_ _ ⟶ G) :
    (toUnit T ≫ x).left = T.hom ≫ x.left :=
  congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit T)))

theorem pull_lam_of_eq {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (l : Pic G.left) (g : T'.left ⟶ T.left)
    {a b : T ⟶ G} {a' b' : T' ⟶ G} (ha : g ≫ a.left = a'.left) (hb : g ≫ b.left = b'.left) :
    pull g (lam l a b) = lam l a' b' := by
  let u : T' ⟶ T := Over.homMk g (by rw [← Over.w a, ← Category.assoc, ha, Over.w])
  have e₁ : u ≫ a = a' := Over.OverMorphism.ext ha
  have e₂ : u ≫ b = b' := Over.OverMorphism.ext hb
  rw [← e₁, ← e₂]
  exact pull_lam u l a b

theorem exists_bundles {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (l : Pic B.left)
    (hl : ∀ (T : Over S) (x y z : T ⟶ B), lam l (x * y) z = lam l x z + lam l y z)
    (X : Type) [AddCommGroup X] (c : Multiplicative X →* (𝟙_ (Over S) ⟶ B)) :
    ∃ O : X → RigLB B,
      (∀ χ χ' : X, ∃ t : LB.Iso (O χ').L (LB.div (O (χ + χ')).L (O χ).L), t.IsGen) ∧
      (∃ t : LB.Gen (O 0).L, t.IsGen) ∧ (∀ χ : X, ∃ t : LB.Gen (abelian₂ B (O χ).L), t.IsGen) ∧
      ∀ χ, cls (O χ).L (O χ).isLB = lam l (toUnit B ≫ c (Multiplicative.ofAdd χ)) (𝟙 B) := by
  choose M hM eM using fun χ : X => cls_surj (lam l (toUnit B ≫ c (Multiplicative.ofAdd χ)) (𝟙 B))
  have pt : ∀ (χ : X) (T : Over S) (y : T ⟶ B),
      pull y.left (cls _ (hM χ)) = lam l y (toUnit T ≫ c (Multiplicative.ofAdd χ)) := fun χ T y => by
    rw [eM, pull_lam, Category.comp_id, ← Category.assoc, comp_toUnit, lam_comm]
  have rig : ∀ χ, ∃ t : LB.Gen ((M χ).pull (eSec B)), t.IsGen := fun χ => by
    refine (cls_eq_zero_iff (pull_isLB (hM χ) _)).1 ((pt χ _ η[B]).trans ?_)
    have e : (η[B] : 𝟙_ _ ⟶ B) = 1 := by simp [Hom.one_def]
    rw [e, lam_one_left]
  refine ⟨fun χ => ⟨M χ, (rig χ).choose, hM χ, (rig χ).choose_spec⟩, fun χ χ' => ?_, ?_, fun χ => ?_, eM⟩
  · refine (cls_eq_iff (hM χ') (LB.isLB_div (hM _) (hM _))).1 ?_
    rw [cls_div (hM _) (hM _), eM, eM, eM, ofAdd_add, map_mul, MonObj.comp_mul, hl, add_sub_cancel_left]
  · refine (cls_eq_zero_iff (hM 0)).1 ?_
    rw [eM, ofAdd_zero, map_one, MonObj.comp_one, lam_one_left]
  · refine (cls_eq_zero_iff (LB.isLB_linComb (hM χ) _ _)).1
      ((cls_cube_two (hM χ) (fst B B) (snd B B) (LB.isLB_linComb (hM χ) _ _)).trans ?_)
    rw [lam, pt, pt, pt, pt, hl, lam_one_left]
    abel

theorem exists_point {S : Scheme.{0}} (P : Out.PolAV S) {k : Type} [Field k] [IsAlgClosed k] {f : Sp k ⟶ S}
    {B : Over (Sp k)} [GrpObj B] {β : B.left ⟶ P.A.left} (h : IsGrpPullback B P.A f β) (o : Pic B.left)
    (ho : lam o (fst B B) (snd B B) = 0) :
    ∃ x : Over.mk f ⟶ P.A, ∀ a b : Over.mk (B.hom ≫ f) ⟶ P.A, a.left = B.hom ≫ x.left → b.left = β →
      o = lam (cls P.L P.isLB) a b := by
  obtain ⟨Q, φ, hφ, -, hm, hL⟩ := abelianSchemeLaws_all.1.polBaseChange _ _ f P
  have hQ : IsGrpPullback Q.A P.A f φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = Out.toBase hφ.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = Out.toBase hφ.w y := Over.OverMorphism.ext hy
    exact congrArg (fun q => q.left) (hm T x y).symm⟩
  have eL : cls Q.L Q.isLB = pull φ (cls P.L P.isLB) := ((cls_eq_iff (pull_isLB P.isLB φ) Q.isLB).2 hL).symm
  obtain ⟨e, he, heβ⟩ := grpPullback_iso h hQ
  obtain ⟨M, hM, eM⟩ := cls_surj (pull e.inv.left o)
  have hp : ∃ u : LB.Gen (abelian₂ Q.A M), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1
      ((cls_cube_two hM (fst Q.A Q.A) (snd Q.A Q.A) (LB.isLB_linComb hM _ _)).trans ?_)
    have j := pull_lam (lift (fst Q.A Q.A ≫ e.inv) (snd Q.A Q.A ≫ e.inv)) o (fst B B) (snd B B)
    rw [ho, map_zero, lift_fst, lift_snd] at j
    rw [eM, lam_pull]
    exact j.symm
  obtain ⟨x, hx⟩ := PrimitiveOverField.exists_point_translate abelianSchemeLaws_all.1 k Q M hM hp
  have e₁ : pull e.inv.left o = lam (cls Q.L Q.isLB) (toUnit Q.A ≫ x) (𝟙 Q.A) := by
    rw [← eM, (cls_eq_iff hM (LB.isLB_linComb Q.isLB _ _)).2 hx, PrimitiveOverField.lam_const]
    refine (cls_linComb Q.isLB _ _ _).trans ?_
    rw [Fin.sum_univ_two, sub_eq_add_neg]
    exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)
  have hxw : x.left ≫ Q.A.hom = 𝟙 _ := Over.w x
  refine ⟨Over.homMk (x.left ≫ φ) ?_, fun a b ha hb => ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hφ.w).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hxw).trans (Category.id_comp _))))
  · have e₂ : o = pull e.hom.left (pull e.inv.left o) := by
      rw [← pull_comp, ← Over.comp_left, e.hom_inv_id, Over.id_left, pull_id]
    rw [e₁, eL, lam_pull_of_isGrpPullback hQ] at e₂
    refine e₂.trans (pull_lam_of_eq (T := Over.mk (Q.A.hom ≫ f)) (T' := Over.mk (B.hom ≫ f))
      (cls P.L P.isLB) e.hom.left ?_ ?_)
    · have w : e.hom.left ≫ (toUnit Q.A ≫ x).left ≫ φ = B.hom ≫ x.left ≫ φ := by
        rw [const_left, ← Over.w e.hom]
        simp only [Category.assoc]
      have w₁ : (pushHom hQ Q.A (toUnit Q.A ≫ x)).left = (toUnit Q.A ≫ x).left ≫ φ := rfl
      exact ((congrArg (e.hom.left ≫ ·) w₁).trans w).trans ha.symm
    · rw [hb, ← heβ]
      change e.hom.left ≫ 𝟙 _ ≫ φ = _
      rw [Category.id_comp]

def clsHom {S : Scheme.{0}} (E : SplitExt S) : E.X →+ Pic E.B.left :=
  AddMonoidHom.mk' (fun χ => cls (E.O χ).L (E.O χ).isLB) fun χ χ' => by
    have h := (cls_eq_iff (E.O χ').isLB (LB.isLB_div (E.O _).isLB (E.O _).isLB)).2 (E.addIso χ χ')
    rw [cls_div (E.O _).isLB (E.O _).isLB] at h
    rw [h, add_sub_cancel]

theorem exists_universal : ∀ (k₀ k : Type) [Field k₀] [Field k] [IsAlgClosed k] (κ : k₀ →+* k) (P₀ : Out.PolAV (Sp k₀)) (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp k ⟶ X), IsSemiAbelian G → IsAbPart G x P₀.A (spMap κ) → ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp k₀) (E : SplitExt X') (G' : Over X') (_ : GrpObj G') (x' : Sp k ⟶ X') (π : E.B.left ⟶ P₀.A.left), IsProper s' ∧ x' ≫ s' = spMap κ ∧ IsGrpPullback E.B P₀.A s' π ∧ IsSemiAbelian G' ∧ E.IsGt G' ∧ SameFibre G x G' x' := by
  rintro k₀ k _ _ _ κ P₀ X G _ x hG ⟨A, _, φ, t, β, hA, hβ⟩
  have laws := abelianSchemeLaws_all.1
  letI := t.addCommGroup
  letI := t.free
  letI := t.finite
  letI := t.grpB
  haveI := hG.comm
  haveI := P₀.isAb.comm
  haveI : IsCommMonObj A := PolPull.isCommMonObj_of_isGrpPullback hA
  have hAs : IsSemiAbelian A := SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hA hG
  obtain ⟨O₁, h₁, h₂, h₃, h⟩ := GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension (Sp k) t.X A t.B t.isAbelian t.q t.i
    t.q_hom t.i_hom t.q_flat t.q_surjective t.q_quasiCompact t.isKernel
  obtain ⟨d₁, -, -⟩ := h t.isAbelian
  let E₁ : SplitExt (Sp k) := SplitExt.mk t.B t.isAbelian t.X O₁ h₁ h₂ h₃
  have hΘ : ∃ t : LB.Gen (Theta P₀.A P₀.L), t.IsGen := by
    obtain ⟨r, hr⟩ := P₀.rigid
    obtain ⟨c⟩ := (laws.cube _ P₀ ⟨P₀.L, r, P₀.isLB, hr⟩ rfl).1
    exact ⟨c.t, c.isGen⟩
  let b := Module.finBasis ℤ t.X
  choose c hc using fun i => exists_point P₀ hβ (cls (O₁ (b i)).L (O₁ (b i)).isLB)
    ((cls_cube_two (O₁ (b i)).isLB _ _ (LB.isLB_linComb (O₁ (b i)).isLB _ _)).symm.trans
      ((cls_eq_zero_iff _).2 (h₃ (b i))))
  obtain ⟨Y, p, hY, hp⟩ := exists_pow P₀.A P₀.isAb.proper (Module.finrank ℤ t.X)
  obtain ⟨y, hy⟩ := hp _ c
  let B : Over Y.left := (Over.pullback Y.hom).obj P₀.A
  let π : B.left ⟶ P₀.A.left := pullback.fst P₀.A.hom Y.hom
  have hB : IsGrpPullback B P₀.A Y.hom π := isGrpPullback_pullback P₀.A Y.hom
  have hBa := PolPull.isAbelianScheme_of_isGrpPullback P₀.isAb hB
  haveI := hBa.comm
  choose s hs using fun i => (GenericKTriv.pushHom_bijective hB (𝟙_ _)).2
    (Over.homMk (p i).left ((Over.w (p i)).trans (Category.id_comp _).symm))
  have hs' : ∀ i, (s i).left ≫ π = (p i).left := fun i => congrArg (fun q => q.left) (hs i)
  let σ : Multiplicative t.X →* (𝟙_ (Over Y.left) ⟶ B) := AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ (fun i => Additive.ofMul (s i))).toAddMonoidHom
  have hσ : ∀ i, σ (Multiplicative.ofAdd (b i)) = s i := fun i =>
    congrArg Additive.toMul (b.constr_basis ℤ (fun i => Additive.ofMul (s i)) i)
  obtain ⟨O, g₁, g₂, g₃, hO⟩ := exists_bundles B (pull π (cls P₀.L P₀.isLB)) (fun T u v w => by
    simp only [lam_pull_of_isGrpPullback hB, map_mul, lam_mul_left P₀.isLB hΘ]) t.X σ
  let E : SplitExt Y.left := SplitExt.mk B hBa t.X O g₁ g₂ g₃
  obtain ⟨G', _, hG', ⟨d⟩⟩ := exists_isSemiAbelian_isGt laws.globalFns _ E
  have hyw : y.left ≫ Y.hom = spMap κ := Over.w y
  refine ⟨Y.left, Y.hom, E, G', _, y.left, π, hY, hyw, hB, hG', ⟨d⟩, ?_⟩
  obtain ⟨E', xe, d', π', hπ', -, hiso, -⟩ := GlobalTheory.T.exists_gtDatum_baseChange_maps' _ _ y.left E G' d
  have hF := isGrpPullback_pullback G' y.left
  haveI := hG'.comm
  haveI := PolPull.isCommMonObj_of_isGrpPullback hF
  have hFs := SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hF hG'
  obtain ⟨e, he, heβ⟩ := grpPullback_iso hβ ((hπ'.comp hB).congr hyw rfl)
  have key : (clsHom E₁).toIntLinearMap = ((pull (e.hom.left ≫ π')).comp (clsHom E)).toIntLinearMap := by
    refine b.ext fun i => ?_
    change cls (O₁ (b i)).L (O₁ (b i)).isLB = pull (e.hom.left ≫ π') (cls (O (b i)).L (O (b i)).isLB)
    rw [hO, hσ, lam_pull_of_isGrpPullback hB]
    refine (hc i (Over.homMk (U := Over.mk (t.B.hom ≫ spMap κ)) (V := Over.mk (spMap κ)) t.B.hom rfl ≫ c i)
      (pushHom hβ _ (𝟙 _)) rfl (Category.id_comp _)).trans (pull_lam_of_eq _ _ ?_ ?_).symm
    · change (e.hom.left ≫ π') ≫ (toUnit B ≫ s i).left ≫ π = t.B.hom ≫ (c i).left
      have w : π' ≫ B.hom = E'.B.hom ≫ y.left := hπ'.1.w
      rw [const_left, ← hy, Over.comp_left, ← Over.w e.hom]
      simp only [Category.assoc]
      rw [hs', reassoc_of% w]
    · change (e.hom.left ≫ π') ≫ 𝟙 _ ≫ π = 𝟙 _ ≫ β
      rw [Category.id_comp, Category.id_comp, Category.assoc]
      exact heβ
  obtain ⟨i, hi⟩ := GlobalTheory.T.semiabelian_iso_of_extension_iso k E₁ E' A ((Over.pullback y.left).obj G') e xe.symm he hAs hFs (fun χ => by
    refine (cls_eq_iff (E₁.O χ).isLB (pull_isLB (E'.O _).isLB _)).1 ?_
    rw [cls_pull (E'.O _).isLB, (cls_eq_iff (E'.O _).isLB (pull_isLB (E.O _).isLB _)).2 (hiso _),
      cls_pull (E.O _).isLB, ← pull_comp]
    refine (LinearMap.congr_fun key χ).trans ?_
    exact congrArg (fun χ => pull (e.hom.left ≫ π') (clsHom E χ)) (xe.apply_symm_apply χ).symm) ⟨d₁⟩ ⟨d'⟩
  exact ⟨A, _, φ, _, hA, ((isGrpPullback_of_iso i).comp hF).congr (Category.id_comp _) rfl⟩

end GlobalTheory.BdDim.UnivExt

end
