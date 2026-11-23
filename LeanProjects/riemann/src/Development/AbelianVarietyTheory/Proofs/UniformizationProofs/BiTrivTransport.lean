import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompRedIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitAddMonoidAlgebraIffOfTwoUniqueSums

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiTransport

variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}

theorem lift_lam {G H T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G) (t : T ⟶ H) (x : T ⟶ G)
    (k : Fin 4) : (lift t x).left ≫ lamφ i k = (![(t ≫ i) * x, t ≫ i, x, 1] k : T ⟶ G).left := by
  fin_cases k
  · exact congrArg (fun q => q.left) (show lift t x ≫ ((fst H G ≫ i) * snd H G) = (t ≫ i) * x by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd])
  · exact congrArg (fun q => q.left) (lift_fst_assoc t x i)
  · exact congrArg (fun q => q.left) (lift_snd t x)
  · exact congrArg (fun q => q.left) (show lift t x ≫ (1 : H ⊗ G ⟶ G) = 1 from MonObj.comp_one _)

theorem prod_lam {G H T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G) (t : T ⟶ H) (x : T ⟶ G)
    {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k, h ((lift t x).left ≫ lamφ i k) ^ Oε k =
      h ((t ≫ i) * x).left * (h (t ≫ i).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left := by
  simp only [lift_lam, Fin.prod_univ_four]
  show h ((t ≫ i) * x).left ^ (1 : ℤ) * h (t ≫ i).left ^ (-1 : ℤ) * h x.left ^ (-1 : ℤ) *
    h (1 : T ⟶ G).left ^ (1 : ℤ) = _
  simp only [zpow_one, zpow_neg]

theorem toBase_surj {A : Over S} {A₀ : Over S₀} {E : A₀.left ⟶ A.left} (hE : IsPullback E A₀.hom A.hom ρ)
    (hw : E ≫ A.hom = A₀.hom ≫ ρ) {T : Over S₀} (x : Over.mk (T.hom ≫ ρ) ⟶ A) : ∃ x₀ : T ⟶ A₀, toBase hw x₀ = x :=
  ⟨Over.homMk (hE.lift x.left T.hom (Over.w x)) (hE.lift_snd _ _ _), Over.OverMorphism.ext (hE.lift_fst _ _ _)⟩

theorem exists_over {Z : Over S} (r : Z.left ⟶ S₀) (h : r ≫ ρ = Z.hom) : ∃ T : Over S₀, Z = Over.mk (T.hom ≫ ρ) := by
  obtain ⟨Z, ⟨⟨⟩⟩, f⟩ := Z
  change Z ⟶ S₀ at r
  change Z ⟶ S at f
  obtain rfl : r ≫ ρ = f := h
  exact ⟨Over.mk r, rfl⟩

section
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G₀ H₀ : Over S₀} [GrpObj G₀] [IsCommMonObj G₀]
  [GrpObj H₀] {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ ρ} {E : H₀.left ⟶ H.left}
  {P : CP G} {P₀ : CP G₀} {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : H ⟶ G} {i₀ : H₀ ⟶ G₀}

omit [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj G₀] [IsCommMonObj G₀] [GrpObj H₀] in

theorem toBase_comp (hE : E ≫ H.hom = H₀.hom ≫ ρ) (hi : E ≫ i.left = i₀.left ≫ F) {T : Over S₀} (t : T ⟶ H₀) :
    toBase hE t ≫ i = toBase hw (t ≫ i₀) := Over.OverMorphism.ext (by
  show (t.left ≫ E) ≫ i.left = (t.left ≫ i₀.left) ≫ F
  rw [Category.assoc, hi, Category.assoc])

theorem exists_gen_val [Mono ρ] (hF : IsPullback F G₀.hom G.hom ρ) (hE : IsPullback E H₀.hom H.hom ρ)
    (hP : IsCPMap P₀ P ρ F hw w) (hi : E ≫ i.left = i₀.left ≫ F)
    (σ : LB.Gen (LB.LinComb P₀.L.L (lamφ i₀) Oε)) (hσ : σ.IsGen) :
    ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧
      ∀ (T : Over S₀) (t : T ⟶ H₀) (x : T ⟶ G₀) (a : T.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift (toBase hE.w t) (toBase hw x)).left →
        ∀ (z : T.left) (J' J), Good P₀.L.L z J' → Good P.L.L z J →
        ∀ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ, (∀ y, W y = gw w y.left z (J (y.left ≫ F)) (J' y.left)) →
          val s a z J = W ((t ≫ i₀) * x) * (W (t ≫ i₀))⁻¹ * (W x)⁻¹ * W 1 * val σ (lift t x).left z J' := by
  let Y : Over S₀ := Over.mk (pullback.snd (H ⊗ G).hom ρ)
  let j : Over.mk (Y.hom ≫ ρ) ⟶ H ⊗ G := Over.homMk (pullback.fst (H ⊗ G).hom ρ) pullback.condition
  obtain ⟨t₀, ht₀⟩ := toBase_surj hE hE.w (j ≫ fst H G)
  obtain ⟨x₀, hx₀⟩ := toBase_surj hF hw (j ≫ snd H G)
  have hj : pullback.fst (H ⊗ G).hom ρ = (lift (toBase hE.w t₀) (toBase hw x₀)).left := by
    rw [ht₀, hx₀, ← comp_lift, lift_fst_snd, Category.comp_id]; rfl
  have hφ : (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) = fun k => ((lift t₀ x₀).left ≫ lamφ i₀ k) ≫ F := by
    funext k
    refine ((congrArg (· ≫ lamφ i k) hj).trans (lift_lam i _ _ k)).trans
      (Eq.trans ?_ (congrArg (· ≫ F) (lift_lam i₀ t₀ x₀ k)).symm)
    rw [toBase_comp (hw := hw) hE.w hi]
    fin_cases k
    · exact (congrArg (fun q => q.left) (hP.mul Y (t₀ ≫ i₀) x₀)).symm
    · rfl
    · rfl
    · exact (congrArg (fun q => q.left) (map_one (toBaseHom hP.mul Y))).symm
  obtain ⟨s, hs, hv⟩ := exists_up ((isGen_iff w).1 hP.gen) P.L.isLB P₀.L.isLB
    (LB.pullGen P₀.L.L (lamφ i₀) Oε σ (lift t₀ x₀).left) (DVR.pullGen_isGen _ _ _ _ hσ _)
  rw [hφ]
  refine ⟨s, hs, fun T t x a ha z J' J hJ' hJ W hW => ?_⟩
  have e₀ : a ≫ pullback.snd (H ⊗ G).hom ρ = T.hom := by
    rw [← cancel_mono ρ, Category.assoc, ← pullback.condition, ← Category.assoc, ha]
    exact Over.w _
  let a' : T ⟶ Y := Over.homMk a e₀
  have e₁ : a' ≫ t₀ = t := Over.OverMorphism.ext (hE.hom_ext (by
    have := congrArg (fun q => a ≫ q.left) ht₀
    refine ((Category.assoc _ _ _).trans this).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fst H G).left) ha)).trans ?_
    exact congrArg (fun q => q.left) (lift_fst (toBase hE.w t) (toBase hw x))) ((Over.w _).trans (Over.w _).symm))
  have e₂ : a' ≫ x₀ = x := Over.OverMorphism.ext (hF.hom_ext (by
    have := congrArg (fun q => a ≫ q.left) hx₀
    refine ((Category.assoc _ _ _).trans this).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (snd H G).left) ha)).trans ?_
    exact congrArg (fun q => q.left) (lift_snd (toBase hE.w t) (toBase hw x))) ((Over.w _).trans (Over.w _).symm))
  have e₃ : a ≫ (lift t₀ x₀).left = (lift t x).left :=
    congrArg (fun q => q.left) (show a' ≫ lift t₀ x₀ = lift t x by rw [comp_lift, e₁, e₂])
  have v := hv _ a z _ _ (hJ.mem (fun k => ((lift t₀ x₀).left ≫ lamφ i₀ k) ≫ F) a)
    (hJ'.mem (fun k => (lift t₀ x₀).left ≫ lamφ i₀ k) a)
  refine v.trans (congrArg₂ (· * ·) ?_ ((val_pull hJ' σ _ a).trans (congrArg (fun q => val σ q z J') e₃)))
  simp only [hW]
  refine Eq.trans ?_ (prod_lam i₀ t x (fun q => gw w q z (J (q ≫ F)) (J' q)))
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← e₃]
  simp only [Category.assoc]

theorem exists_transport [Mono ρ] (hF : IsPullback F G₀.hom G.hom ρ) (hE : IsGrpPullback H₀ H ρ E)
    (hP : IsCPMap P₀ P ρ F hw w) (hi : E ≫ i.left = i₀.left ≫ F) [IsMonHom i₀] (σ : BiTriv P₀.c i₀) :
    ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧
      (∀ (Z : Over S) (t t' : Z ⟶ H) (x : Z ⟶ G) (a b d : Z.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift (t * t') x).left → b ≫ pullback.fst _ _ = (lift t x).left →
        d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I), Good P.L.L z I →
        val s a z I = cubV P.c z I (t ≫ i) (t' ≫ i) x * val s b z I * val s d z I) ∧
      (∀ (Z : Over S) (t : Z ⟶ H) (x x' : Z ⟶ G) (a b d : Z.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift t (x * x')).left → b ≫ pullback.fst _ _ = (lift t x).left →
        d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I), Good P.L.L z I →
        val s a z I = cubV P.c z I (t ≫ i) x x' * val s b z I * val s d z I) := by
  obtain ⟨s, hs, hv⟩ := exists_gen_val hF hE.1 hP hi σ.s σ.gen
  have ov : ∀ (Z : Over S) (a : Z.left ⟶ pullback (H ⊗ G).hom ρ) (p : Z ⟶ H ⊗ G), a ≫ pullback.fst _ _ = p.left →
      ∃ T : Over S₀, Z = Over.mk (T.hom ≫ ρ) := fun Z a p ha => exists_over (a ≫ pullback.snd _ _) (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha]; exact Over.w p)
  refine ⟨s, hs, fun Z t t' x a b d ha hb hd z I hI => ?_, fun Z t x x' a b d ha hb hd z I hI => ?_⟩
  · obtain ⟨T, rfl⟩ := ov Z a _ ha
    obtain ⟨t, rfl⟩ := toBase_surj hE.1 hE.1.w t
    obtain ⟨t', rfl⟩ := toBase_surj hE.1 hE.1.w t'
    obtain ⟨x, rfl⟩ := toBase_surj hF hw x
    obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB (Z := T.left) z
    have m : toBase hE.1.w t * toBase hE.1.w t' = toBase hE.1.w (t * t') :=
      Over.OverMorphism.ext (hE.2 T t t' _ _ rfl rfl)
    rw [m] at ha
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ y, W y = gw w y.left z (I (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    have c := (hP.vals T z J' I hJ' hI W hW).2.2 (t ≫ i₀) (t' ≫ i₀) x
    have l := σ.law1 T t t' x z J' hJ'
    have va := hv T _ _ a ha z J' I hJ' hI W hW
    have vb := hv T _ _ b hb z J' I hJ' hI W hW
    have vd := hv T _ _ d hd z J' I hJ' hI W hW
    rw [MonObj.mul_comp] at va
    rw [toBase_comp (hw := hw) hE.1.w hi, toBase_comp (hw := hw) hE.1.w hi]
    show @id (T.left.presheaf.stalk z)ˣ (val s a z I) = @id (T.left.presheaf.stalk z)ˣ
      (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀)) (toBase hw (t' ≫ i₀)) (toBase hw x)) *
        @id (T.left.presheaf.stalk z)ˣ (val s b z I) * @id (T.left.presheaf.stalk z)ˣ (val s d z I)
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀))
      (toBase hw (t' ≫ i₀)) (toBase hw x)) = C at c ⊢
    refine va.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (C * ·) vb) vd).symm)
    rw [l]
    apply Additive.ofMul.injective
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv] at c' ⊢
    linear_combination (norm := abel) -c'
  · obtain ⟨T, rfl⟩ := ov Z a _ ha
    obtain ⟨t, rfl⟩ := toBase_surj hE.1 hE.1.w t
    obtain ⟨x, rfl⟩ := toBase_surj hF hw x
    obtain ⟨x', rfl⟩ := toBase_surj hF hw x'
    obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB (Z := T.left) z
    rw [← hP.mul] at ha
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ y, W y = gw w y.left z (I (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    have c := (hP.vals T z J' I hJ' hI W hW).2.2 (t ≫ i₀) x x'
    have l := σ.law2 T t x x' z J' hJ'
    have va := hv T _ _ a ha z J' I hJ' hI W hW
    have vb := hv T _ _ b hb z J' I hJ' hI W hW
    have vd := hv T _ _ d hd z J' I hJ' hI W hW
    rw [← _root_.mul_assoc (t ≫ i₀)] at va
    rw [toBase_comp (hw := hw) hE.1.w hi]
    show @id (T.left.presheaf.stalk z)ˣ (val s a z I) = @id (T.left.presheaf.stalk z)ˣ
      (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀)) (toBase hw x) (toBase hw x')) *
        @id (T.left.presheaf.stalk z)ˣ (val s b z I) * @id (T.left.presheaf.stalk z)ˣ (val s d z I)
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀))
      (toBase hw x) (toBase hw x')) = C at c ⊢
    refine va.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (C * ·) vb) vd).symm)
    rw [l]
    apply Additive.ofMul.injective
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv] at c' ⊢
    linear_combination (norm := abel) -c'

end

theorem biTriv_transport : ∀ (S S₀ : Scheme.{0}) (ρ : S₀ ⟶ S) [Mono ρ] (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G ρ F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P ρ F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat ρ F i₀ i → BiTriv P₀.c i₀ → ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (splitTorus S X ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧ (∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (x : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift (t * t') x).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) (t' ≫ i) x * val s b z I * val s d z I) ∧ (∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x x' : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift t (x * x')).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) x x' * val s b z I * val s d z I) := by
  intro S S₀ ρ _ X _ G _ _ G₀ _ _ F hw hF P P₀ w hP i i₀ _ _ hi σ
  exact exists_transport hF.1 (SplitTorus.isGrpPullback_bcMap ρ X) hP (torusCompat_iff.1 hi) σ

end GlobalTheory.UU.BiTransport
end
