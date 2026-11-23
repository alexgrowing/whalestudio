import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiExpansion

theorem exists_sec_of_retract {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (m : Y ⟶ Y') (hm : h ≫ m = 𝟙 Y')
    (e : ∀ k, m ≫ φ' k = φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ g => by simp only [e]) (H1.SectionArithmetic.pullSec s' m)
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, Category.assoc, hm, Category.comp_id]

theorem snd_lift_unit {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ _) G).left ≫ (lift (toUnit G) (𝟙 G)).left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  have : snd (𝟙_ _) G ≫ lift (toUnit G) (𝟙 G) = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  exact congrArg CommaMorphism.left this

variable {R : Type} [CommRing R] [IsDomain R]

omit [IsDomain R] in

theorem exists_lift_of_retraction (F : Type) [Field F] [Algebra (FractionRing R) F] (g : F →+* FractionRing R)
    (hg : ∀ a, g (algebraMap (FractionRing R) F a) = a) {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) F, κ'.left ≫ jFK (R := R) F = κ.left := by
  let i : (TK R).left ⟶ Spec (CommRingCat.of F) := Spec.map (CommRingCat.ofHom g)
  have hi : i ≫ jFK (R := R) F = 𝟙 (TK R).left := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    exact CommRingCat.hom_ext (RingHom.ext hg)
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by
    rw [Category.assoc, hi, Category.comp_id]
  exact ⟨Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ))), hκ⟩

theorem exists_lift_frac {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) (FractionRing R), κ'.left ≫ jFK (R := R) (FractionRing R) = κ.left :=
  exists_lift_of_retraction (FractionRing R) (RingHom.id _) (fun _ => rfl) κ

omit [IsDomain R] in

theorem exists_sameG {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} (hL : L.IsLB) {k : ℕ}
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ)))) :
    ∃ σ : H0 L k, SameG σ s :=
  exists_sec_of_retract hL _ _ (snd_lift_unit G)
    (fun _ => congrArg CommaMorphism.left (lift_snd (toUnit G) (𝟙 G))) s

theorem exists_sameB {D : DegPre R} {k : ℕ} (s : ∀ α, SecBT D (𝟙_ _) k α) : ∃ f : ∀ α, D.SecB k α, SameB f s := by
  have H : ∀ α, ∃ f : D.SecB k α, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval f (r ≫ (snd _ D.P.A).left) z J := fun α => by
    refine exists_sec_of_retract D.P.isLB _ _ (snd_lift_unit D.P.A) (fun i => ?_) (s α)
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit D.P.A) (𝟙 D.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫
        padd D.P.A (snd _ _) (toUnit _ ≫ D.c α) = padd D.P.A (𝟙 _) (toUnit _ ≫ D.c α) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ D.c α = toUnit _ ≫ D.c α from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ η[D.P.A] = toUnit _ ≫ η[D.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  choose f hf using H
  exact ⟨f, hf⟩

theorem psiRel_of_levelOneEq {D : DegPre R} {f₀ : ∀ α, D.SecB 1 α} {f : ∀ α, SecBT D (𝟙_ _) 1 α}
    (hs : SameB f₀ f) (h : PsiCompare.LevelOneEq D f₀) : PsiRel D (𝟙_ _) f := by
  intro χ T ρ κ y z J hJ
  obtain ⟨κ', hκ⟩ := exists_lift_frac κ
  have l : ∀ u : T ⟶ D.P.A, (lift ρ u).left ≫ (snd _ D.P.A).left = u.left := fun u =>
    congrArg CommaMorphism.left (lift_snd ρ u)
  have e := (h χ 0 rfl T κ' y z J hJ).trans (congrArg (fun q => sval (f₀ 0) (y * cT D T χ).left z J *
    (val (D.psi χ) q z J * rigV D z J).val) hκ)
  rw [hs χ _ _ z J hJ, hs 0 _ _ z J hJ, l, l]
  exact e.trans (mul_comm _ _)

theorem psiRel_of_expT : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal V), AdmBase V I → ∀ (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U₀ : Unif I D A G), Under U U₀.toUnifPre → ∀ (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D.toPre (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 σ f → PsiRel D.toPre (𝟙_ _) f := by
  intro h₁ h₂ V _ _ _ I hV D A G _ _ U U₀ hU σ f hE
  obtain ⟨σ₁, hσ₁⟩ := exists_sameG U.P.L.isLB σ
  obtain ⟨f₀, hf₀⟩ := exists_sameB f
  have ht : H0 U.P.L.L 1 = H0 U₀.toUnifPre.LG.L 1 := by rw [hU.2.1]
  have hc : HEq (cast ht σ₁) σ₁ := cast_heq ht σ₁
  have H := ((PreForm.under_exists_and_expands h₁ h₂ V I D A G U.semi).2.2 U U₀.toUnifPre hU 1 σ f (cast ht σ₁) f₀
    (fun τ hτ z J hJ => by
      obtain rfl : τ = σ₁ := eq_of_heq (hτ.trans hc)
      rw [hσ₁ _ _ z J hJ, Category.id_comp])
    (fun α z J hJ => by rw [hf₀ α _ _ z J hJ, Category.id_comp])).1 hE
  exact psiRel_of_levelOneEq hf₀
    (PsiCompare.levelOneEq_of_expandsAt h₁.globalFns hV U₀.toUnifPre (U₀.expand 1 le_rfl) _ f₀ H)

end GlobalTheory.PsiExpansion
end
