import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGerm
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.LocDescent

theorem gs_comp_stalkMap {W Z Y : Scheme.{0}} (x : W ⟶ Z) (g : Z ⟶ Y) (w : W) (U : Y.Opens) (h : g (x w) ∈ U)
    (a : Γ(Y, U)) : gs (x ≫ g) w U a = (x.stalkMap w).hom (gs g (x w) U a) := by
  exact (gs_eq (x ≫ g) w U h a).trans (((Scheme.Hom.germ_stalkMap_apply x (g ⁻¹ᵁ U) w h _).symm).trans
    (congrArg (x.stalkMap w).hom (gs_eq g (x w) U h a).symm))

theorem stalkMap_fromSpecStalk_injective {Z : Scheme.{0}} (z : Z) :
    Function.Injective ((Z.fromSpecStalk z).stalkMap (closedPoint (Z.presheaf.stalk z))).hom := by
  have e := Scheme.stalkClosedPointTo_fromSpecStalk z
  have h : Function.Injective (Scheme.stalkClosedPointTo (Z.fromSpecStalk z)).hom := by
    rw [e]
    exact (Iso.commRingCatIsoToRingEquiv _).injective
  exact Function.Injective.of_comp (f := (stalkClosedPointIso (Z.presheaf.stalk z)).hom.hom) h

theorem gs_appLE_top {Z Y : Scheme.{0}} (g : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) :
    gs (𝟙 Z) z ⊤ ((g.appLE U ⊤ h).hom a) = gs g z U a :=
  (gs_res (𝟙 Z) z h trivial _).trans ((gs_pull (𝟙 Z) g z U (h trivial) a).trans (by rw [Category.id_comp]))

theorem gs_eq_of_local {Z Y : Scheme.{0}} (g₁ g₂ : Z ⟶ Y) (z : Z) (U : Y.Opens) (h₁ : g₁ z ∈ U) (h₂ : g₂ z ∈ U)
    (a : Γ(Y, U)) (h : gs (Z.fromSpecStalk z ≫ g₁) (closedPoint (Z.presheaf.stalk z)) U a =
      gs (Z.fromSpecStalk z ≫ g₂) (closedPoint (Z.presheaf.stalk z)) U a) : gs g₁ z U a = gs g₂ z U a := by
  have e : Z.fromSpecStalk z (closedPoint (Z.presheaf.stalk z)) = z := Scheme.fromSpecStalk_closedPoint
  have H : ∀ y : Z, y = z → gs g₁ y U a = gs g₂ y U a → gs g₁ z U a = gs g₂ z U a := by
    rintro _ rfl h
    exact h
  have m : ∀ (g : Z ⟶ Y) (y : Z), y = z → g z ∈ U → g y ∈ U := by
    rintro g _ rfl h
    exact h
  exact H _ e (stalkMap_fromSpecStalk_injective z ((gs_comp_stalkMap _ g₁ _ U (m g₁ _ e h₁) a).symm.trans
    (h.trans (gs_comp_stalkMap _ g₂ _ U (m g₂ _ e h₂) a))))

theorem trF_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (q : Y' ⟶ Y) (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (j j' : K → L.ι) :
    trF (fun a => q ≫ ψ a) ε r z j j' = trF ψ ε (r ≫ q) z j j' := by
  simp only [trF, Category.assoc]

theorem exists_sec_descend : ∀ {X B H : Scheme.{0}} (L : LB X), L.IsLB → ∀ (q : H ⟶ B), Flat q → Surjective q → QuasiCompact q → ∀ {K : Type} [Fintype K] (ψ : K → (B ⟶ X)) (ε : K → ℤ) (σ : LB.Sec (LB.LinComb L (fun k => q ≫ ψ k) ε)), (∀ (S : Type) [CommRing S] [IsLocalRing S] (g₁ g₂ : Sp S ⟶ H), g₁ ≫ q = g₂ ≫ q → ∀ J, Good L (closedPoint S) J → sval σ g₁ (closedPoint S) J = sval σ g₂ (closedPoint S) J) → ∃ b : LB.Sec (LB.LinComb L ψ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) J, Good L z J → sval σ r z J = sval b (r ≫ q) z J := by
  intro X B H L hL q _ _ _ K _ ψ ε σ hσ
  have le : ∀ j : K → L.ι, q ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun a => q ≫ ψ a) j :=
    fun j y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  have desc : ∀ j : K → L.ι, ∃ a : Γ(B, LB.wchart L ψ j),
      (q.app _).hom a = (H.presheaf.map (homOfLE (le j)).op).hom (σ.f j) := by
    intro j
    refine FunDescent.exists_app_eq q _ _ fun Z g₁ g₂ h₁ h₂ hq => fn_ext fun z _ => ?_
    rw [gs_appLE_top, gs_appLE_top]
    refine gs_eq_of_local g₁ g₂ z _ (h₁ trivial) (h₂ trivial) _ ?_
    have key : ∀ (S : Type) [CommRing S] [IsLocalRing S] (k₁ k₂ : Sp S ⟶ H), k₁ ≫ q = k₂ ≫ q →
        k₁ (closedPoint S) ∈ q ⁻¹ᵁ LB.wchart L ψ j → k₂ (closedPoint S) ∈ q ⁻¹ᵁ LB.wchart L ψ j →
        gs k₁ (closedPoint S) _ ((H.presheaf.map (homOfLE (le j)).op).hom (σ.f j)) =
        gs k₂ (closedPoint S) _ ((H.presheaf.map (homOfLE (le j)).op).hom (σ.f j)) := by
      intro S _ _ k₁ k₂ hk hz' hz
      choose J hJ using fun χ : Sp S ⟶ X => exists_chart hL (χ (closedPoint S))
      have hJ' : Good L (Z := Sp S) (closedPoint S) J := hJ
      refine (gs_res _ _ (le j) hz' _).trans (Eq.trans ?_ (gs_res _ _ (le j) hz _).symm)
      refine (sec_trans σ _ _ (le j hz') (hJ'.mem _ _)).trans
        (Eq.trans ?_ (sec_trans σ _ _ (le j hz) (hJ'.mem _ _)).symm)
      refine congrArg₂ (· * ·) (congrArg Units.val ?_) (hσ S k₁ k₂ hk J hJ')
      refine (trF_comp _ _ _ _ _ _ _).trans (Eq.trans ?_ (trF_comp _ _ _ _ _ _ _).symm)
      simp only [← Category.assoc, hk]
    exact @key (Z.presheaf.stalk z) _ (Z.toLocallyRingedSpace.isLocalRing z)
      (Z.fromSpecStalk z ≫ g₁) (Z.fromSpecStalk z ≫ g₂)
      ((Category.assoc _ _ _).trans ((congrArg (Z.fromSpecStalk z ≫ ·) hq).trans (Category.assoc _ _ _).symm))
      (h₁ trivial) (h₂ trivial)
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z), q (r z) ∈ LB.wchart L ψ j →
      gs (r ≫ q) z (LB.wchart L ψ j) (a j) =
        gs r z (LB.wchart L (fun a => q ≫ ψ a) j) (σ.f j) := fun j Z r z hz =>
    (gs_pull r _ z _ hz _).symm.trans ((congrArg (gs r z _) (ha j)).trans (gs_res r z (le j) hz _))
  refine ⟨⟨a, fun j j' => FunDescent.app_injective q (LB.wchart L ψ j ⊓ LB.wchart L ψ j')
    (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ => ?_⟩
  · have hy' : q y ∈ LB.wchart L ψ j ⊓ LB.wchart L ψ j' := hy
    refine (gs_pull (𝟙 _) q y _ hy' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) q y _ hy' _).symm)
    refine ((gs_res (𝟙 _ ≫ q) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (sec_trans σ (𝟙 _) y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (gs_mul (𝟙 _ ≫ q) y _ hy' _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 _ ≫ q) y _ hy' _).trans (congrArg Units.val
        ((gm_linComb L ψ ε (𝟙 _ ≫ q) y j j' hy'.1 hy'.2).trans (trF_comp _ _ _ _ _ _ _).symm)))
      ((gs_res (𝟙 _ ≫ q) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  · refine Eq.symm ?_
    rw [sval_of _ (r ≫ q) z J (fun a => J (r ≫ q ≫ ψ a)) (fun a => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun a => hJ (r ≫ q ≫ ψ a))

end GlobalTheory.LocDescent
end
