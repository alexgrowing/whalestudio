import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiSpread

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_finite_cube_induction (X : Type) [AddCommGroup X] [Module.Finite ℤ X] :
    ∃ S : Set X, S.Finite ∧ ∀ E : X → Prop, (∀ x ∈ S, E x) →
      (∀ a a' b, E a → E a' → E b → E (a + a') → E (a + b) → E (a' + b) → E (a + a' + b)) → ∀ x, E x := by
  have h : AddMonoid.FG X := AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  obtain ⟨G, hG⟩ := h.fg_top
  refine ⟨insert 0 ((G : Set X) ∪ Set.image2 (· + ·) (G : Set X) G),
    (G.finite_toSet.union (G.finite_toSet.image2 _ G.finite_toSet)).insert _, fun E hS hE x => ?_⟩
  have h₁ : ∀ g ∈ (G : Set X), E g := fun g hg => hS g (Or.inr (Or.inl hg))
  have key : E x ∧ ∀ g ∈ (G : Set X), E (g + x) := by
    refine AddSubmonoid.induction_of_closure_eq_top_left (motive := fun x => E x ∧ ∀ g ∈ (G : Set X), E (g + x))
      hG x ⟨hS 0 (Or.inl rfl), fun g hg => by rw [add_zero]; exact h₁ g hg⟩ fun g hg y hy => ⟨hy.2 g hg, fun g' hg' => ?_⟩
    rw [← add_assoc]
    exact hE g' g y (h₁ _ hg') (h₁ _ hg) hy.1 (hS _ (Or.inr (Or.inr ⟨g', hg', g, hg, rfl⟩))) (hy.2 _ hg') (hy.2 _ hg)
  exact key.1

theorem exists_gen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (j : K → L.ι) (hj : ∀ y, y ∈ LB.wchart L φ j) (V : Y.Opens) (hV : ∀ y, y ∈ V) (u : Γ(Y, V)ˣ) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u := by
  let t : LB.Gen (LB.LinComb L φ ε) := ⟨fun j' =>
    res (le_inf le_rfl (fun y _ => hj y) : LB.wchart L φ j' ≤ LB.wchart L φ j' ⊓ LB.wchart L φ j)
      ((LB.LinComb L φ ε).g j' j) * res (fun y _ => hV y : LB.wchart L φ j' ≤ V) u⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u :=
    fun Z r z j' h => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ h _).trans (gm_linComb L φ ε r z j' j h (hj _))) (gm_res r z _ h _))
  refine ⟨t, fun (i i' : K → L.ι) => unit_ext fun y hy => ?_, key⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i hy.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y i i' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i' hy.2))).trans ?_)
  rw [← trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hj _), _root_.mul_assoc]
  rfl

theorem exists_unit_near {X Y : Scheme.{0}} (f : Y ⟶ X) [IsPreimmersion f] (y : Y) (a : (Y.presheaf.stalk y)ˣ) :
    ∃ (U : X.Opens) (u : Γ(X, U)ˣ), f y ∈ U ∧ gm f y U u = a := by
  obtain ⟨s, hs⟩ := f.stalkMap_surjective y a.val
  obtain ⟨U, hU, g, rfl⟩ := X.presheaf.exists_germ_eq s
  have hu : IsUnit ((X.presheaf.germ U (f y) hU).hom g) :=
    (isUnit_map_iff (f.stalkMap y).hom _).1 (hs ▸ a.isUnit)
  have hm : f y ∈ X.basicOpen g := (X.mem_basicOpen g (f y) hU).2 hu
  refine ⟨X.basicOpen g, (X.toRingedSpace.isUnit_res_basicOpen g).unit, hm, Units.ext ?_⟩
  refine (gs_unit f y _ hm _).symm.trans ((gs_res f y (X.basicOpen_le g) hm g).trans ((gs_eq f y U hU g).trans ?_))
  exact (Scheme.Hom.germ_stalkMap_apply f U y hU g).symm.trans hs

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def Extends {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (χ : D.X) : Prop :=
  ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (cP D T χ).left) (fun _ => -1)), t.IsGen ∧
    ∀ z J, Good D.P.L z J → val t κ.left z J = val (D.psi χ) (𝟙 _) z J

theorem exists_extends (χ : D.X) (z : (TK R).left) : ∃ V : (Spec (CommRingCat.of R)).Opens, jK R z ∈ V ∧
    ∀ W : (Spec (CommRingCat.of R)).Opens, W ≤ V → ∀ κ : TK R ⟶ TW W, Extends D κ χ := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R) (S := FractionRing R)
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  obtain ⟨j, hj⟩ := exists_chart D.P.isLB (D.xK χ z)
  obtain ⟨U, u, hU, e⟩ := exists_unit_near (jK R) z
    (gm (𝟙 (TK R).left) z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j)) ((D.psi χ).s (fun _ => j)))
  refine ⟨U ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U j, ⟨hU, hj⟩, fun W hW κ => ?_⟩
  have hκ : κ.left ≫ W.ι = jK R := Over.w κ
  obtain ⟨t, ht, vt⟩ := exists_gen_of_chart D.P.isLB (K := PUnit) (fun _ => (cP D (TW W) χ).left) (fun _ => -1)
    (fun _ => j) (fun y => Set.mem_iInter.2 fun _ => (hW y.2).2) (W.ι ⁻¹ᵁ U) (fun y => (hW y.2).1) (pullU W.ι U u)
  refine ⟨t, ht, fun z' J hJ => ?_⟩
  obtain rfl : z = z' := Subsingleton.elim _ _
  have q : κ.left ≫ (cP D (TW W) χ).left = 𝟙 _ ≫ D.xK χ :=
    (congrArg (fun q => q.left) (comp_cP D κ χ)).trans (Category.id_comp _).symm
  refine (vt _ κ.left z _ (hJ.mem _ _)).trans (Eq.trans ?_
    (gen_trans (D.psi_gen χ) (𝟙 _) z (j' := fun _ => j) (hJ.mem _ _) (Set.mem_iInter.2 fun _ => hj)).symm)
  refine congrArg₂ (· * ·) ?_ ((gm_pull κ.left W.ι z U (hW (κ.left z).2).1 u).trans (by rw [hκ]; exact e))
  exact congrArg (fun ψ => ∏ _k : PUnit.{1}, gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U j) (D.P.L.g (J ψ) j) ^ (-1 : ℤ)) q

theorem prod_elim {A U K K' : Type} [CommGroup U] [Fintype K] [Fintype K'] (h : A → U) {φ : K → A} {ε : K → ℤ}
    {φ' : K' → A} {ε' : K' → ℤ} {c c' : U} (e : ∏ k, h (φ k) ^ ε k = c) (e' : ∏ k, h (φ' k) ^ ε' k = c') :
    ∏ k, h (Sum.elim φ φ' k) ^ Sum.elim ε ε' k = c * c' := by
  rw [Fintype.prod_sum_type, ← e, ← e']; rfl

theorem prod_punit {A U : Type} [CommGroup U] (h : A → U) (a : A) (n : ℤ) :
    ∏ k : PUnit.{1}, h ((fun _ => a) k) ^ (fun _ => n) k = h a ^ n := Fintype.prod_unique _

theorem Extends.cube (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (a a' b : D.X)
    (h₁ : Extends D κ a) (h₂ : Extends D κ a') (h₃ : Extends D κ b) (h₄ : Extends D κ (a + a'))
    (h₅ : Extends D κ (a + b)) (h₆ : Extends D κ (a' + b)) : Extends D κ (a + a' + b) := by
  obtain ⟨t₁, g₁, v₁⟩ := h₁
  obtain ⟨t₂, g₂, v₂⟩ := h₂
  obtain ⟨t₃, g₃, v₃⟩ := h₃
  obtain ⟨t₄, g₄, v₄⟩ := h₄
  obtain ⟨t₅, g₅, v₅⟩ := h₅
  obtain ⟨t₆, g₆, v₆⟩ := h₆
  obtain ⟨t, gt, vt⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => (cP D T (a + a' + b)).left) (ε' := fun _ => -1)
    (fun U _ h => by
      have p := prod_cub (cP D T a) (cP D T a') (cP D T b) h
      have q : (toUnit T).left ≫ eSec D.P.A = (1 : T ⟶ D.P.A).left := rfl
      refine (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
        (prod_neg _ _ (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
          (prod_elim h (prod_punit h _ _) p)))).trans (Eq.trans ?_ (prod_punit h _ _).symm)
      rw [q]
      simp only [cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₄ t₅) t₆)
      (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₁ t₂) t₃)
        (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit T).left)
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (cP D T a) (lift (cP D T a') (cP D T b))).left)))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₄ g₅) g₆)
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₁ g₂) g₃)
        (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) (pullGen_isGen _ _ _ _ D.cub.isGen _)))))
  refine ⟨t, gt, fun z J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).trans (by simp only [comp_cP])
  have vρ : val (LB.pullGen D.P.L _ _ D.rig (toUnit T).left) κ.left z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]
    exact congrArg (fun q => val D.rig q z J) (Over.w κ)
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (cP D T a) (lift (cP D T a') (cP D T b))).left) κ.left z J = th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub κ hJ _ _ _).trans (by simp only [comp_cP])
  rw [c, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ] at e
  refine (vt _ _ z J hJ).trans (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (v₄ z J hJ) (v₅ z J hJ))) (v₆ z J hJ)))
    ((val_inv _ _).trans (congrArg (·⁻¹) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (v₁ z J hJ) (v₂ z J hJ))) (v₃ z J hJ)))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) vρ vc)))))))).trans ?_)
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) -e'

theorem nonempty_psiOn {W : (Spec (CommRingCat.of R)).Opens} (κ : TK R ⟶ TW W) (h : ∀ χ, Extends D κ χ) :
    Nonempty (PsiOn D W) := by
  choose t gt vt using h
  refine ⟨⟨t, gt, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  have c : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (t χ) κ.left) (D.psi χ) :=
    corr_of_val D.P.isLB fun z J hJ => (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; exact vt χ z J hJ)
  have q : (jK R ⁻¹ᵁ W).ι ≫ κ.left = jK R ∣_ W := by
    have hκ : κ.left ≫ W.ι = jK R := Over.w κ
    rw [← cancel_mono W.ι, morphismRestrict_ι, Category.assoc, hκ]
  have e := (val_pull hJ _ _ _).symm.trans (val_corr hJ c (jK R ⁻¹ᵁ W).ι)
  rw [q] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  rw [Category.id_comp, Category.id_comp]
  exact e

theorem exists_psiOn (hB : D.TauBimult) : ∃ W : (Spec (CommRingCat.of R)).Opens,
    genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨S, hS, ind⟩ := exists_finite_cube_induction D.X
  choose V hV ext using fun χ => exists_extends D χ z
  let W : (Spec (CommRingCat.of R)).Opens := ⟨⋂ χ ∈ S, V χ, hS.isOpen_biInter fun χ _ => (V χ).isOpen⟩
  have hz : jK R z ∈ W := Set.mem_iInter₂.2 fun χ _ => hV χ
  let κ : TK R ⟶ TW W := Over.homMk (IsOpenImmersion.lift W.ι (jK R) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact TauPull.jK_mem y W ⟨_, hz⟩)) (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨W, ?_, nonempty_psiOn D κ (ind _ (fun χ hχ => ext χ W (fun x hx => Set.mem_iInter₂.1 hx χ hχ) κ)
    (Extends.cube D hB κ))⟩
  exact ((genericPoint_spec (Spec (CommRingCat.of R))).mem_open_set_iff W.isOpen).2 ⟨_, trivial, hz⟩

end PsiSpread

theorem psiOnExists : PsiOnExistsSt := fun _ _ _ _ _ D => PsiSpread.exists_psiOn D.toPre D.tau_bimult

end GlobalTheory
