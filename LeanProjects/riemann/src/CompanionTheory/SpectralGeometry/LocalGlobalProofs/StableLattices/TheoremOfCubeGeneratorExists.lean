import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LinearCombinationGeneratorSectionExistsStatement
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.RigDescLink

variable {S : Scheme.{0}} {A X : Over S}

abbrev aH (A : Over S) {T X : Over S} (x : T ⟶ X) : A ⊗ T ⟶ A ⊗ X := lift (fst A T) (snd A T ≫ x)

abbrev zS (A : Over S) [GrpObj A] (T : Over S) : T ⟶ A ⊗ T := lift (1 : T ⟶ A) (𝟙 T)

theorem aH_comp {T T' : Over S} (v : T' ⟶ T) (x : T ⟶ X) : aH A v ≫ aH A x = aH A (v ≫ x) := by
  simp [aH, comp_lift]

theorem zS_aH [GrpObj A] {T : Over S} (x : T ⟶ X) : zS A T ≫ aH A x = x ≫ zS A X := by
  simp [aH, zS, comp_lift]

theorem zS_left_snd [GrpObj A] (T : Over S) : (zS A T).left ≫ (snd A T).left = 𝟙 T.left := by
  rw [← Over.comp_left]; simp [zS]

def Normed [GrpObj A] (M : LB (A ⊗ X).left) (R : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => (zS A X).left) (fun _ => 1)))
    {T : Over S} (x x' : T ⟶ X) (l : LB.Gen (LB.LinComb M (K := Fin 2) ![(aH A x).left, (aH A x').left] ![-1, 1])) : Prop :=
  l.IsGen ∧ ∀ (Z : Scheme.{0}) (s : Z ⟶ T.left) (z : Z) (J : (Z ⟶ (A ⊗ X).left) → M.ι), Good M z J →
    val l (s ≫ (zS A T).left) z J = (val R (s ≫ x.left) z J)⁻¹ * val R (s ≫ x'.left) z J

variable [GrpObj A] {M : LB (A ⊗ X).left} {R : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => (zS A X).left) (fun _ => 1))}

theorem exists_normed (hM : M.IsLB) (hR : R.IsGen) {T : Over S} (x x' : T ⟶ X)
    (h : LBIso (ev M (fst A T) (snd A T ≫ x)) (ev M (fst A T) (snd A T ≫ x'))) : ∃ l, Normed M R x x' l := by
  have hc := (cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).2 h
  rw [cls_pull hM, cls_pull hM] at hc
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (LB.isLB_linComb hM ![(aH A x).left, (aH A x').left] ![-1, 1])).1 (by
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, one_smul]
    rw [← hc]; simp)
  have e₁ : ∀ y : T ⟶ X, (zS A T).left ≫ (aH A y).left = y.left ≫ (zS A X).left := fun y => by
    rw [← Over.comp_left, ← Over.comp_left, zS_aH]
  obtain ⟨t', ht', hv⟩ := GlobalTheory.T.linear_combination_generator_section_exists hM ![(aH A x).left, (aH A x').left] ![-1, 1]
    (Sum.elim (fun _ : PUnit => x.left ≫ (zS A X).left) (fun _ : PUnit => x'.left ≫ (zS A X).left))
    (Sum.elim (fun _ => -1) (fun _ => 1)) (snd A T).left (zS A T).left (zS_left_snd T)
    (fun U _ k => by
      rw [Fin.prod_univ_two, Fintype.prod_sum_type]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.prod_singleton, zpow_neg, zpow_one]) t ht
    (LB.mulGen M _ _ _ _ (LB.invGen M _ _ (LB.pullGen M _ _ R x.left)) (LB.pullGen M _ _ R x'.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hR _)) (DVR.pullGen_isGen _ _ _ _ hR _))
  refine ⟨t', ht', fun Z s z J hJ => ?_⟩
  rw [hv Z s z J hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ]

theorem normed_mul (hG : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hM : M.IsLB) {T : Over S} {x x' x'' : T ⟶ X}
    {l₁ l₂ l₃} (h₁ : Normed M R x x' l₁) (h₂ : Normed M R x' x'' l₂) (h₃ : Normed M R x x'' l₃)
    (Z : Scheme.{0}) (r : Z ⟶ (A ⊗ T).left) (z : Z) (J) (hJ : Good M z J) :
    val l₁ r z J * val l₂ r z J = val l₃ r z J := by
  rw [← val_mul hJ]
  refine gen_unique' hM (fun U _ k => ?_) (snd A T).left (zS A T).left (zS_left_snd T) (surj_snd hG hA T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁.1 h₂.1) h₃.1 (fun y I hI => ?_) Z r z J hJ
  · rw [Fin.prod_univ_two, Fintype.prod_sum_type]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl, Sum.elim_inr, zpow_neg, zpow_one]
    group
  · have a₁ := h₁.2 _ (𝟙 _) y I hI
    have a₂ := h₂.2 _ (𝟙 _) y I hI
    have a₃ := h₃.2 _ (𝟙 _) y I hI
    simp only [Category.id_comp] at a₁ a₂ a₃
    rw [val_mul hI, a₁, a₂, a₃]
    group

theorem normed_pull (hG : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hM : M.IsLB) {T T' : Over S} {x x' : T ⟶ X} {y y' : T' ⟶ X}
    (v : T' ⟶ T) (e : v ≫ x = y) (e' : v ≫ x' = y') {l l'} (h : Normed M R x x' l) (h' : Normed M R y y' l')
    (Z : Scheme.{0}) (r : Z ⟶ (A ⊗ T').left) (z : Z) (J) (hJ : Good M z J) :
    val l' r z J = val l (r ≫ (aH A v).left) z J := by
  subst e e'
  rw [← val_pull hJ]
  refine gen_unique' hM (fun U _ k => ?_) (snd A T').left (zS A T').left (zS_left_snd T') (surj_snd hG hA T')
    h'.1 (DVR.pullGen_isGen _ _ _ _ h.1 _) (fun w I hI => ?_) Z r z J hJ
  · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Over.comp_left, ← Over.comp_left, aH_comp, aH_comp]
  · have a₁ := h'.2 _ (𝟙 _) w I hI
    have a₂ := h.2 _ v.left w I hI
    simp only [Category.id_comp] at a₁
    have e₀ : (zS A T').left ≫ (aH A v).left = v.left ≫ (zS A T).left := by
      rw [← Over.comp_left, ← Over.comp_left, zS_aH]
    rw [val_pull hI, e₀, a₁, a₂]; rfl

section Descent

variable {Y : Over S} (q : X ⟶ Y)

omit [GrpObj A] in
theorem fst_eq {W : Over S} {a b : W ⟶ A ⊗ X} (h : a ≫ aH A q = b ≫ aH A q) : a ≫ fst A X = b ≫ fst A X := by
  have := congrArg (· ≫ fst A Y) h
  simpa [aH] using this

omit [GrpObj A] in
theorem snd_eq {W : Over S} {a b : W ⟶ A ⊗ X} (h : a ≫ aH A q = b ≫ aH A q) :
    (a ≫ snd A X) ≫ q = (b ≫ snd A X) ≫ q := by
  have := congrArg (· ≫ snd A Y) h
  simpa [aH] using this

omit [GrpObj A] in
theorem hom_eq {W : Scheme.{0}} {a b : W ⟶ (A ⊗ X).left} (h : a ≫ (aH A q).left = b ≫ (aH A q).left) :
    b ≫ (A ⊗ X).hom = a ≫ (A ⊗ X).hom := by
  rw [← Over.w (aH A q), ← Category.assoc, ← Category.assoc, h]

abbrev T₂ (A : Over S) {X Y : Over S} (q : X ⟶ Y) : Over S :=
  Over.mk (pullback.fst (aH A q).left (aH A q).left ≫ (A ⊗ X).hom)

abbrev P₁ (A : Over S) {X Y : Over S} (q : X ⟶ Y) : T₂ A q ⟶ A ⊗ X := Over.homMk (pullback.fst _ _) rfl

abbrev P₂ (A : Over S) {X Y : Over S} (q : X ⟶ Y) : T₂ A q ⟶ A ⊗ X :=
  Over.homMk (pullback.snd _ _) (hom_eq q pullback.condition)

omit [GrpObj A] in
theorem charpoly_eq_of_isIso : P₁ A q ≫ aH A q = P₂ A q ≫ aH A q := Over.OverMorphism.ext pullback.condition

abbrev sg (A : Over S) {X Y : Over S} (q : X ⟶ Y) : T₂ A q ⟶ A ⊗ T₂ A q := lift (P₁ A q ≫ fst A X) (𝟙 _)

omit [GrpObj A] in
theorem sg_one : sg A q ≫ aH A (P₁ A q ≫ snd A X) = P₁ A q := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [aH, sg]

omit [GrpObj A] in
theorem sg_two : sg A q ≫ aH A (P₂ A q ≫ snd A X) = P₂ A q := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa [aH, sg] using fst_eq q (charpoly_eq_of_isIso q)
  · simp [aH, sg]

abbrev pr {W : Over S} (a b : W ⟶ A ⊗ X) (h : a.left ≫ (aH A q).left = b.left ≫ (aH A q).left) : W ⟶ T₂ A q :=
  Over.homMk (pullback.lift a.left b.left h) (by
    show pullback.lift a.left b.left h ≫ pullback.fst _ _ ≫ (A ⊗ X).hom = W.hom
    rw [pullback.lift_fst_assoc]; exact Over.w a)

omit [GrpObj A] in
theorem pr_one {W : Over S} (a b : W ⟶ A ⊗ X) (h) : pr q a b h ≫ P₁ A q = a :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

omit [GrpObj A] in
theorem pr_two {W : Over S} (a b : W ⟶ A ⊗ X) (h) : pr q a b h ≫ P₂ A q = b :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

omit [GrpObj A] in
theorem pr_sg {W : Over S} (a b : W ⟶ A ⊗ X) (h) :
    lift (a ≫ fst A X) (𝟙 W) ≫ aH A (pr q a b h) = pr q a b h ≫ sg A q := by
  apply CartesianMonoidalCategory.hom_ext
  · have := pr_one q a b h
    simp only [aH, sg, comp_lift, lift_fst, Category.assoc, lift_snd_assoc, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, this]
  · simp [aH, sg]

theorem exists_c (hM : M.IsLB) {l : LB.Gen (LB.LinComb M (K := Fin 2)
      ![(aH A (P₁ A q ≫ snd A X)).left, (aH A (P₂ A q ≫ snd A X)).left] ![-1, 1])} (hl : l.IsGen) :
    ∃ c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst (aH A q).left (aH A q).left,
        pullback.snd (aH A q).left (aH A q).left] ![-1, 1]), c.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback (aH A q).left (aH A q).left) (z : Z) (J), Good M z J →
        val c r z J = val l (r ≫ (sg A q).left) z J := by
  obtain ⟨c, hc, hv⟩ := exists_gen hM (φ' := ![pullback.fst (aH A q).left (aH A q).left,
      pullback.snd (aH A q).left (aH A q).left]) (ε' := ![-1, 1]) (fun U _ k => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← Over.comp_left, ← Over.comp_left, sg_one, sg_two]; rfl)
    (LB.pullGen M _ _ l (sg A q).left) (DVR.pullGen_isGen _ _ _ _ hl _)
  exact ⟨c, hc, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem val_pr (hG : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hM : M.IsLB)
    {l : LB.Gen (LB.LinComb M (K := Fin 2)
      ![(aH A (P₁ A q ≫ snd A X)).left, (aH A (P₂ A q ≫ snd A X)).left] ![-1, 1])}
    (hl : Normed M R (P₁ A q ≫ snd A X) (P₂ A q ≫ snd A X) l) {W : Over S} (a b : W ⟶ A ⊗ X) (h)
    {l₀} (h₀ : Normed M R (a ≫ snd A X) (b ≫ snd A X) l₀) (w : W.left) (J) (hJ : Good M w J) :
    val l ((pr q a b h).left ≫ (sg A q).left) w J = val l₀ (lift (a ≫ fst A X) (𝟙 W)).left w J := by
  rw [normed_pull hG hA hM (pr q a b h) (by rw [← Category.assoc, pr_one]) (by rw [← Category.assoc, pr_two]) hl h₀ _ _ w J hJ,
    ← Over.comp_left, ← Over.comp_left, pr_sg]

end Descent

theorem descent_datum : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ (q : X ⟶ Y) (M : LB (A ⊗ X).left), M.IsLB →
    Triv (ev M (1 : X ⟶ A) (𝟙 X)) →
    (∀ (T : Over S) (x x' : T ⟶ X), x ≫ q = x' ≫ q →
        LBIso (ev M (fst A T) (snd A T ≫ x)) (ev M (fst A T) (snd A T ≫ x'))) →
    ∃ c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst (lift (fst A X) (snd A X ≫ q)).left (lift (fst A X) (snd A X ≫ q)).left,
        pullback.snd (lift (fst A X) (snd A X ≫ q)).left (lift (fst A X) (snd A X ≫ q)).left] ![-1, 1]), c.IsGen ∧
      ∀ (W : Scheme.{0}) (a b d : W ⟶ (A ⊗ X).left) (hab : a ≫ (lift (fst A X) (snd A X ≫ q)).left = b ≫ (lift (fst A X) (snd A X ≫ q)).left)
        (hbd : b ≫ (lift (fst A X) (snd A X ≫ q)).left = d ≫ (lift (fst A X) (snd A X ≫ q)).left) (w : W) (J : (W ⟶ (A ⊗ X).left) → M.ι), Good M w J →
        val c (pullback.lift a b hab) w J * val c (pullback.lift b d hbd) w J = val c (pullback.lift a d (hab.trans hbd)) w J := by
  intro S A X Y _ hA q M hM hT hyp
  obtain ⟨R, hR⟩ := hT
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨l, hl⟩ := exists_normed (A := A) hM hR (P₁ A q ≫ snd A X) (P₂ A q ≫ snd A X)
    (hyp _ _ _ (snd_eq q (charpoly_eq_of_isIso q)))
  obtain ⟨c, hc, hv⟩ := exists_c q hM hl.1
  refine ⟨c, hc, fun W a b d hab hbd w J hJ => ?_⟩
  let W₀ : Over S := Over.mk (a ≫ (A ⊗ X).hom)
  let a' : W₀ ⟶ A ⊗ X := Over.homMk a rfl
  let b' : W₀ ⟶ A ⊗ X := Over.homMk b (hom_eq q hab)
  let d' : W₀ ⟶ A ⊗ X := Over.homMk d ((hom_eq q hbd).trans (hom_eq q hab))
  have eab : a' ≫ aH A q = b' ≫ aH A q := Over.OverMorphism.ext hab
  have ebd : b' ≫ aH A q = d' ≫ aH A q := Over.OverMorphism.ext hbd
  obtain ⟨l₁, h₁⟩ := exists_normed (A := A) hM hR (a' ≫ snd A X) (b' ≫ snd A X) (hyp _ _ _ (snd_eq q eab))
  obtain ⟨l₂, h₂⟩ := exists_normed (A := A) hM hR (b' ≫ snd A X) (d' ≫ snd A X) (hyp _ _ _ (snd_eq q ebd))
  obtain ⟨l₃, h₃⟩ := exists_normed (A := A) hM hR (a' ≫ snd A X) (d' ≫ snd A X) (hyp _ _ _ (snd_eq q (eab.trans ebd)))
  have v₁ := (hv W _ w J hJ).trans (val_pr q hG hA hM hl a' b' hab h₁ w J hJ)
  have v₂ := (hv W _ w J hJ).trans (val_pr q hG hA hM hl b' d' hbd h₂ w J hJ)
  have v₃ := (hv W _ w J hJ).trans (val_pr q hG hA hM hl a' d' (hab.trans hbd) h₃ w J hJ)
  rw [← fst_eq q eab] at v₂
  exact (congrArg₂ (· * ·) v₁ v₂).trans ((normed_mul hG hA hM h₁ h₂ h₃ _ _ w J hJ).trans v₃.symm)

end GlobalTheory.CompanionTheory.RigDescLink
