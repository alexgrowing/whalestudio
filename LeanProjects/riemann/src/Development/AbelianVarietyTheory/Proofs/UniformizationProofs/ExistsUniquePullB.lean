import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.PullSec

section General
variable {X X' W Y Y₂ : Scheme.{0}}

theorem sec_eq {M : LB X} {s t : LB.Sec M} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t; congr; funext i; exact h i

theorem exists_pullSec {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y₂ ⟶ X)} {φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (h : Y ⟶ Y₂) (hc : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  have h1 : (LB.oneGen L (Y := Y)).IsGen := fun i j =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨s', hs⟩ := exists_sec hL (φ' := φ') (ε' := ε) (fun U _ g => by
      refine ((Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) rfl (Fintype.prod_empty _)).trans
        (_root_.mul_one _))).trans ?_
      exact Finset.prod_congr rfl fun k _ => by rw [hc]; rfl) (pullMulSec s h (LB.oneGen L) h1)
  refine ⟨s', fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec s h _ h1 r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]

theorem exists_sec_of_iso {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) (y₀ : Y ⟶ W) (h : Y ⟶ Y₂) (a : Y ⟶ X') (b : Y₂ ⟶ X)
    (ha : y₀ ≫ F' = a) (hb : y₀ ≫ F = h ≫ b) (k : ℕ)
    (σ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => b) (fun _ => (k : ℤ)))) :
    ∃ t : LB.Sec (LB.LinComb L' (fun _ : Fin 1 => a) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι) (j : L'.ι), F (y₀ (r z)) ∈ L.U i → F' (y₀ (r z)) ∈ L'.U j →
        (gw w (r ≫ y₀) z i (fun _ => j)).val ^ k *
            gs r z (LB.wchart L' (fun _ : Fin 1 => a) (fun _ => j)) (t.f fun _ => j) =
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) := by
  subst ha
  have pw := (isGen_iff w).1 hw
  have pt : ∀ y : Y, b (h y) = F (y₀ y) := fun y => congrArg (fun g => g y) hb.symm
  have mb : ∀ (y : Y) (i : L.ι), F (y₀ y) ∈ L.U i → h y ∈ LB.wchart L (fun _ : Fin 1 => b) (fun _ => i) :=
    fun y i hi => Set.mem_iInter.2 fun _ => show b (h y) ∈ L.U i by rw [pt]; exact hi
  have tw : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i i' : L.ι) (j j' : L'.ι), F (y₀ (r z)) ∈ L.U i →
      F (y₀ (r z)) ∈ L.U i' → F' (y₀ (r z)) ∈ L'.U j → F' (y₀ (r z)) ∈ L'.U j' →
      ((gw w (r ≫ y₀) z i (fun _ => j))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) =
        (gm (r ≫ y₀ ≫ F') z (L'.U j ⊓ L'.U j') (L'.g j j') ^ (k : ℤ)).val *
          (((gw w (r ≫ y₀) z i' (fun _ => j'))⁻¹ ^ k).val *
            gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i')) (σ.f fun _ => i')) := by
    intro Z r z i i' j j' hi hi' hj hj'
    have e := pw Z (r ≫ y₀) z i i' (fun _ => j) (fun _ => j') hi hi' (mem_pull.2 hj) (mem_pull.2 hj')
    rw [gm_pull_g L' F' (r ≫ y₀) z (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')] at e
    rw [sec_trans σ (r ≫ h) z (mb _ i hi) (mb _ i' hi'), trF, Fintype.prod_unique, e, ← _root_.mul_assoc,
      ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    rw [Category.assoc r h b, ← hb, Category.assoc r y₀ F, Category.assoc r y₀ F', zpow_natCast, zpow_natCast,
      ← mul_pow, ← mul_pow]
    congr 1
    generalize gm (r ≫ y₀ ≫ F) z (L.U i ⊓ L.U i') (L.g i i') = P
    generalize gm (r ≫ y₀ ≫ F') z (L'.U j ⊓ L'.U j') (L'.g j j') = Q
    generalize gw w (r ≫ y₀) z i' (fun _ => j') = C
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ j : Fin 1 → L'.ι, ∃ s : Γ(Y, LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), F (y₀ (r z)) ∈ L.U i → F' (y₀ (r z)) ∈ L'.U (j 0) →
        gs r z _ s = ((gw w (r ≫ y₀) z i (fun _ => j 0))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) := by
    intro j
    obtain ⟨V, hV⟩ : ∃ V : L.ι → Y.Opens, ∀ i y, y ∈ V i ↔ F (y₀ y) ∈ L.U i ∧ F' (y₀ y) ∈ L'.U (j 0) :=
      ⟨fun i => y₀ ⁻¹ᵁ (F ⁻¹ᵁ L.U i) ⊓ y₀ ⁻¹ᵁ (F' ⁻¹ᵁ L'.U (j 0)), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, V i ≤ LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j := fun i y hy =>
      Set.mem_iInter.2 fun c => by rw [Subsingleton.elim c 0]; exact ((hV i y).1 hy).2
    have l₁ : ∀ i, V i ≤ y₀ ⁻¹ᵁ ((L.pull F).U (fun _ => i) ⊓ (L'.pull F').U (fun _ => j 0)) := fun i y hy =>
      ⟨mem_pull.2 ((hV i y).1 hy).1, mem_pull.2 ((hV i y).1 hy).2⟩
    have l₂ : ∀ i, V i ≤ h ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => b) (fun _ => i) := fun i y hy =>
      mb y i ((hV i y).1 hy).1
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y, V i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), r z ∈ V i →
        gs r z (V i) (u i) = ((gw w (r ≫ y₀) z i (fun _ => j 0))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) :=
      ⟨fun i => ((res (l₁ i) (pullU y₀ _ (w.s (fun _ => i, fun _ => j 0))))⁻¹ ^ k).val *
          (Y.presheaf.map (homOfLE (l₂ i)).op).hom ((h.app _).hom (σ.f fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans (congrArg Units.val
          ((map_pow _ _ _).trans (congrArg (· ^ k) ((map_inv _ _).trans (congrArg (·⁻¹)
            ((gm_res r z (l₁ i) hz _).trans (gm_pull r y₀ z _ (l₁ i hz) _))))))))
          ((gs_res r z (l₂ i) hz _).trans (gs_pull r h z _ (l₂ i hz) _)))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V (LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j)
      (fun i => homOfLE (l₀ i)) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL (F (y₀ y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hV i y).2 ⟨hi, Set.mem_iInter.1 hy 0⟩⟩) u
      (fun i i' => fn_ext (V := V i ⊓ V i') fun y hy => by
        have h₁ := (hV i y).1 hy.1
        have h₂ := (hV i' y).1 hy.2
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y i hy.1, hu _ _ y i' hy.2, tw _ (𝟙 Y) y i i' (j 0) (j 0) h₁.1 h₂.1 h₁.2 h₁.2,
          gm_self hL' (𝟙 Y ≫ y₀ ≫ F') y h₁.2, one_zpow, Units.val_one, _root_.one_mul])
    refine ⟨s, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ V i := (hV i _).2 ⟨h₁, h₂⟩
    exact (gs_res r z (l₀ i) hz s).symm.trans ((congrArg (gs r z (V i)) (hs i)).trans (hu Z r z i hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z i j hi hj => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL (F (y₀ y))
    have m : F' (y₀ y) ∈ L'.U (j 0) := Set.mem_iInter.1 hy.1 0
    have m' : F' (y₀ y) ∈ L'.U (j' 0) := Set.mem_iInter.1 hy.2 0
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L' _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (hs j _ (𝟙 Y) y i hi m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y i hi m')).symm)
    rw [Fin.prod_univ_one]
    exact tw _ (𝟙 Y) y i i (j 0) (j' 0) hi hi m m'
  · refine (congrArg _ (hs (fun _ => j) Z r z i hi hj)).trans ?_
    rw [← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
      Units.val_one, _root_.one_mul]

end General

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem existsUnique_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (σ : U.SecGT T k) :
    ∃! t, U.PullG F φ k σ t := by
  let y₀ : (TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left :=
    (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left
  have ih : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id]; rfl
  have hi : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id]; rfl
  have ha : y₀ ≫ U.gen.hom.left = (snd (TFK (R := R) F) A.A).left :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ih).trans (Category.comp_id _))
  have hcomm : ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ T.hom = (y₀ ≫ pullback.fst G.hom (jK R)) ≫ G.hom := by
    have e₁ : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    have e₂ : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w U.gen.inv
    have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ jK R) e₃).trans ?_)))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (y₀ ≫ ·) pullback.condition)).symm
    rw [← e₂]
    simp only [y₀, Category.assoc]
  let h : (TFK (R := R) F ⊗ A.A).left ⟶ (T ⊗ G).left := pullback.lift _ _ hcomm
  have h₁ : h ≫ (fst T G).left = (fst (TFK (R := R) F) A.A).left ≫ φ.left := pullback.lift_fst _ _ _
  have h₂ : h ≫ (snd T G).left = y₀ ≫ pullback.fst G.hom (jK R) := pullback.lift_snd _ _ _
  obtain ⟨t, ht⟩ := exists_sec_of_iso U.P.L.isLB A.isLB U.wA U.wA_gen y₀ h _ (snd T G).left ha h₂.symm k σ
  have key : U.PullG F φ k σ t := by
    intro Z rA y rG e₁ e₂ e₃ z JA JG hA hG
    obtain rfl : y = rA ≫ y₀ := by
      have := congrArg (· ≫ U.gen.inv.left) e₁
      simp only [Category.assoc, hi, Category.comp_id] at this
      exact this.symm
    obtain rfl : rG = rA ≫ h := by
      refine pullback.hom_ext (e₃.trans ?_) (e₂.trans ?_)
      · exact ((Category.assoc _ _ _).trans (congrArg (rA ≫ ·) h₁)).symm
      · exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (rA ≫ ·) h₂)).symm
    rw [sval_of (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) t rA z JA
        (fun _ => JA ((rA ≫ y₀) ≫ U.gen.hom.left)) (fun _ => congrArg JA e₁),
      sval_of σ (rA ≫ h) z JG (fun _ => JG ((rA ≫ y₀) ≫ pullback.fst G.hom (jK R))) (fun _ => congrArg JG e₂)]
    exact ht Z rA z _ _ (hG ((rA ≫ y₀) ≫ pullback.fst G.hom (jK R))) (hA ((rA ≫ y₀) ≫ U.gen.hom.left))
  refine ⟨t, key, fun t' key' => sec_eq fun j => sec_ext_val A.isLB (fun z JA hA => ?_) j⟩
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have e₁ : 𝟙 _ ≫ (snd (TFK (R := R) F) A.A).left = y₀ ≫ U.gen.hom.left := (Category.id_comp _).trans ha.symm
  have e₃ : h ≫ (fst T G).left = 𝟙 _ ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left := h₁.trans (Category.id_comp _).symm
  have := (key' _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).trans (key _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).symm
  rw [← Units.val_pow_eq_pow_val] at this
  exact (Units.mul_right_inj _).1 this

theorem existsUnique_pullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) :
    ∃! s, PullB D F φ k f s := by
  have hc : ∀ (α : D.X) (i : Fin 4), DegPre.famφ D F α i = (φ ▷ D.P.A).left ≫ famφT D T α i := fun α i => by
    have u : φ ▷ D.P.A ≫ toUnit (T ⊗ D.P.A) = toUnit _ := toUnit_unique _ _
    have a₀ : snd (TF (R := R) F) D.P.A = φ ▷ D.P.A ≫ snd T D.P.A := (whiskerRight_snd _ _).symm
    have a₂ : ∀ c : 𝟙_ _ ⟶ D.P.A, toUnit (DegPre.BF D F) ≫ c = φ ▷ D.P.A ≫ toUnit (T ⊗ D.P.A) ≫ c := fun c => by
      rw [← Category.assoc, u]
    fin_cases i
    · exact congrArg (fun q => q.left) a₀
    · exact congrArg (fun q => q.left) ((congrArg₂ (· * ·) a₀ (a₂ (D.c α))).trans (MonObj.comp_mul _ _ _).symm)
    · exact congrArg (fun q => q.left) (a₂ (D.c α))
    · exact congrArg (fun q => q.left) (a₂ η[D.P.A])
  choose s hs using fun α => exists_pullSec D.P.isLB (φ ▷ D.P.A).left (hc α) (f α)
  have key : PullB D F φ k f s := fun α z J hJ => (hs α _ (𝟙 _) z J hJ).trans (by rw [Category.id_comp])
  exact ⟨s, key, fun s' key' => funext fun α => sec_eq fun j => sec_ext_val D.P.isLB
    (fun z J hJ => (key' α z J hJ).trans (key α z J hJ).symm) j⟩

theorem pullEx : (AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (T : Over (Spec (CommRingCat.of V))) (φ : TF (R := V) F ⟶ T) (k : ℕ), (∀ σ, ∃! t, U.PullG F φ k σ t) ∧ ∀ f, ∃! s, PullB D F φ k f s) :=
  fun _ _ _ _ _ D _ _ _ _ U F _ _ _ φ k => ⟨existsUnique_pullG U F φ k, existsUnique_pullB D F φ k⟩

end GlobalTheory.UU.PullSec
end
