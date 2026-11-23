import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxTheta

section Box

variable {X X' Y Y' Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem bw_trans {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z)
    {jN jN' : Fin j → M.ι} {k k' : M'.ι} (h : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k)
    (h' : ψ z ∈ LB.wchart M pr jN' ⊓ M'.U k') :
    bw w ψ z jN k = (∏ i, gm (ψ ≫ pr i) z (M.U (jN i) ⊓ M.U (jN' i)) (M.g (jN i) (jN' i))) *
      (gm ψ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * bw w ψ z jN' k' := by
  have hm : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k') := ⟨h, h'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k'))) (hw (jN, k) (jN', k'))
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (jN, k) (jN', k') hm).trans (congrArg₂ (· * ·) ?_ rfl))
    (gm_res ψ z _ hm _))))
  refine (gm_linComb M pr (fun _ => 1) ψ z jN jN' h.1 h'.1).trans ?_
  simp only [zpow_one]

theorem exists_box_ratio (hM : M.IsLB) (hM' : M'.IsLB) {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen)
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y' ⟶ Y)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (ht' : t'.IsGen)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    ∃ c : Γ(Y', ⊤)ˣ, ∀ (y : Y') (J J'), Good M y J → Good M' y J' →
      (∏ a, bw w (φ' a) y (fun i => J (φ' a ≫ pr i)) (J' (φ' a)) ^ ε a) * val t' (𝟙 _) y J' =
        gm (𝟙 _) y ⊤ c * ∏ i, val (t i) (ρ i) y J := by
  let W : (K → Fin j → M.ι) × (K → M'.ι) → Y'.Opens := fun p =>
    LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' p.1 ⊓ LB.wchart M' φ' p.2
  have le : ∀ p i, W p ≤ ρ i ⁻¹ᵁ LB.wchart M (φ i) (fun a => p.1 a i) := fun p i y hy =>
    Set.mem_iInter.2 fun a => (congrArg (fun q => q y ∈ M.U (p.1 a i)) (hψ i a)).mp
      (Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 a) i)
  obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(Y', W p)ˣ, ∀ p y, y ∈ W p → gm (𝟙 Y') y (W p) (u p) =
      (∏ a, bw w (φ' a) y (p.1 a) (p.2 a) ^ ε a) * gm (𝟙 Y') y (LB.wchart M' φ' p.2) (t'.s p.2) *
        (∏ i, gm (ρ i) y (LB.wchart M (φ i) (fun a => p.1 a i)) ((t i).s (fun a => p.1 a i)))⁻¹ := by
    refine ⟨fun p => @id (Γ(Y', W p)ˣ) ((LB.linCombIso w φ' ε).s p) * res inf_le_right (t'.s p.2) *
      (∏ i, res (le p i) (pullU (ρ i) _ ((t i).s (fun a => p.1 a i))))⁻¹, fun p y hy => ?_⟩
    have E₁ := gm_linCombIso w φ' ε (𝟙 Y') y p.1 p.2 hy
    simp only [Category.id_comp] at E₁
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) E₁
      (gm_res (𝟙 Y') y inf_le_right hy _))) ((map_inv _ _).trans (congrArg (·⁻¹) ((map_prod _ _ _).trans
      (Finset.prod_congr rfl fun i _ => gm_rp₁ (ρ i) y _ _ (le p i) hy _)))))
  obtain ⟨c, hc⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
      choose I' hI' using fun χ : Y' ⟶ X' => exists_chart hM' (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun a i => I (φ' a ≫ pr i), fun a => I' (φ' a)),
        Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hI (φ' a ≫ pr i), Set.mem_iInter.2 fun a => hI' (φ' a)⟩) u
    (fun p q y hy => by
      have b : ∀ a, bw w (φ' a) y (p.1 a) (p.2 a) = _ := fun a => bw_trans hw (φ' a) y (jN' := q.1 a) (k' := q.2 a)
        ⟨Set.mem_iInter.1 hy.1.1 a, Set.mem_iInter.1 hy.1.2 a⟩ ⟨Set.mem_iInter.1 hy.2.1 a, Set.mem_iInter.1 hy.2.2 a⟩
      have g' := gen_trans ht' (𝟙 Y') y hy.1.2 hy.2.2
      have g := fun i => gen_trans (ht i) (ρ i) y (le p i hy.1) (le q i hy.2)
      rw [hu p y hy.1, hu q y hy.2, g']
      simp only [b, g, trF, hψ, Category.id_comp, mul_zpow, Finset.prod_mul_distrib, inv_zpow, Finset.prod_inv_distrib,
        ← Finset.prod_zpow]
      rw [Finset.prod_comm]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨c, fun y J J' hJ hJ' => ?_⟩
  have hy : y ∈ W (fun a i => J (φ' a ≫ pr i), fun a => J' (φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ (φ' a ≫ pr i), Set.mem_iInter.2 fun a => hJ' (φ' a)⟩
  have e := (gm_res (𝟙 Y') y le_top hy c).symm.trans ((congrArg (gm (𝟙 Y') y _) (hc _)).trans (hu _ y hy))
  rw [e, val_of t' _ y J' (fun a => J' (φ' a)) (fun a => by rw [Category.id_comp])]
  simp only [fun i => val_of (t i) (ρ i) y J (fun a => J (φ' a ≫ pr i)) (fun a => congrArg J (hψ i a).symm),
    inv_mul_cancel_right]

theorem exists_gen_of_section (N : LB Y) (f : Y' ⟶ Y) (g : Y ⟶ Y') (hg : g ≫ f = 𝟙 Y) (c : LB.Gen (N.pull f))
    (hc : c.IsGen) : ∃ t : LB.Gen N, t.IsGen := by
  have le : ∀ i, N.U i ≤ g ⁻¹ᵁ (N.pull f).U (fun _ => i) := fun i y hy =>
    mem_pull.2 ((congrArg (fun q => q y ∈ N.U i) hg).mpr hy)
  refine ⟨⟨fun i => res (le i) (pullU g _ (c.s fun _ => i))⟩, fun i i' => unit_ext fun y hy => ?_⟩
  have e := gen_trans (L := N) (φ := fun _ : PUnit.{1} => f) (ε := fun _ => 1) hc g y (le i hy.1) (le i' hy.2)
  rw [trF, Fintype.prod_unique, zpow_one, hg] at e
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_rp₁ g y _ _ (le i) hy.1 _)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res (𝟙 Y) y _ hy _).trans (gm_rp₁ g y _ _ (le i') hy.2 _)))

end Box

section Theta

variable {S : Scheme.{0}}

theorem act_val {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T)
    (s s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => k)))
    (h : IsActOf A L k θ s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    sval s' r z J = (val (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k])
      θ.φ r z J).val * sval s (r ≫ (translT A θ.pt).left) z J := by
  have hm := hJ.mem (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] r
  have e := congrArg (gs r z _) (h (fun a => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] a)))
  have l := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _)
    (fun a => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] a))
  rw [sval_of s (r ≫ (translT A θ.pt).left) z J (fun _ => J (r ≫ (translPt A θ.pt).left)) (fun _ => by
    rw [Category.assoc, ← Over.comp_left, translT, lift_snd])]
  exact (gs_res r z _ hm _).symm.trans (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hm _)
    ((gs_res r z l hm _).trans (gs_pull r (translT A θ.pt).left z
      (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ (translPt A θ.pt).left))) (l hm) _)))))

theorem exists_theta (hK : KerPowSt) [IsLocallyNoetherian S] (P : PolAV S) {k : ℕ} (hk : 1 ≤ k) {T : Over S}
    [Subsingleton T.left] [Nonempty T.left] (x : T ⟶ P.A) (hx : x ^ k = 1) :
    ∃ θ : ThetaGrp P.A P.L (k : ℤ) T, θ.pt = x := by
  obtain ⟨p⟩ := ‹Nonempty T.left›
  obtain ⟨V, hV, c, hc⟩ := (hK S P k hk T x).2 hx p
  have hr : Set.range (𝟙 (T ⊗ P.A).left : (T ⊗ P.A).left ⟶ _) ⊆ Set.range ((fst T P.A).left ⁻¹ᵁ V).ι := by
    intro y _
    exact ⟨⟨y, show (fst T P.A).left y ∈ V from Subsingleton.elim p ((fst T P.A).left y) ▸ hV⟩, rfl⟩
  obtain ⟨t, ht⟩ := exists_gen_of_section _ _ (IsOpenImmersion.lift _ _ hr) (IsOpenImmersion.lift_fac _ _ hr) c hc
  exact ⟨⟨x, t, ht⟩, rfl⟩

theorem surj_fst (hG : GlobalFnsSt) {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  rw [← lift_snd (snd T A) (fst T A), Over.comp_left]
  refine surj_comp (fun a => ⟨(lift (snd A T) (fst A T)).left.appTop.hom a, ?_⟩) (surj_snd hG hA T)
  have e : (lift (snd T A) (fst T A)).left ≫ (lift (snd A T) (fst A T)).left = 𝟙 _ := by
    rw [← Over.comp_left, comp_lift, lift_snd, lift_fst, lift_fst_snd]; rfl
  have := congrArg (fun q => (Scheme.Hom.appTop q).hom a) e
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_appTop,
    CommRingCat.hom_id, RingHom.id_apply] using this

theorem translPt_hom {A A' T : Over S} [GrpObj A] [GrpObj A'] (f : A' ⟶ A) [IsMonHom f] (x : T ⟶ A') :
    translPt A' x ≫ f = T ◁ f ≫ translPt A (x ≫ f) := by
  show (fst T A' ≫ x * snd T A') ≫ f = T ◁ f ≫ (fst T A ≫ x ≫ f * snd T A)
  rw [MonObj.mul_comp, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, Category.assoc]

theorem translT_hom {A A' T : Over S} [GrpObj A] [GrpObj A'] (f : A' ⟶ A) [IsMonHom f] (x : T ⟶ A') :
    translT A' x ≫ T ◁ f = T ◁ f ≫ translT A (x ≫ f) := by
  rw [translT, translT, lift_whiskerLeft, comp_lift, whiskerLeft_fst, translPt_hom]

theorem box_act (hG : GlobalFnsSt) {j : ℕ} {A A' : PolAV S} (pA : IsPowPolAV A' A j) {T : Over S} (k : ℕ)
    (θ' : ThetaGrp A'.A A'.L (k : ℤ) T) (θ : Fin j → ThetaGrp A.A A.L (k : ℤ) T)
    (hθ : ∀ i, (θ i).pt = θ'.pt ≫ pA.pr i) :
    ∃ c : Γ(T.left, ⊤), IsUnit ((fst T A'.A).left.appTop.hom c) ∧
      ∀ (t u : Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd T A.A).left) (fun _ => (k : ℤ))))
        (t' u' t'' : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd T A'.A).left) (fun _ => (k : ℤ)))),
        (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A'.A).left) (z : Z) (J J'), Good A.L z J → Good A'.L z J' →
          (bw pA.w (r ≫ (snd T A'.A).left) z (fun i => J ((r ≫ (snd T A'.A).left) ≫ (pA.pr i).left))
            (J' (r ≫ (snd T A'.A).left)) ^ k).val * sval t' r z J' = ∏ i, sval (t i) (r ≫ (T ◁ pA.pr i).left) z J) →
        (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A'.A).left) (z : Z) (J J'), Good A.L z J → Good A'.L z J' →
          (bw pA.w (r ≫ (snd T A'.A).left) z (fun i => J ((r ≫ (snd T A'.A).left) ≫ (pA.pr i).left))
            (J' (r ≫ (snd T A'.A).left)) ^ k).val * sval u' r z J' = ∏ i, sval (u i) (r ≫ (T ◁ pA.pr i).left) z J) →
        (∀ i, IsActOf A.A A.L (k : ℤ) (θ i) (t i) (u i)) → IsActOf A'.A A'.L (k : ℤ) θ' t' t'' →
        ∀ jj, t''.f jj = liftFun A'.A _ c * u'.f jj := by
  have hP : ∀ i, translPt A'.A θ'.pt ≫ pA.pr i = T ◁ pA.pr i ≫ translPt A.A (θ i).pt := fun i => by
    haveI := pA.hom i
    rw [hθ, translPt_hom]
  have hT : ∀ i, (translT A'.A θ'.pt).left ≫ (T ◁ pA.pr i).left = (T ◁ pA.pr i).left ≫ (translT A.A (θ i).pt).left :=
    fun i => by
      haveI := pA.hom i
      rw [hθ, ← Over.comp_left, translT_hom, Over.comp_left]
  obtain ⟨a, ha⟩ := exists_box_ratio (pr := fun i => (pA.pr i).left) A.isLB A'.isLB pA.w_gen (K := Fin 2)
    (φ' := ![(snd T A'.A).left, (translPt A'.A θ'.pt).left])
    (φ := fun i => ![(snd T A.A).left, (translPt A.A (θ i).pt).left]) (ε := ![(k : ℤ), -(k : ℤ)])
    (ρ := fun i => (T ◁ pA.pr i).left) (fun i a => by
      fin_cases a
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T (pA.pr i)).symm
      · exact congrArg (fun q => q.left) (hP i)) θ'.φ θ'.isGen (fun i => (θ i).φ) (fun i => (θ i).isGen)
  obtain ⟨c, hc⟩ := surj_fst hG A'.isAb T a.val
  refine ⟨c, hc ▸ a.isUnit, fun t u t' u' t'' ht hu hA hA' jj => fn_ext fun y hy => ?_⟩
  obtain ⟨J', hJ', eJ⟩ := exists_good A'.L A'.isLB y (fun _ : Fin 1 => (snd T A'.A).left) jj
    (fun a b _ => congrArg jj (Subsingleton.elim a b)) (fun a => Set.mem_iInter.1 hy a)
  choose J hJ using fun χ : (T ⊗ A'.A).left ⟶ A.A.left => exists_chart A.isLB (χ y)
  have e₁ := ht _ (translT A'.A θ'.pt).left y J J' hJ hJ'
  have e₂ := hu _ (𝟙 _) y J J' hJ hJ'
  have e₃ := act_val θ' t' t'' hA' (𝟙 _) y hJ'
  have e₄ := fun i => act_val (θ i) (t i) (u i) (hA i) (T ◁ pA.pr i).left y hJ
  have e₅ := ha y J J' hJ hJ'
  have s₁ : (translT A'.A θ'.pt).left ≫ (snd T A'.A).left = (translPt A'.A θ'.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  rw [Fin.prod_univ_two] at e₅
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at e₅
  simp only [s₁, hT] at e₁
  simp only [Category.id_comp, e₄, Finset.prod_mul_distrib, ← Units.coe_prod] at e₂
  rw [Category.id_comp] at e₃
  have f₁ := sval_of t'' (𝟙 _) y J' jj (fun a => by rw [Category.id_comp]; exact eJ a)
  have f₂ := sval_of u' (𝟙 _) y J' jj (fun a => by rw [Category.id_comp]; exact eJ a)
  have f₃ : gs (𝟙 (T ⊗ A'.A).left) y _ (liftFun A'.A (LB.wchart A'.L (fun _ : Fin 1 => (snd T A'.A).left) jj) c) =
      (gm (𝟙 _) y ⊤ a).val := (gs_res (𝟙 _) y le_top hy _).trans ((congrArg _ hc).trans (gs_unit _ y ⊤ trivial a))
  refine f₁.symm.trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) f₃ f₂.symm)).symm)
  rw [← e₁, ← _root_.mul_assoc, ← Units.val_mul] at e₂
  rw [e₃, (Units.eq_inv_mul_iff_mul_eq _).2 e₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
  refine congrArg (fun v : ((T ⊗ A'.A).left.presheaf.stalk y)ˣ => v.val * _) ?_
  rw [eq_inv_mul_iff_mul_eq.2 e₅, eq_mul_inv_iff_mul_eq.2 e₅.symm]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Theta

theorem box_theta_act : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (θ' : ThetaGrp A'.A A'.L (k : ℤ) (TFK (R := R) F)), θ'.pt ^ k = 1 → ∃ (θ : Fin j → ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (c : F), c ≠ 0 ∧ (∀ i, (θ i).pt = θ'.pt ≫ pA.pr i) ∧ ∀ (t u : Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (t' u' t'' : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ)))), (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval t' r z J' = ∏ i, Geo.Tor.sval (t i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J) → (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval u' r z J' = ∏ i, Geo.Tor.sval (u i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J) → (∀ i, IsActOf A.A A.L (k : ℤ) (θ i) (t i) (u i)) → IsActOf A'.A A'.L (k : ℤ) θ' t' t'' → ∀ jj, t''.f jj = liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * u'.f jj := by
  intro hL R _ _ j A A' pA F _ _ k hk θ' hθ'
  haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  choose θ hθ using fun i => exists_theta hL.kerPow A hk (T := TFK (R := R) F) (θ'.pt ≫ pA.pr i) (by
    haveI := pA.hom i
    rw [← MonObj.pow_comp, hθ', MonObj.one_comp])
  obtain ⟨c, hc, H⟩ := box_act hL.globalFns pA k θ' θ hθ
  have e : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c) = c :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply c
  refine ⟨θ, (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c, fun h0 => ?_, hθ, ?_⟩
  · rw [h0, map_zero] at e
    rw [← e, map_zero] at hc
    obtain ⟨p⟩ := ‹Nonempty (TFK (R := R) F).left›
    have h1 := hc.map (((TFK (R := R) F) ⊗ A'.A).left.presheaf.germ ⊤ ((lift (𝟙 _) θ'.pt).left p) trivial).hom
    rw [map_zero] at h1
    exact not_isUnit_zero h1
  · rw [e]; exact H

end GlobalTheory.BoxTheta
