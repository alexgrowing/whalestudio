import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isGen_pull {X Y : Scheme.{0}} (M : LB X) (v : LB.Gen M) (hv : v.IsGen) (f : Y ⟶ X) :
    ∃ c : LB.Gen (M.pull f), c.IsGen := by
  have le : ∀ J : PUnit → M.ι, (M.pull f).U J ≤ f ⁻¹ᵁ M.U (J PUnit.unit) := fun J y hy => mem_pull.1 hy
  refine ⟨⟨fun J => res (le J) (pullU f _ (v.s (J PUnit.unit)))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J : PUnit → M.ι, y ∈ (M.pull f).U J →
      gm (𝟙 Y) y _ (res (le J) (pullU f _ (v.s (J PUnit.unit)))) =
        gm (𝟙 Y ≫ f) y _ (v.s (J PUnit.unit)) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  have hm : (𝟙 Y ≫ f) y ∈ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) := ⟨le J hy.1, le J' hy.2⟩
  have e := congrArg (gm (𝟙 Y ≫ f) y _) (hv (J PUnit.unit) (J' PUnit.unit))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at e
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))

theorem exists_isGen_of_invariant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y'))
    (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, φ' k = m ≫ φ k)
    (u : LB.Gen (LB.LinComb L φ' ε)) (hu : u.IsGen)
    (hinv : ∀ i y J, Good L y J → val u (t i) y J = val u (𝟙 Y') y J) :
    ∃ v : LB.Gen (LB.LinComb L φ ε), v.IsGen := by
  obtain rfl : φ' = fun k => m ≫ φ k := funext hφ
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have hunit : ∀ (U : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ U)ˣ),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), res e (pullU (t i) _ a) = a) →
      ∃ b : Γ(Y, U)ˣ, pullU m U b = a := by
    intro U a ha
    obtain ⟨g, hg, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨g', hg', -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (t i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have h1 : g * g' = 1 := hinj U (by rw [map_mul, map_one, hg, hg']; exact a.mul_inv)
    exact ⟨⟨g, g', h1, (mul_comm _ _).trans h1⟩, Units.ext hg⟩
  have le : ∀ j : K → L.ι, m ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => m ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hex : ∀ j : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ j)ˣ, pullU m _ b = res (le j) (u.s j) := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    have hJ' : Good L y J := hJ
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ LB.wchart L φ j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    refine (gm_res (t i) y (le j) (e hy) _).trans (Eq.trans ?_ (gm_res (𝟙 Y') y (le j) hy _).symm)
    refine (gen_trans hu (t i) y (le j (e hy)) (hJ'.mem _ _)).trans
      (Eq.trans ?_ (gen_trans hu (𝟙 Y') y (le j hy) (hJ'.mem _ _)).symm)
    refine congrArg₂ (· * ·) ?_ (hinv i y J hJ')
    have e3 : ∀ k, t i ≫ m ≫ φ k = 𝟙 Y' ≫ m ≫ φ k := fun k => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X => gm ψ y (L.U (j k) ⊓ L.U (J ψ)) (L.g (j k) (J ψ)) ^ ε k) (e3 k)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j : K → L.ι, y ∈ m ⁻¹ᵁ LB.wchart L φ j →
      gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (u.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans ((congrArg _ (hb j)).trans (gm_res (𝟙 Y') y (le j) hj _))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans
    ((gen_trans hu (𝟙 Y') y (le i hy.1) (le j hy.2)).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_linComb L φ ε (𝟙 Y' ≫ m) y i j hy.1 hy.2).trans ?_) ((gm_res _ y _ hy _).trans (val j hy.2)))
  simp only [trF, Category.assoc]

theorem weilNondeg_of_descent :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 → ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤ ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)), (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε)))) → WeilNondegSt := by
  intro hG hC K _ _ P k hk x hx hy
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨u, ε, hu, -, hcorr⟩ := hC K P k x hx
  let B := baseOver (Spec (CommRingCat.of K))
  let β : P.A ⟶ B := Over.homMk P.A.hom (Category.comp_id _)
  have hβ : ∀ {T : Over (Spec (CommRingCat.of K))} (a b : T ⟶ B), a = b := fun a b =>
    Over.OverMorphism.ext (((Category.comp_id _).symm.trans (Over.w a)).trans
      ((Category.comp_id _).symm.trans (Over.w b)).symm)
  let σ : P.A ⟶ B ⊗ P.A := lift β (𝟙 _)
  have hσ : snd B P.A ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hβ _ _
    · simp [σ]
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ P.A), y ≫ mulA P.A k = y ^ k :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  have h0 : σ ≫ mulT P.A B k = mulA P.A k ≫ σ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hβ _ _
    · simp [σ, mulT, mulA, MonObj.comp_pow]
  obtain ⟨v, hv⟩ := exists_isGen_of_invariant P.isLB (K := Fin 2)
    ![(σ ≫ translPt P.A x).left, 𝟙 _] ![1, -1] (mulA P.A k).left
    (I := {y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A // y ^ k = 1})
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, hmul, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul, mulA])
    (fun U f hf => hG K P k hk U f fun y hy => hf ⟨y, hy⟩) _
    (fun i => by
      fin_cases i
      · change (σ ≫ mulT P.A B k ≫ translPt P.A x).left = (mulA P.A k ≫ σ ≫ translPt P.A x).left
        rw [reassoc_of% h0]
      · change (σ ≫ snd B P.A ^ k).left = (mulA P.A k ≫ 𝟙 _).left
        simp [σ, mulA, MonObj.comp_pow])
    (LB.pullGen P.L _ _ u σ.left) (DVR.pullGen_isGen _ _ _ u hu _)
    (fun y z J hJ => by
      have hy' : (toUnit B ≫ y.1) ^ k = 1 := by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      have h1 := val_corr hJ (hcorr _ 1 hy' (hy _ hy')) σ.left
      have h2 : ((toUnit P.A ≫ y.1) * 𝟙 P.A) ≫ σ = σ ≫ translT P.A (toUnit B ≫ y.1) := by
        apply CartesianMonoidalCategory.hom_ext
        · exact hβ _ _
        · clear hG hC hcorr h1
          simp only [σ, translT, translPt, Hom.mul_def, Category.assoc, lift_snd, Category.comp_id,
            comp_lift_assoc, lift_fst_assoc, comp_toUnit_assoc]
      rw [val_pull hJ, val_mul hJ, one_zpow] at h1
      rw [val_pull hJ, val_pull hJ, Category.id_comp, ← Over.comp_left, h2]
      refine h1.trans ?_
      refine mul_eq_left.2 ?_
      exact (congrArg _ ((congrArg _ (map_one _)).trans (map_one _))).trans (map_one _))
  refine P.ktriv K (𝟙 _) x fun p => ⟨⊤, trivial, ?_⟩
  have h3 : (fun i => (snd B P.A).left ≫ ![(σ ≫ translPt P.A x).left, 𝟙 _] i) =
      ![(translPt P.A x).left, (snd B P.A).left] := by
    funext i
    fin_cases i
    · change (snd B P.A ≫ σ ≫ translPt P.A x).left = (translPt P.A x).left
      rw [reassoc_of% hσ]
    · exact Category.comp_id _
  have h4 : ∃ w : LB.Gen (LB.LinComb P.L
      (fun i => (snd B P.A).left ≫ ![(σ ≫ translPt P.A x).left, 𝟙 _] i) ![1, -1]), w.IsGen :=
    ⟨_, DVR.pullGen_isGen _ _ _ v hv _⟩
  rw [h3] at h4
  obtain ⟨w, hw⟩ := h4
  exact exists_isGen_pull (translDiff P.A P.L x) w hw _

end GlobalTheory
