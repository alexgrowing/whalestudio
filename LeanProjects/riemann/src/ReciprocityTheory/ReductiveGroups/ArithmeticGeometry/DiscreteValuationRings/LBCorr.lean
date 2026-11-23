import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HasGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}

private lemma res_res_lemma {A : Scheme.{0}} {U V W : A.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (a : Γ(A, U)ˣ) : res h2 (res h1 a) = res (h2.trans h1) a := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  try rfl

private lemma res_eq_res_of_le_of_res_eq {A : Scheme.{0}} {U V V0 O : A.Opens} {a : Γ(A, U)ˣ} {b : Γ(A, V)ˣ}
    {p : V0 ≤ U} {q : V0 ≤ V} (h : res p a = res q b) (hO : O ≤ V0) (r : O ≤ U) (s : O ≤ V) :
    res r a = res s b := by
  have h' := congrArg (res hO) h
  rwa [res_res_lemma, res_res_lemma] at h'

private lemma pullU_res_eq_res_pullU' {A B : Scheme.{0}} (g : B ⟶ A) {U V : A.Opens} (h : V ≤ U)
    (a : Γ(A, U)ˣ) :
    pullU g V (res h a) = res (fun _ hy => h hy : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U) (pullU g U a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp]
  exact congrArg (fun φ => φ.hom (a : Γ(A, U))) (g.naturality (homOfLE h).op)

private lemma pullU_comp_lemma {A B C : Scheme.{0}} (g : B ⟶ A) (g' : C ⟶ B) {U : A.Opens}
    {O : C.Opens} (p : O ≤ g' ⁻¹ᵁ (g ⁻¹ᵁ U)) (q : O ≤ (g' ≫ g) ⁻¹ᵁ U) (x : Γ(A, U)ˣ) :
    res p (pullU g' _ (pullU g U x)) = res q (pullU (g' ≫ g) U x) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rfl

private lemma res_pullU_id' {A : Scheme.{0}} {U V : A.Opens} (h : V ≤ (𝟙 A) ⁻¹ᵁ U) (h' : V ≤ U)
    (x : Γ(A, U)ˣ) : res h (pullU (𝟙 A) U x) = res h' x := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rfl

private lemma res_pullU_eq_of_res_eq {A B : Scheme.{0}} (g : B ⟶ A) {U V V0 : A.Opens} {a : Γ(A, U)ˣ}
    {b : Γ(A, V)ˣ} {p : V0 ≤ U} {q : V0 ≤ V} (h : res p a = res q b) :
    res (fun _ hy => p hy : g ⁻¹ᵁ V0 ≤ g ⁻¹ᵁ U) (pullU g U a) =
      res (fun _ hy => q hy : g ⁻¹ᵁ V0 ≤ g ⁻¹ᵁ V) (pullU g V b) := by
  have h' := congrArg (pullU g V0) h
  rwa [pullU_res_eq_res_pullU', pullU_res_eq_res_pullU'] at h'

private lemma wchart_comp_inf_le_preimage_wchart_inf (g : Z ⟶ Y) (j : K → L.ι) (j' : K' → L.ι) :
    LB.wchart L (fun k => g ≫ φ k) j ⊓ LB.wchart L (fun k => g ≫ φ' k) j' ≤
      g ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun _ hx =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 k⟩

private lemma wchart_sumElim_inf_le_wchart_inl_inf (j : K ⊕ K₂ → L.ι) (j' : K' ⊕ K₂' → L.ι) :
    LB.wchart L (Sum.elim φ φ₂) j ⊓ LB.wchart L (Sum.elim φ' φ₂') j' ≤
      LB.wchart L φ (j ∘ Sum.inl) ⊓ LB.wchart L φ' (j' ∘ Sum.inl) := fun _ hx =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 (Sum.inl k),
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inl k)⟩

private lemma wchart_sumElim_inf_le_wchart_inr_inf (j : K ⊕ K₂ → L.ι) (j' : K' ⊕ K₂' → L.ι) :
    LB.wchart L (Sum.elim φ φ₂) j ⊓ LB.wchart L (Sum.elim φ' φ₂') j' ≤
      LB.wchart L φ₂ (j ∘ Sum.inr) ⊓ LB.wchart L φ₂' (j' ∘ Sum.inr) := fun _ hx =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 (Sum.inr k),
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inr k)⟩

private lemma gen_corr_self (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen.Corr L φ ε φ ε t t := by
  intro j j' _ _ hk
  obtain rfl : j = j' := funext fun k => hk k k rfl
  rfl

lemma res_eq_of_res_eq {U V W : Y.Opens} (a : Γ(Y, U)ˣ) (b : Γ(Y, V)ˣ) (h1 : W ≤ U) (h2 : W ≤ V)
    (h : res (inf_le_left : U ⊓ V ≤ U) a = res (inf_le_right : U ⊓ V ≤ V) b) :
    res h1 a = res h2 b := by
  exact res_eq_res_of_le_of_res_eq h (le_inf h1 h2) h1 h2

lemma corr_symm {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') : LB.Gen.Corr L φ' ε' φ ε t' t := by
  intro j' j hc' hc hk
  exact (res_eq_of_res_eq _ _ _ _ (h j j' hc hc' fun k k' e => (hk k' k e.symm).symm)).symm

lemma corr_pullGen {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') (g : Z ⟶ Y) :
    LB.Gen.Corr L _ ε _ ε' (LB.pullGen L φ ε t g) (LB.pullGen L φ' ε' t' g) := by
  intro j j' hc hc' hk
  have e0 := h j j' (fun k₁ k₂ e => hc k₁ k₂ (congrArg (g ≫ ·) e))
    (fun k₁ k₂ e => hc' k₁ k₂ (congrArg (g ≫ ·) e)) fun k k' e => hk k k' (congrArg (g ≫ ·) e)
  exact (res_res_lemma _ _ _).trans ((res_eq_res_of_le_of_res_eq (res_pullU_eq_of_res_eq g e0) (wchart_comp_inf_le_preimage_wchart_inf g j j') _ _).trans
    (res_res_lemma _ _ _).symm)

lemma corr_mulGen {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    {t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)} {t₂' : LB.Gen (LB.LinComb L φ₂' ε₂')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') (h₂ : LB.Gen.Corr L φ₂ ε₂ φ₂' ε₂' t₂ t₂') :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t t₂) (LB.mulGen L _ _ _ _ t' t₂') := by
  intro j j' hc hc' hk
  have e1 := h (j ∘ Sum.inl) (j' ∘ Sum.inl) (fun a b e => hc (Sum.inl a) (Sum.inl b) e)
    (fun a b e => hc' (Sum.inl a) (Sum.inl b) e) fun k k' e => hk (Sum.inl k) (Sum.inl k') e
  have e2 := h₂ (j ∘ Sum.inr) (j' ∘ Sum.inr) (fun a b e => hc (Sum.inr a) (Sum.inr b) e)
    (fun a b e => hc' (Sum.inr a) (Sum.inr b) e) fun k k' e => hk (Sum.inr k) (Sum.inr k') e
  refine (map_mul _ _ _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (res_res_lemma _ _ _).trans ((res_eq_res_of_le_of_res_eq e1 (wchart_sumElim_inf_le_wchart_inl_inf j j') _ _).trans
      (res_res_lemma _ _ _).symm)
  · exact (res_res_lemma _ _ _).trans ((res_eq_res_of_le_of_res_eq e2 (wchart_sumElim_inf_le_wchart_inr_inf j j') _ _).trans
      (res_res_lemma _ _ _).symm)

open scoped Classical in
lemma corr_trans (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} {t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)}
    {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ₂ ε₂ t t₂) (h' : LB.Gen.Corr L φ₂ ε₂ φ' ε' t₂ t') :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' hj hj' hm
  let ρ : ((Y ⟶ X) → L.ι) → (Y ⟶ X) → L.ι := fun ρ₀ ψ =>
    if h₁ : ∃ k, φ k = ψ then j h₁.choose else if h₃ : ∃ k', φ' k' = ψ then j' h₃.choose else ρ₀ ψ
  have hρ1 : ∀ ρ₀ k, ρ ρ₀ (φ k) = j k := fun ρ₀ k => by
    simp only [ρ, dif_pos (⟨k, rfl⟩ : ∃ k₀, φ k₀ = φ k)]
    exact hj _ _ (⟨k, rfl⟩ : ∃ k₀, φ k₀ = φ k).choose_spec
  have hρ3 : ∀ ρ₀ k', ρ ρ₀ (φ' k') = j' k' := fun ρ₀ k' => by
    simp only [ρ]
    split_ifs with h₁ h₃
    · exact hm _ _ h₁.choose_spec
    · exact hj' _ _ h₃.choose_spec
    · exact absurd ⟨k', rfl⟩ h₃
  set O := LB.wchart L φ j ⊓ LB.wchart L φ' j'
  apply units_ext_cover O (fun ρ₀ => O ⊓ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂)) (fun _ => inf_le_left)
  · intro y hy
    have hex : ∀ ψ : Y ⟶ X, ∃ i, ψ.base y ∈ L.U i := fun ψ => by
      have : ψ.base y ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this
    choose ρ₀ hρ₀ using hex
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨ρ₀, hy, Set.mem_iInter.2 fun k₂ => ?_⟩
    show (φ₂ k₂).base y ∈ L.U (ρ ρ₀ (φ₂ k₂))
    simp only [ρ]
    split_ifs with h₁ h₃
    · have := Set.mem_iInter.1 hy.1 h₁.choose
      rw [h₁.choose_spec] at this
      exact this
    · have := Set.mem_iInter.1 hy.2 h₃.choose
      rw [h₃.choose_spec] at this
      exact this
    · exact hρ₀ _
  · intro ρ₀
    have c2 : LB.Coh L φ₂ (ρ ρ₀ ∘ φ₂) := fun k₁ k₂ e => by simp only [Function.comp, e]
    have e1 := h j (ρ ρ₀ ∘ φ₂) hj c2 (fun k k₂ e => by simp only [Function.comp, ← e, hρ1])
    have e2 := h' (ρ ρ₀ ∘ φ₂) j' c2 hj' (fun k₂ k' e => by simp only [Function.comp, e, hρ3])
    have le1 : O ⊓ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂) ≤ LB.wchart L φ j := fun _ hy => hy.1.1
    have le2 : O ⊓ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂) ≤ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂) := fun _ hy => hy.2
    have le3 : O ⊓ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂) ≤ LB.wchart L φ' j' := fun _ hy => hy.1.2
    have f1 := res_eq_of_res_eq _ _ le1 le2 e1
    have f2 := res_eq_of_res_eq _ _ le2 le3 e2
    erw [res_res', res_res']
    exact f1.trans f2

lemma corr_refl (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : LB.Gen.Corr L φ ε φ ε t t := by
  exact gen_corr_self t

lemma shape_pull_mul (g : Z ⟶ Y) {U₁ U₂ W : Y.Opens} {Wz W₁ W₂ O Ow : Z.Opens}
    (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) (hz : Wz ≤ g ⁻¹ᵁ W) (hO : O ≤ Wz) (k₁ : W₁ ≤ g ⁻¹ᵁ U₁) (k₂ : W₂ ≤ g ⁻¹ᵁ U₂)
    (m₁ : Ow ≤ W₁) (m₂ : Ow ≤ W₂) (o : O ≤ Ow) (a : Γ(Y, U₁)ˣ) (b : Γ(Y, U₂)ˣ) :
    res hO (res hz (pullU g W (res h₁ a * res h₂ b))) =
      res o (res m₁ (res k₁ (pullU g U₁ a)) * res m₂ (res k₂ (pullU g U₂ b))) := by
  simp only [map_mul, pullU_res_eq_res_pullU', res_res_lemma]
  congr 1 <;> exact res_res_lemma _ _ _

lemma corr_pullGen_mulGen (t : LB.Gen (LB.LinComb L φ ε)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)) (g : Z ⟶ Y) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _ t t₂) g)
      (LB.mulGen L _ _ _ _ (LB.pullGen L φ ε t g) (LB.pullGen L φ₂ ε₂ t₂ g)) := by
  intro j j' _ _ hk
  obtain rfl : j = j' := funext fun k => by cases k <;> exact hk _ _ rfl
  exact shape_pull_mul g _ _ _ _ _ _ _ _ _ _ _

lemma shape_pull_comp {W : Scheme.{0}} (g : Z ⟶ Y) (g' : W ⟶ Z) {U : Y.Opens} {U₁ : Z.Opens} {V₁ V₂ O : W.Opens}
    (h₁ : U₁ ≤ g ⁻¹ᵁ U) (k₁ : V₁ ≤ g' ⁻¹ᵁ U₁) (k₂ : V₂ ≤ (g' ≫ g) ⁻¹ᵁ U) (o₁ : O ≤ V₁) (o₂ : O ≤ V₂)
    (x : Γ(Y, U)ˣ) :
    res o₁ (res k₁ (pullU g' U₁ (res h₁ (pullU g U x)))) = res o₂ (res k₂ (pullU (g' ≫ g) U x)) := by
  simp only [pullU_res_eq_res_pullU', res_res_lemma]
  first
    | exact (res_res_lemma _ _ _).trans (pullU_comp_lemma _ _ _ _ _)
    | exact (res_res_lemma _ _ _).trans ((res_res_lemma _ _ _).trans (pullU_comp_lemma _ _ _ _ _))

lemma corr_pullGen_comp {W : Scheme.{0}} (t : LB.Gen (LB.LinComb L φ ε)) (g : Z ⟶ Y) (g' : W ⟶ Z) :
    LB.Gen.Corr L _ ε _ ε (LB.pullGen L _ ε (LB.pullGen L φ ε t g) g') (LB.pullGen L φ ε t (g' ≫ g)) := by
  intro j j' _ _ hk
  obtain rfl : j = j' := funext fun k => hk k k (Category.assoc _ _ _).symm
  exact shape_pull_comp g g' _ _ _ _ _ _

lemma corr_one_of {t : LB.Gen (LB.LinComb L φ ε)} (h : ∀ j, LB.Coh L φ j → t.s j = 1) :
    LB.Gen.Corr L φ ε (K' := PEmpty) PEmpty.elim PEmpty.elim t (LB.oneGen L) := by
  intro j j' hc _ _
  exact (congrArg (res _) (h j hc)).trans ((map_one _).trans (map_one _).symm)

lemma shape_one_mul {U₁ O O' : Y.Opens} {V : Y.Opens} (h : O ≤ O') (h₀ : O' ≤ V) (h₁ : O' ≤ U₁) (hO : O ≤ U₁)
    (x : Γ(Y, U₁)ˣ) : res h (res h₀ (1 : Γ(Y, V)ˣ) * res h₁ x) = res hO x := by
  simp only [map_one, one_mul, res_res_lemma]

lemma corr_mulGen_one (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen.Corr L _ _ φ ε (LB.mulGen L (K := PEmpty) PEmpty.elim PEmpty.elim φ ε (LB.oneGen L) t) t := by
  intro j j' _ _ hk
  obtain rfl : j ∘ Sum.inr = j' := funext fun k => hk (Sum.inr k) k rfl
  exact shape_one_mul _ _ _ _ _

lemma corr_pullGen_of_eq (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (g g' : Z ⟶ Y) (e : g = g') :
    LB.Gen.Corr L _ ε _ ε (LB.pullGen L φ ε t g) (LB.pullGen L φ ε t g') := by
  subst e
  exact gen_corr_self _

lemma shape_pull_id {U : Y.Opens} {V O : Y.Opens} (h : V ≤ (𝟙 Y) ⁻¹ᵁ U) (o : O ≤ V) (o' : O ≤ U) (x : Γ(Y, U)ˣ) :
    res o (res h (pullU (𝟙 Y) U x)) = res o' x := by
  rw [res_res_lemma]
  exact res_pullU_id' _ _ x

lemma corr_pullGen_id (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen.Corr L _ ε φ ε (LB.pullGen L φ ε t (𝟙 Y)) t := by
  intro j j' _ _ hk
  obtain rfl : j = j' := funext fun k => hk k k (Category.id_comp _)
  exact shape_pull_id _ _ _ _

lemma powGen_isGen_of_isGen (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) :
    (ReciprocityTheory.ChartRestriction.G.Out.GeneratorPullback.powGen L φ ε t n).IsGen := by
  intro (i : K → L.ι) (j : K → L.ι)
  have e := ht i j
  have hg : (LB.LinComb L φ (fun k => (n : ℤ) * ε k)).g i j = ((LB.LinComb L φ ε).g i j) ^ n := by
    simp only [LB.LinComb, mul_comm (n : ℤ), zpow_mul, zpow_natCast, Finset.prod_pow]
    rfl
  exact (map_pow _ _ _).trans ((congrArg (· ^ n) e).trans ((mul_pow _ _ _).trans
    (congrArg₂ (· * ·) hg.symm (map_pow _ _ _).symm)))

lemma invGen_isGen_of_isGen (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : (LB.invGen L φ ε t).IsGen := by
  intro (i : K → L.ι) (j : K → L.ι)
  have e := ht i j
  have hinv : (LB.LinComb L φ (fun k => -ε k)).g i j = ((LB.LinComb L φ ε).g i j)⁻¹ := by
    simp only [LB.LinComb, zpow_neg, Finset.prod_inv_distrib]
    rfl
  exact (map_inv _ _).trans ((congrArg (·⁻¹) e).trans ((mul_inv _ _).trans
    (congrArg₂ (· * ·) hinv.symm (map_inv _ _).symm)))

lemma mulGen_isGen_of_isGen (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂))
    (ht₂ : t₂.IsGen) : (LB.mulGen L _ _ _ _ t t₂).IsGen := by
  intro i j
  ext
  exact (mulSec L φ ε φ₂ ε₂ (genSec t ht) (genSec t₂ ht₂)).compat i j

lemma shape_pull_inv (g : Z ⟶ Y) {U : Y.Opens} {W O O' : Z.Opens} (h : W ≤ g ⁻¹ᵁ U) (o : O ≤ W) (h' : O' ≤ g ⁻¹ᵁ U)
    (o' : O ≤ O') (x : Γ(Y, U)ˣ) : res o (res h (pullU g U x⁻¹)) = res o' (res h' (pullU g U x))⁻¹ := by
  simp only [map_inv, res_res_lemma]

lemma corr_pullGen_invGen (t : LB.Gen (LB.LinComb L φ ε)) (g : Z ⟶ Y) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (LB.invGen L φ ε t) g) (LB.invGen L _ _ (LB.pullGen L φ ε t g)) := by
  intro j j' _ _ hk
  obtain rfl : j = j' := funext fun k => hk k k rfl
  exact shape_pull_inv g _ _ _ _ _

lemma shape_mul_inv_one {U U' O : Y.Opens} {W : Y.Opens} (h₁ : W ≤ U) (h₂ : W ≤ U') (o : O ≤ W) (x : Γ(Y, U)ˣ)
    (y : Γ(Y, U')ˣ) (hxy : res (inf_le_left : U ⊓ U' ≤ U) x = res (inf_le_right : U ⊓ U' ≤ U') y) :
    res o (res h₁ x * res h₂ y⁻¹) = 1 := by
  simp only [map_mul, map_inv, res_res_lemma]
  rw [res_eq_res_of_le_of_res_eq hxy (le_inf (o.trans h₁) (o.trans h₂)) _ (o.trans h₂), mul_inv_cancel]

lemma corr_ratio_one {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') :
    LB.Gen.Corr L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t'))
      (LB.oneGen L) := by
  intro j j' hc _ _
  have e := h (j ∘ Sum.inl) (j ∘ Sum.inr) (fun a b e => hc (Sum.inl a) (Sum.inl b) e)
    (fun a b e => hc (Sum.inr a) (Sum.inr b) e) fun k k' e => hc (Sum.inl k) (Sum.inr k') e
  exact (shape_mul_inv_one _ _ _ _ _ e).trans (map_one _).symm

theorem exists_normalized_to {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K Kr : Type} [Fintype K] [Fintype Kr]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z)
    (φr : Kr → (Z ⟶ X)) (εr : Kr → ℤ) (r : LB.Gen (LB.LinComb L φr εr)) (hr : r.IsGen)
    (h0 : fsum (fun k => z ≫ φ k) ε = fsum φr εr) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' z) r := by
  set rT := LB.pullGen L φr εr r p
  have hrT : rT.IsGen := pullGen_isGen_of_isGen _ _ r hr p
  set v := LB.mulGen L _ _ _ _ t (LB.invGen L _ _ rT)
  have hv : v.IsGen := mulGen_isGen_of_isGen _ ht _ (invGen_isGen_of_isGen _ hrT)
  have h0' : fsum (fun i => z ≫ Sum.elim φ (fun k => p ≫ φr k) i) (Sum.elim ε (fun k => -εr k)) = 0 := by
    rw [fsum_comp, fsum_sumElim, Finsupp.mapDomain_add, ← fsum_comp, h0, ← fsum_comp]
    have e : (fun k => z ≫ p ≫ φr k) = φr := by
      funext k
      rw [← Category.assoc, hzp, Category.id_comp]
    rw [e, fsum_neg, add_neg_cancel]
  obtain ⟨v', hv', hv1⟩ := exists_normalized hL _ _ v hv p z hzp h0'
  have hW := mulGen_isGen_of_isGen _ hv' _ hrT
  have hsW : LB.SameSum (Sum.elim (Sum.elim φ (fun k => p ≫ φr k)) (fun k => p ≫ φr k))
      (Sum.elim (Sum.elim ε (fun k => -εr k)) εr) φ ε := by
    rw [sameSum_iff_fsum, fsum_sumElim, fsum_sumElim, fsum_neg]
    abel
  obtain ⟨u, hu, hcW⟩ := gen_transport hL hsW _ hW
  refine ⟨u, hu, ?_⟩
  have c1 := corr_pullGen (corr_symm hcW) z
  have c2 := corr_pullGen_mulGen v' rT z
  have c4 := corr_trans hL (corr_pullGen_comp r p z)
    (corr_trans hL (corr_pullGen_of_eq r hr _ _ hzp) (corr_pullGen_id r))
  have c3 := corr_mulGen (corr_one_of (fun j hj => hv1 j hj)) c4
  have c5 := corr_mulGen_one r
  exact corr_trans hL c1 (corr_trans hL c2 (corr_trans hL c3 c5))

end ReciprocityTheory.ChartRestriction.G.DVR
