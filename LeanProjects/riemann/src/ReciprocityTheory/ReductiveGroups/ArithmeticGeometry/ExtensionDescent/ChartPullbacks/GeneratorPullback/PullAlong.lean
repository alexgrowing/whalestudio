import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.LBxP

open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res')

section Germ

variable {X X' Y Y' Z Z' : Scheme.{0}}

lemma pullU_comp (a : Z ⟶ Y) (h : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    pullU (a ≫ h) U u = pullU a (h ⁻¹ᵁ U) (pullU h U u) := by
  first
    | rfl
    | (ext1; simp [pullU])

lemma gU_pullU_comp (a : Z ⟶ Y) (h : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) (z : Z)
    (hz : z ∈ a ⁻¹ᵁ (h ⁻¹ᵁ U)) (hz' : z ∈ (a ≫ h) ⁻¹ᵁ U) :
    gU z hz (pullU a (h ⁻¹ᵁ U) (pullU h U u)) = gU z hz' (pullU (a ≫ h) U u) := by
  first
    | exact (congrArg (gU z hz) (pullU_comp a h U u)).symm
    | exact (congrArg (gU z hz') (pullU_comp a h U u)).symm

lemma gU_rp_rp (a : Z ⟶ Y) (h : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hV : V ≤ h ⁻¹ᵁ U)
    {W : Z.Opens} (hW : W ≤ a ⁻¹ᵁ V) (u : Γ(X, U)ˣ) (z : Z) (hz : z ∈ W) :
    gU z hz (res hW (pullU a V (res hV (pullU h U u)))) =
      gU z (show z ∈ (a ≫ h) ⁻¹ᵁ U from hV (hW hz)) (pullU (a ≫ h) U u) := by
  rw [gU_res, gU_pullU_res a hV (pullU h U u) z (hW hz) (hV (hW hz))]
  exact gU_pullU_comp a h U u z _ _

lemma gen_ext {M : LB Y} (a b : LB.Gen M)
    (h : ∀ j (y : Y) (hy : y ∈ M.U j), gU y hy (a.s j) = gU y hy (b.s j)) : a = b := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  congr 1
  funext j
  exact unit_ext _ _ (h j)

variable (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

lemma pullGen_pullAlong (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε))
    (a : Z ⟶ Y') (h2 : Z ⟶ Z') (b : Z' ⟶ Y) (hab : a ≫ h = h2 ≫ b)
    (hψ2 : ∀ k, (a ≫ ψ k) ≫ F = h2 ≫ (b ≫ φ k)) :
    LB.pullGen (L.pull F) ψ ε (GeneratorPullback.pullAlong L F h φ ε ψ hψ t) a =
      GeneratorPullback.pullAlong L F h2 (fun k => b ≫ φ k) ε (fun k => a ≫ ψ k) hψ2 (LB.pullGen L φ ε t b) := by
  apply gen_ext
  intro jj y hy
  exact (gU_rp_rp a h _ _ _ y hy).trans
    ((gU_pullU_congr hab _ _ y _ _).trans (gU_rp_rp h2 b _ _ _ y hy).symm)

lemma gU_lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) (y : Y)
    (hy : y ∈ (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') :
    gU y hy ((LB.LinComb L φ ε).g j j') =
      ∏ k, (gU y (show y ∈ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) from
        ⟨LB.wchart_le L φ j k hy.1, LB.wchart_le L φ j' k hy.2⟩)
        (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k) := by
  have hy2 : y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  have e : @Eq (Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ) ((LB.LinComb L φ ε).g j j')
      (∏ k, (@res Y (φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) (LB.wchart L φ j ⊓ LB.wchart L φ j')
        (le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k)))
        (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))) ^ (ε k)) := rfl
  show gU y hy2 _ = _
  rw [e, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) (gU_res _ y hy2 _)

lemma gU_pull_g (F : X' ⟶ X) (a : Y ⟶ X') (i j : PUnit → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((L.pull F).U i ⊓ (L.pull F).U j))
    (hy' : y ∈ (a ≫ F) ⁻¹ᵁ (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩))) :
    gU y hy (pullU a _ ((L.pull F).g i j)) = gU y hy' (pullU (a ≫ F) _ (L.g (i ⟨⟩) (j ⟨⟩))) := by
  rw [gU_pullU, gU_lcg L (fun _ => F) (fun _ => 1) i j (a.base y) hy]
  simp only [Fintype.prod_unique, zpow_one]
  exact (gU_pullU a _ y _ _).symm.trans (gU_pullU_comp a F _ _ y _ hy')

lemma gU_pullAlong (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε))
    (jj : K → (L.pull F).ι) (y : Y') (hy : y ∈ LB.wchart (L.pull F) ψ jj) :
    gU y hy ((GeneratorPullback.pullAlong L F h φ ε ψ hψ t).s jj) =
      Units.map (h.stalkMap y).hom (gU (h.base y)
        (GeneratorPullback.pullAlong_le L F h φ ψ hψ jj hy) (t.s (fun k => jj k ⟨⟩))) := by
  exact (gU_res _ y hy _).trans (gU_pullU h _ y _ _)

lemma gU_mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι) (y : Y)
    (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    gU y hy ((LB.mulGen L φ ε φ' ε' t t').s j) =
      gU y (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)) (t.s (j ∘ Sum.inl)) *
      gU y (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)) (t'.s (j ∘ Sum.inr)) := by
  exact (map_mul (gU y hy) _ _).trans (congrArg₂ (· * ·) (gU_res _ y hy _) (gU_res _ y hy _))

lemma mulGen_pullAlong (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (ψ : K → (Y' ⟶ X')) (ψ' : K' → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (hψ' : ∀ k, ψ' k ≫ F = h ≫ φ' k)
    (hψS : ∀ k, Sum.elim ψ ψ' k ≫ F = h ≫ Sum.elim φ φ' k)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    GeneratorPullback.pullAlong L F h (Sum.elim φ φ') (Sum.elim ε ε') (Sum.elim ψ ψ') hψS
                      (LB.mulGen L φ ε φ' ε' t t') =
      LB.mulGen (L.pull F) ψ ε ψ' ε' (GeneratorPullback.pullAlong L F h φ ε ψ hψ t)
        (GeneratorPullback.pullAlong L F h φ' ε' ψ' hψ' t') := by
  apply gen_ext
  intro jj y hy
  refine (gU_pullAlong L F h (Sum.elim φ φ') (Sum.elim ε ε') (Sum.elim ψ ψ') hψS _ jj y hy).trans ?_
  refine ((congrArg (Units.map (h.stalkMap y).hom.toMonoidHom)
    (gU_mulGen L φ ε φ' ε' t t' _ (h.base y) _)).trans (map_mul _ _ _)).trans ?_
  refine Eq.trans ?_ (gU_mulGen (L.pull F) ψ ε ψ' ε' _ _ jj y hy).symm
  exact congrArg₂ (· * ·) (gU_pullAlong L F h φ ε ψ hψ t (jj ∘ Sum.inl) y _).symm
    (gU_pullAlong L F h φ' ε' ψ' hψ' t' (jj ∘ Sum.inr) y _).symm

lemma invGen_pullAlong (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) :
    GeneratorPullback.pullAlong L F h φ (fun k => - ε k) ψ hψ (LB.invGen L φ ε t) =
      LB.invGen (L.pull F) ψ ε (GeneratorPullback.pullAlong L F h φ ε ψ hψ t) := by
  apply gen_ext
  intro jj y hy
  refine (gU_pullAlong L F h φ (fun k => - ε k) ψ hψ _ jj y hy).trans ?_
  refine ((congrArg (Units.map (h.stalkMap y).hom.toMonoidHom)
    (map_inv (@gU Y (LB.wchart L φ (fun k => jj k ⟨⟩)) (h.base y) (GeneratorPullback.pullAlong_le L F h φ ψ hψ jj hy)) (t.s (fun k => jj k ⟨⟩)))).trans
    (map_inv _ _)).trans ?_
  exact ((map_inv (gU y hy) _).trans (congrArg (·⁻¹) (gU_pullAlong L F h φ ε ψ hψ t jj y hy))).symm

lemma oneGen_pullAlong (F : X' ⟶ X) (h : Y' ⟶ Y) (hψ : ∀ k : PEmpty, (PEmpty.elim k : Y' ⟶ X') ≫ F =
      h ≫ (PEmpty.elim k : Y ⟶ X)) :
    GeneratorPullback.pullAlong L F h PEmpty.elim PEmpty.elim PEmpty.elim hψ (LB.oneGen L) =
      LB.oneGen (L.pull F) := by
  apply gen_ext
  intro jj y hy
  refine (gU_pullAlong L F h PEmpty.elim PEmpty.elim PEmpty.elim hψ (LB.oneGen L) jj y hy).trans ?_
  exact ((congrArg (Units.map (h.stalkMap y).hom.toMonoidHom)
    (map_one (@gU Y (LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) (fun k => jj k ⟨⟩)) (h.base y)
      (GeneratorPullback.pullAlong_le L F h PEmpty.elim PEmpty.elim hψ jj hy)))).trans
    (map_one _)).trans (map_one (gU y hy)).symm

private lemma gU_pull_g_lemma_2 (F : X' ⟶ X) (h : Y' ⟶ Y) (φk : Y ⟶ X) (ψk : Y' ⟶ X')
    (hk : ψk ≫ F = h ≫ φk) (i j : PUnit → L.ι) (y : Y')
    (hy : y ∈ ψk ⁻¹ᵁ ((L.pull F).U i ⊓ (L.pull F).U j))
    (hy' : h.base y ∈ φk ⁻¹ᵁ (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩))) :
    gU y hy (pullU ψk _ ((L.pull F).g i j)) =
      Units.map (h.stalkMap y).hom (gU (h.base y) hy' (pullU φk _ (L.g (i ⟨⟩) (j ⟨⟩)))) := by
  have h1 : y ∈ (ψk ≫ F) ⁻¹ᵁ (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩)) := by
    rw [hk]; exact hy'
  rw [gU_pull_g L F ψk i j y hy h1,
    gU_pullU_congr hk (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩)) (L.g (i ⟨⟩) (j ⟨⟩)) y h1 hy',
    ← gU_pullU_comp h φk (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩)) (L.g (i ⟨⟩) (j ⟨⟩)) y hy' hy']
  exact gU_pullU h _ y _ _

lemma isGen_pullAlong (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) : (GeneratorPullback.pullAlong L F h φ ε ψ hψ t).IsGen := by
  unfold LB.Gen.IsGen at ht ⊢
  intro i j
  apply unit_ext
  intro y hy
  have hb : h.base y ∈ (LB.LinComb L φ ε).U (fun k => i k ⟨⟩) ⊓
      (LB.LinComb L φ ε).U (fun k => j k ⟨⟩) :=
    ⟨GeneratorPullback.pullAlong_le L F h φ ψ hψ i hy.1, GeneratorPullback.pullAlong_le L F h φ ψ hψ j hy.2⟩
  have kk := (gU_res _ (h.base y) hb _).symm.trans
    ((congrArg (gU (h.base y) hb) (ht (fun k => i k ⟨⟩) (fun k => j k ⟨⟩))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gU_lcg L φ ε _ _ (h.base y) hb)
        (gU_res _ (h.base y) hb _))))
  refine ((gU_res _ y hy _).trans (gU_pullAlong L F h φ ε ψ hψ t i y _)).trans ?_
  refine Eq.trans ?_ ((map_mul (gU y hy) _ _).trans (congrArg₂ (· * ·) (gU_lcg (L.pull F) ψ ε i j y hy)
    ((gU_res _ y hy _).trans (gU_pullAlong L F h φ ε ψ hψ t j y _)))).symm
  refine (congrArg (Units.map (h.stalkMap y).hom.toMonoidHom) kk).trans ?_
  rw [map_mul, map_prod]
  refine congrArg₂ (fun a b => a * b) (Finset.prod_congr rfl fun k _ => ?_) rfl
  rw [map_zpow]
  exact congrArg (· ^ ε k) (gU_pull_g_lemma_2 L F h (φ k) (ψ k) (hψ k) (i k) (j k) y _ _).symm

lemma corr_pullAlong (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (ψ : K → (Y' ⟶ X')) (ψ' : K' → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (hψ' : ∀ k, ψ' k ≫ F = h ≫ φ' k)
    (hinj : ∀ a b : K ⊕ K', Sum.elim ψ ψ' a ≫ F = Sum.elim ψ ψ' b ≫ F →
      Sum.elim ψ ψ' a = Sum.elim ψ ψ' b)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (hc : LB.Gen.Corr L φ ε φ' ε' t t') :
    LB.Gen.Corr (L.pull F) ψ ε ψ' ε' (GeneratorPullback.pullAlong L F h φ ε ψ hψ t)
      (GeneratorPullback.pullAlong L F h φ' ε' ψ' hψ' t') := by
  unfold LB.Gen.Corr at hc ⊢
  intro j j' hj hj' hjj
  have c1 : LB.Coh L φ (fun k => j k ⟨⟩) := fun k₁ k₂ e =>
    congrFun (hj k₁ k₂ (hinj (Sum.inl k₁) (Sum.inl k₂) (by
      show ψ k₁ ≫ F = ψ k₂ ≫ F
      rw [hψ, hψ, e]))) ⟨⟩
  have c2 : LB.Coh L φ' (fun k => j' k ⟨⟩) := fun k₁ k₂ e =>
    congrFun (hj' k₁ k₂ (hinj (Sum.inr k₁) (Sum.inr k₂) (by
      show ψ' k₁ ≫ F = ψ' k₂ ≫ F
      rw [hψ', hψ', e]))) ⟨⟩
  have c3 : ∀ k k', φ k = φ' k' → j k ⟨⟩ = j' k' ⟨⟩ := fun k k' e =>
    congrFun (hjj k k' (hinj (Sum.inl k) (Sum.inr k') (by
      show ψ k ≫ F = ψ' k' ≫ F
      rw [hψ, hψ', e]))) ⟨⟩
  have key := hc (fun k => j k ⟨⟩) (fun k => j' k ⟨⟩) c1 c2 c3
  apply unit_ext
  intro y hy
  have hb : h.base y ∈ LB.wchart L φ (fun k => j k ⟨⟩) ⊓ LB.wchart L φ' (fun k => j' k ⟨⟩) :=
    ⟨GeneratorPullback.pullAlong_le L F h φ ψ hψ j hy.1, GeneratorPullback.pullAlong_le L F h φ' ψ' hψ' j' hy.2⟩
  have kk := (gU_res _ (h.base y) hb _).symm.trans
    ((congrArg (gU (h.base y) hb) key).trans (gU_res _ (h.base y) hb _))
  exact ((gU_res _ y hy _).trans (gU_pullAlong L F h φ ε ψ hψ t j y _)).trans
    ((congrArg (Units.map (h.stalkMap y).hom.toMonoidHom) kk).trans
      ((gU_res _ y hy _).trans (gU_pullAlong L F h φ' ε' ψ' hψ' t' j' y _)).symm)

lemma wpl {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (h : Z ⟶ Y)
    (j : K → L.ι) : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

lemma corr_of_eq {M : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {t₁ t₁' : LB.Gen (LB.LinComb M φ ε)}
    {t₂ t₂' : LB.Gen (LB.LinComb M φ' ε')} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂')
    (h : LB.Gen.Corr M φ ε φ' ε' t₁' t₂') : LB.Gen.Corr M φ ε φ' ε' t₁ t₂ := by
  subst h₁
  subst h₂
  exact h

end Germ

end ReciprocityTheory.ChartRestriction.G.Out.LBxP
