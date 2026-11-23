import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf

open Semi

theorem zpow_sum' {M : Type} [CommGroup M] {K : Type} (a : M) (s : Finset K) (f : K → ℤ) :
    a ^ (∑ k ∈ s, f k) = ∏ k ∈ s, a ^ f k := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons k s hk ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add, ih]

theorem prod_sameSum {M : Type} [CommGroup M] {Y X : Scheme.{0}} {K K' : Type} [Fintype K]
    [Fintype K'] (B : (Y ⟶ X) → M) (ψ : K → (Y ⟶ X)) (ψ' : K' → (Y ⟶ X)) (ε : K → ℤ)
    (ε' : K' → ℤ) (hS : LB.SameSum ψ ε ψ' ε') :
    ∏ k, B (ψ k) ^ ε k = ∏ k', B (ψ' k') ^ ε' k' := by
  classical
  have key : ∀ {L : Type} [Fintype L] (g : L → (Y ⟶ X)) (e : L → ℤ) (S : Finset (Y ⟶ X)),
      (∀ k, g k ∈ S) → ∏ k, B (g k) ^ e k = ∏ φ ∈ S, B φ ^ (∑ k, if g k = φ then e k else 0) := by
    intro L _ g e S hS
    rw [← Finset.prod_fiberwise_of_maps_to (g := g) (t := S) (fun k _ => hS k)]
    refine Finset.prod_congr rfl (fun φ _ => ?_)
    rw [zpow_sum', Finset.prod_filter]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    split_ifs with hk
    · rw [hk]
    · simp
  rw [key ψ ε (Finset.univ.image ψ ∪ Finset.univ.image ψ')
      (fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))),
    key ψ' ε' (Finset.univ.image ψ ∪ Finset.univ.image ψ')
      (fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
  refine Finset.prod_congr rfl (fun φ _ => ?_)
  congr 1
  first
  | exact hS φ
  | convert hS φ

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr base_eq) in

theorem gU_pullAlong_idx {X X' Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (jj : K → (L.pull F).ι) (y : Y') (hy : y ∈ LB.wchart (L.pull F) ψ jj)
    (idx : (Y' ⟶ X) → L.ι)
    (mk : ∀ k, y ∈ (ψ k ≫ F) ⁻¹ᵁ (L.U (jj k ⟨⟩) ⊓ L.U (idx (ψ k ≫ F))))
    (mem0 : h.base y ∈ LB.wchart L φ (fun k => idx (ψ k ≫ F))) :
    gU y hy ((GeneratorPullback.pullAlong L F h φ ε ψ hψ t).s jj) =
      (∏ k, (gU y (mk k) (pullU (ψ k ≫ F) _ (L.g (jj k ⟨⟩) (idx (ψ k ≫ F))))) ^ (ε k)) *
        Units.map (h.stalkMap y).hom (gU (h.base y) mem0 (t.s (fun k => idx (ψ k ≫ F)))) := by
  have m1 := GeneratorPullback.pullAlong_le L F h φ ψ hψ jj hy
  have step : ∀ k (hk : h.base y ∈ φ k ⁻¹ᵁ (L.U (jj k ⟨⟩) ⊓ L.U (idx (ψ k ≫ F)))),
      Units.map (h.stalkMap y).hom (gU (h.base y) hk
        (pullU (φ k) _ (L.g (jj k ⟨⟩) (idx (ψ k ≫ F))))) =
      gU y (mk k) (pullU (ψ k ≫ F) _ (L.g (jj k ⟨⟩) (idx (ψ k ≫ F)))) := by
    intro k hk
    have hk' : y ∈ h ⁻¹ᵁ (φ k ⁻¹ᵁ (L.U (jj k ⟨⟩) ⊓ L.U (idx (ψ k ≫ F)))) := hk
    exact (gU_pullU h _ y hk' _).symm.trans ((LBxP.gU_pullU_comp h (φ k) _ _ y hk'
      (show y ∈ (h ≫ φ k) ⁻¹ᵁ _ from hk)).trans (gU_pullU_congr (hψ k).symm _ _ y _ _))
  refine (LBxP.gU_pullAlong L F h φ ε ψ hψ t jj y hy).trans ?_
  rw [Semi.Transport.gU_isGen ht (h.base y) m1 mem0, map_mul]
  erw [LBxP.gU_lcg L φ ε (fun k => jj k ⟨⟩) (fun k => idx (ψ k ≫ F)) (h.base y) ⟨m1, mem0⟩]
  rw [map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) (step k _)

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res) in

theorem corr_pullAlong_sameSum {X X' Y Y' : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (ψ : K → (Y' ⟶ X')) (ψ' : K' → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (hψ' : ∀ k, ψ' k ≫ F = h ≫ φ' k)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen)
    (ht' : t'.IsGen) (hc : LB.Gen.Corr L φ ε φ' ε' t t') (hS : LB.SameSum ψ ε ψ' ε') :
    LB.Gen.Corr (L.pull F) ψ ε ψ' ε' (GeneratorPullback.pullAlong L F h φ ε ψ hψ t)
      (GeneratorPullback.pullAlong L F h φ' ε' ψ' hψ' t') := by
  classical
  intro j j' cj cj' cjj
  apply unit_ext
  intro y hy
  refine (gU_res _ y hy _).trans (Eq.trans ?_ (gU_res _ y hy _).symm)
  obtain ⟨idx, hidx⟩ := TLinPf.idx_exists L hL y
  have hF : ∀ (ζ : Y' ⟶ X') (a : (L.pull F).ι), ζ y ∈ (L.pull F).U a → F (ζ y) ∈ L.U (a ⟨⟩) :=
    fun ζ a hz => Set.mem_iInter.1 hz ⟨⟩
  have mk : ∀ k, y ∈ (ψ k ≫ F) ⁻¹ᵁ (L.U (j k ⟨⟩) ⊓ L.U (idx (ψ k ≫ F))) := fun k =>
    ⟨show (ψ k ≫ F) y ∈ L.U (j k ⟨⟩) by
      rw [Scheme.Hom.comp_apply]; exact hF _ _ (Set.mem_iInter.1 hy.1 k), hidx _⟩
  have mk' : ∀ k, y ∈ (ψ' k ≫ F) ⁻¹ᵁ (L.U (j' k ⟨⟩) ⊓ L.U (idx (ψ' k ≫ F))) := fun k =>
    ⟨show (ψ' k ≫ F) y ∈ L.U (j' k ⟨⟩) by
      rw [Scheme.Hom.comp_apply]; exact hF _ _ (Set.mem_iInter.1 hy.2 k), hidx _⟩
  have mem0 : h y ∈ LB.wchart L φ (fun k => idx (ψ k ≫ F)) := Set.mem_iInter.2 fun k => by
    show (φ k) (h y) ∈ L.U (idx (ψ k ≫ F))
    rw [← Scheme.Hom.comp_apply, ← hψ k]; exact hidx _
  have mem0' : h y ∈ LB.wchart L φ' (fun k => idx (ψ' k ≫ F)) := Set.mem_iInter.2 fun k => by
    show (φ' k) (h y) ∈ L.U (idx (ψ' k ≫ F))
    rw [← Scheme.Hom.comp_apply, ← hψ' k]; exact hidx _
  refine (gU_pullAlong_idx L F h φ ε ψ hψ t ht j y hy.1 idx mk mem0).trans
    (Eq.trans ?_ (gU_pullAlong_idx L F h φ' ε' ψ' hψ' t' ht' j' y hy.2 idx mk' mem0').symm)

  have hmid : gU (h y) mem0 (t.s (fun k => idx (ψ k ≫ F))) =
      gU (h y) mem0' (t'.s (fun k => idx (ψ' k ≫ F))) := by
    have hc0 := hc (fun k => idx (ψ k ≫ F)) (fun k => idx (ψ' k ≫ F))
      (fun k1 k2 e => congrArg idx (by rw [hψ k1, hψ k2, e]))
      (fun k1 k2 e => congrArg idx (by rw [hψ' k1, hψ' k2, e]))
      (fun k k' e => congrArg idx (by rw [hψ k, hψ' k', e]))
    have := congrArg (gU (h y) (⟨mem0, mem0'⟩ : h y ∈ LB.wchart L φ (fun k => idx (ψ k ≫ F)) ⊓
      LB.wchart L φ' (fun k => idx (ψ' k ≫ F)))) hc0
    exact (gU_res _ (h y) _ _).symm.trans (this.trans (gU_res _ (h y) _ _))

  let Jf : (Y' ⟶ X') → L.ι := fun ζ =>
    if hz : ∃ k, ψ k = ζ then j hz.choose ⟨⟩
    else if hz' : ∃ k', ψ' k' = ζ then j' hz'.choose ⟨⟩ else idx (ζ ≫ F)
  have hJ : ∀ k, Jf (ψ k) = j k ⟨⟩ := by
    intro k
    have hz : ∃ k', ψ k' = ψ k := ⟨k, rfl⟩
    show (if hz : ∃ k', ψ k' = ψ k then j hz.choose ⟨⟩ else _) = _
    rw [dif_pos hz]
    exact congrFun (cj _ _ hz.choose_spec) ⟨⟩
  have hJ' : ∀ k', Jf (ψ' k') = j' k' ⟨⟩ := by
    intro k'
    show (if hz : ∃ k, ψ k = ψ' k' then j hz.choose ⟨⟩
      else if hz' : ∃ k'', ψ' k'' = ψ' k' then j' hz'.choose ⟨⟩ else idx (ψ' k' ≫ F)) = _
    by_cases hz : ∃ k, ψ k = ψ' k'
    · rw [dif_pos hz]; exact congrFun (cjj _ _ hz.choose_spec) ⟨⟩
    · have hz' : ∃ k'', ψ' k'' = ψ' k' := ⟨k', rfl⟩
      rw [dif_neg hz, dif_pos hz']; exact congrFun (cj' _ _ hz'.choose_spec) ⟨⟩
  let B : (Y' ⟶ X') → (Y'.presheaf.stalk y)ˣ := fun ζ =>
    if hm : y ∈ (ζ ≫ F) ⁻¹ᵁ (L.U (Jf ζ) ⊓ L.U (idx (ζ ≫ F))) then
      gU y hm (pullU (ζ ≫ F) _ (L.g (Jf ζ) (idx (ζ ≫ F)))) else 1
  have hgc : ∀ (ζ : Y' ⟶ X) (a b c : L.ι) (hab : a = b) (hm : y ∈ ζ ⁻¹ᵁ (L.U a ⊓ L.U c))
      (hm' : y ∈ ζ ⁻¹ᵁ (L.U b ⊓ L.U c)),
      gU y hm (pullU ζ _ (L.g a c)) = gU y hm' (pullU ζ _ (L.g b c)) := by
    intro ζ a b c hab hm hm'; subst hab; rfl
  have hB : ∀ k, gU y (mk k) (pullU (ψ k ≫ F) _ (L.g (j k ⟨⟩) (idx (ψ k ≫ F)))) = B (ψ k) := by
    intro k
    have hm : y ∈ (ψ k ≫ F) ⁻¹ᵁ (L.U (Jf (ψ k)) ⊓ L.U (idx (ψ k ≫ F))) := by
      rw [hJ k]; exact mk k
    show _ = (if hm : _ then _ else _)
    rw [dif_pos hm]
    exact hgc _ _ _ _ (hJ k).symm _ _
  have hB' : ∀ k, gU y (mk' k) (pullU (ψ' k ≫ F) _ (L.g (j' k ⟨⟩) (idx (ψ' k ≫ F)))) = B (ψ' k) := by
    intro k
    have hm : y ∈ (ψ' k ≫ F) ⁻¹ᵁ (L.U (Jf (ψ' k)) ⊓ L.U (idx (ψ' k ≫ F))) := by
      rw [hJ' k]; exact mk' k
    show _ = (if hm : _ then _ else _)
    rw [dif_pos hm]
    exact hgc _ _ _ _ (hJ' k).symm _ _
  refine congrArg₂ (· * ·) ?_ (congrArg _ hmid)
  exact ((Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (hB k)).trans
    (prod_sameSum B ψ ψ' ε ε' hS)).trans
    (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε' k) (hB' k)).symm

end ReciprocityTheory.ChartRestriction.G.Out.CubePf
