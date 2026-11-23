import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section BoxG

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {LG : LB G.left} {LG' : LB G'.left}

lemma unit_cancel {S : Type*} [CommRing S] (a b : Sˣ) (X Y : S) (h1 : X = ((a⁻¹ : Sˣ) : S) * Y) (h2 : a = b) :
    (b : S) * X = Y := by
  subst h2
  rw [h1, ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul]

def boxSecG (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (hw : w.IsGen) (hLG : LG.IsLB)
    (hLG' : LG'.IsLB) (k : ℕ) (σ : Fin j → H0 LG k) : H0 LG' k :=
  secOfIso (u := LB.linCombIso w (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ)))
    (boxSec LG (fun i => (pG.pr i).left) (k : ℤ) σ) (linCombIso_isGen w hw _ _)
    (linComb_isLB LG' hLG' _ _) (linComb_isLB _ (linComb_isLB LG hLG _ _) _ _)

set_option maxHeartbeats 1000000 in
theorem isBoxSecG_boxSecG (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (hw : w.IsGen)
    (hLG : LG.IsLB) (hLG' : LG'.IsLB) (k : ℕ) (σ : Fin j → H0 LG k) :
    IsBoxSecG pG w k (boxSecG pG w hw hLG hLG' k σ) σ := by
  intro jN jL
  set V := (LB.div (boxLB LG pG.pr) LG').U (jN, jL) with hVdef
  have hVab : V ≤ LB.wchart LG' (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL) ⊓
      LB.wchart (boxLB LG pG.pr) (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jN) :=
    fun _ hy => ⟨Set.mem_iInter.2 fun _ => hy.2, Set.mem_iInter.2 fun _ => hy.1⟩
  have hspec := congrArg (rs hVab) (secOfIso_spec (u := LB.linCombIso w (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ)))
    (boxSec LG (fun i => (pG.pr i).left) (k : ℤ) σ) (linCombIso_isGen w hw _ _)
    (linComb_isLB LG' hLG' _ _) (linComb_isLB _ (linComb_isLB LG hLG _ _) _ _) (fun _ => jL) (fun _ => jN))
  erw [rs_rs] at hspec
  have hspec2 := hspec.trans (isoCand_rs (LB.linCombIso w (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ)))
    (boxSec LG (fun i => (pG.pr i).left) (k : ℤ) σ) (fun _ => jL) (fun _ => jN) hVab)
  have hVd : V ≤ (LB.div (LB.LinComb (boxLB LG pG.pr) (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ)))
      (LB.LinComb LG' (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ)))).U ((fun _ => jN), (fun _ => jL)) :=
    fun _ hy => ⟨Set.mem_iInter.2 fun _ => hy.1, Set.mem_iInter.2 fun _ => hy.2⟩
  have hu : res hVd ((LB.linCombIso w (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ))).s ((fun _ => jN), (fun _ => jL))) =
      w.s (jN, jL) ^ k := by
    erw [linCombIso_res, Fin.prod_univ_one]
    show tu (LB.div (boxLB LG pG.pr) LG').U w.s V (𝟙 G'.left) (jN, jL) ^ (k : ℤ) = _
    rw [tu_def (U := (LB.div (boxLB LG pG.pr) LG').U) (u := w.s) (ψ := 𝟙 G'.left) (p := (jN, jL)) (V := V)
      (fun _ hy => hy), zpow_natCast]
    congr 1
    ext
    simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.id_app]
    show (G'.left.presheaf.map (homOfLE _).op).hom ((w.s (jN, jL)).val) = (w.s (jN, jL)).val
    rw [show (homOfLE (le_refl V)).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  have key := unit_cancel _ _ _ _ hspec2 hu
  refine key.trans ?_
  simp only [boxSec, boxSecF]
  refine (map_prod ((G'.left.presheaf.map (homOfLE _).op).hom) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact rs_rs _ _ _

end BoxG

section BoxGen

variable {X X' Y Y' : Scheme.{0}} (L : LB X) {j : ℕ} (pr : Fin j → (X' ⟶ X)) {K : Type} [Fintype K]
  (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (p : Fin j → (Y' ⟶ Y)) (φ : Fin j → K → (Y ⟶ X))
  (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a)

def boxSecGenF (σ : ∀ i, LB.Sec (LB.LinComb L (φ i) ε)) (jN : K → (Fin j → L.ι)) :
    Γ(Y', LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN) :=
  ∏ i, rs (box_le_of_comp L pr φ' (φ i) (p i) i (hφ i) jN) (((p i).app _).hom ((σ i).f (fun a => jN a i)))

set_option maxHeartbeats 1000000 in
include hφ in
lemma boxGen_g_res (jN jN' : K → (Fin j → L.ι)) {V : Y'.Opens}
    (h : V ≤ LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN ⊓ LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN') :
    res h ((LB.LinComb (LB.LinComb L pr (fun _ => 1)) φ' ε).g jN jN') =
      ∏ i, ∏ a, tr L V (p i ≫ φ i a) (jN a i) (jN' a i) ^ ε a := by
  erw [linComb_g_res]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun a _ => ?_
  have h0 : V ≤ φ' a ⁻¹ᵁ ((LB.LinComb L pr (fun _ => 1)).U (jN a) ⊓ (LB.LinComb L pr (fun _ => 1)).U (jN' a)) :=
    fun y hy => ⟨Set.mem_iInter.1 (h hy).1 a, Set.mem_iInter.1 (h hy).2 a⟩
  rw [tr_def _ h0]
  have h1 : V ≤ LB.wchart L (fun i => φ' a ≫ pr i) (jN a) ⊓ LB.wchart L (fun i => φ' a ≫ pr i) (jN' a) :=
    fun y hy => ⟨Set.mem_iInter.2 fun i => Set.mem_iInter.1 (Set.mem_iInter.1 (h hy).1 a) i,
      Set.mem_iInter.2 fun i => Set.mem_iInter.1 (Set.mem_iInter.1 (h hy).2 a) i⟩
  have e := linComb_g_comp (L := L) pr (fun _ => 1) (φ' a) (jN a) (jN' a)
  have e2 := congrArg (res h1) e
  erw [res_res'] at e2
  erw [← e2, linComb_g_res]
  simp only [zpow_one]
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hφ i a]

set_option maxHeartbeats 1000000 in
lemma g_pull_gen {Z : Scheme.{0}} (h : Z ⟶ Y) (ψ : K → (Y ⟶ X)) (a b : K → L.ι) {W : Z.Opens}
    (hW : W ≤ h ⁻¹ᵁ (LB.wchart L ψ a ⊓ LB.wchart L ψ b)) :
    res hW (pullU h _ ((LB.LinComb L ψ ε).g a b)) = ∏ c, tr L W (h ≫ ψ c) (a c) (b c) ^ ε c := by
  simp only [LB.LinComb, map_prod, map_zpow]
  refine Finset.prod_congr rfl fun c _ => ?_
  congr 1
  have hle : LB.wchart L ψ a ⊓ LB.wchart L ψ b ≤ ψ c ⁻¹ᵁ (L.U (a c) ⊓ L.U (b c)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L ψ a c)) (inf_le_right.trans (LB.wchart_le L ψ b c))
  have e : res hle (pullU (ψ c) _ (L.g (a c) (b c))) = tr L _ (ψ c) (a c) (b c) := by
    rw [tr_eq_tu, tu, dif_pos hle]
  erw [e]
  exact tr_pull L h hW hle

set_option maxHeartbeats 1000000 in
lemma boxSecGenF_compat (σ : ∀ i, LB.Sec (LB.LinComb L (φ i) ε)) (jN jN' : K → (Fin j → L.ι)) :
    rs (inf_le_left : LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN ⊓
        LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN' ≤ LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN)
        (boxSecGenF L pr φ' ε p φ hφ σ jN) =
      @Units.val (Γ(Y', LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN ⊓
            LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN')) _
          ((LB.LinComb (LB.LinComb L pr (fun _ => 1)) φ' ε).g jN jN') *
        rs (inf_le_right : LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN ⊓
          LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN' ≤ LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN')
          (boxSecGenF L pr φ' ε p φ hφ σ jN') := by
  set W := LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN ⊓ LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN'
    with hWdef
  have hfac : ∀ i, rs (inf_le_left : W ≤ _) (rs (box_le_of_comp L pr φ' (φ i) (p i) i (hφ i) jN)
        (((p i).app _).hom ((σ i).f (fun a => jN a i)))) =
      ((∏ c, tr L W (p i ≫ φ i c) (jN c i) (jN' c i) ^ ε c : Γ(Y', W)ˣ) : Γ(Y', W)) *
        rs (inf_le_right : W ≤ _) (rs (box_le_of_comp L pr φ' (φ i) (p i) i (hφ i) jN')
          (((p i).app _).hom ((σ i).f (fun a => jN' a i)))) :=
    fun i => app_compat_generic (p i) (box_le_of_comp L pr φ' (φ i) (p i) i (hφ i) jN)
      (box_le_of_comp L pr φ' (φ i) (p i) i (hφ i) jN') _ _ _ ((σ i).compat _ _) _
      (g_pull_gen L ε (p i) (φ i) (fun a => jN a i) (fun a => jN' a i) _).symm
  have hg := boxGen_g_res L pr φ' ε p φ hφ jN jN' (le_refl W)
  erw [res_refl'] at hg
  simp only [boxSecGenF]
  refine (map_prod ((Y'.presheaf.map (homOfLE _).op).hom) _ _).trans ?_
  refine Eq.trans (Finset.prod_congr rfl (fun i _ => hfac i)) ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  · erw [hg, Units.coe_prod]
  · exact (map_prod ((Y'.presheaf.map (homOfLE _).op).hom) _ _).symm

def boxSecGen (σ : ∀ i, LB.Sec (LB.LinComb L (φ i) ε)) :
    LB.Sec (LB.LinComb (LB.LinComb L pr (fun _ => 1)) φ' ε) where
  f jN := boxSecGenF L pr φ' ε p φ hφ σ jN
  compat jN jN' := boxSecGenF_compat L pr φ' ε p φ hφ σ jN jN'

end BoxGen

end ReciprocityTheory.ChartRestriction.G.DVR
