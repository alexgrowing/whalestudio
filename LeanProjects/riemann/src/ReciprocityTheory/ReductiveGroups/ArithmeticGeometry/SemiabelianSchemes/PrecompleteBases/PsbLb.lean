import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

namespace ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace LB

variable {X Y Z : Scheme.{u}}

lemma res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl

lemma res_factor {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) {h : W ≤ U} (x : Γ(X, U)ˣ) :
    res h x = res h₂ (res h₁ x) := by
  rw [res_res]

lemma pullU_res (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (f.preimage_mono h) (pullU f U x) := by
  ext
  change ((X.presheaf.map (homOfLE h).op ≫ f.app V).hom) (x : Γ(X, U)) = _
  rw [Scheme.Hom.naturality]
  rfl

lemma res_pullU_eq (f : Y ⟶ X) {U U' : X.Opens} (hU' : U' ≤ U) {W : Y.Opens}
    (hW : W ≤ f ⁻¹ᵁ U) (hW' : W ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) :
    res hW (pullU f U x) = res hW' (pullU f U' (res hU' x)) := by
  rw [pullU_res, res_res]

lemma res_g_self {L : LB X} (hL : L.IsLB) (i : L.ι) {W : X.Opens} (h : W ≤ L.U i ⊓ L.U i) :
    res h (L.g i i) = 1 := by
  rw [res_factor (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (h.trans inf_le_left),
    hL.g_self, map_one]

lemma res_cocycle {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
  rw [res_factor (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) hW,
    res_factor (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) hW,
    res_factor (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) hW,
    ← map_mul, hL.cocycle]

lemma pull_g_self {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι) {W : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U i)) : res h (pullU f _ (L.g i i)) = 1 := by
  rw [res_pullU_eq f (le_refl (L.U i ⊓ L.U i)) h h, res_g_self hL i le_rfl, map_one, map_one]

lemma pull_cocycle {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i j k : L.ι) {W : Y.Opens}
    (h₁ : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j)) (h₂ : W ≤ f ⁻¹ᵁ (L.U j ⊓ L.U k))
    (h₃ : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    res h₁ (pullU f _ (L.g i j)) * res h₂ (pullU f _ (L.g j k)) =
      res h₃ (pullU f _ (L.g i k)) := by
  have hW : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := fun _ hy => ⟨h₁ hy, (h₂ hy).2⟩
  rw [res_pullU_eq f (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) h₁ hW,
    res_pullU_eq f (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) h₂ hW,
    res_pullU_eq f (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) h₃ hW,
    ← map_mul, ← map_mul, hL.cocycle]

lemma mem_of_cover {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i := by
  have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hx

abbrev triv (X : Scheme.{u}) : LB X where
  ι := PUnit.{u+1}
  U := fun _ => ⊤
  g := fun _ _ => 1

theorem isLB_triv (X : Scheme.{u}) : (triv X).IsLB where
  cover := iSup_const
  g_self := fun _ => map_one _
  cocycle := fun _ _ _ => by simp only [map_one, mul_one]

def dg (M L : LB X) (p q : M.ι × L.ι) : Γ(X, M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2))ˣ :=
  res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤ M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
    (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹

lemma res_dg (M L : LB X) (p q : M.ι × L.ι) {W : X.Opens}
    (hW : W ≤ M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2)) :
    res hW (dg M L p q) =
      res (hW.trans (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)))
        (M.g p.1 q.1) *
      (res (hW.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
        (L.g p.2 q.2))⁻¹ := by
  simp only [dg, map_mul, map_inv, res_res]

lemma dg_self {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) (p : M.ι × L.ι) :
    res (le_inf le_rfl le_rfl : M.U p.1 ⊓ L.U p.2 ≤ M.U p.1 ⊓ L.U p.2 ⊓ (M.U p.1 ⊓ L.U p.2))
      (dg M L p p) = 1 := by
  rw [res_dg, res_g_self hM, res_g_self hL, inv_one, mul_one]

lemma dg_cocycle {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) (p q r : M.ι × L.ι) :
    res (inf_le_left : M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ⊓ (M.U r.1 ⊓ L.U r.2) ≤
        M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2)) (dg M L p q) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ⊓ (M.U r.1 ⊓ L.U r.2) ≤
          M.U q.1 ⊓ L.U q.2 ⊓ (M.U r.1 ⊓ L.U r.2)) (dg M L q r) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ⊓ (M.U r.1 ⊓ L.U r.2) ≤
          M.U p.1 ⊓ L.U p.2 ⊓ (M.U r.1 ⊓ L.U r.2)) (dg M L p r) := by
  rw [res_dg, res_dg, res_dg, mul_mul_mul_comm, ← mul_inv]
  exact congrArg₂ (fun a b => a * b⁻¹) (res_cocycle hM _ _ _ _ _ _) (res_cocycle hL _ _ _ _ _ _)

theorem isLB_div {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) : (div M L).IsLB where
  cover := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := mem_of_cover hM x
    obtain ⟨j, hj⟩ := mem_of_cover hL x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩
  g_self := dg_self hM hL
  cocycle := dg_cocycle hM hL

variable (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']

lemma wchart_inter_le (φ : K → (Y ⟶ X)) (j j' : K → L.ι) (k : K) :
    wchart L φ j ⊓ wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) :=
  le_inf (inf_le_left.trans (wchart_le L φ j k)) (inf_le_right.trans (wchart_le L φ j' k))

def lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) :
    Γ(Y, wchart L φ j ⊓ wchart L φ j')ˣ :=
  ∏ k, (res (wchart_inter_le L φ j j' k) (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)

def ts {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : Gen (LinComb L φ ε)) (j : K → L.ι) :
    Γ(Y, wchart L φ j)ˣ :=
  t.s j

lemma res_lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) {W : Y.Opens}
    (hW : W ≤ wchart L φ j ⊓ wchart L φ j') :
    res hW (lcg L φ ε j j') =
      ∏ k, (res (hW.trans (wchart_inter_le L φ j j' k)) (pullU (φ k) _ (L.g (j k) (j' k)))) ^
        (ε k) := by
  rw [lcg, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) (res_res _ _ _)

lemma isGen_iff {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : Gen (LinComb L φ ε)) :
    t.IsGen ↔ ∀ i j : K → L.ι,
      res (inf_le_left : wchart L φ i ⊓ wchart L φ j ≤ wchart L φ i) (ts t i) =
        lcg L φ ε i j * res (inf_le_right : wchart L φ i ⊓ wchart L φ j ≤ wchart L φ j) (ts t j) :=
  Iff.rfl

lemma lcg_self {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j : K → L.ι) :
    res (le_inf le_rfl le_rfl : wchart L φ j ≤ wchart L φ j ⊓ wchart L φ j) (lcg L φ ε j j) = 1 := by
  rw [res_lcg]
  exact Finset.prod_eq_one fun k _ => by rw [pull_g_self hL (φ k), one_zpow]

lemma lcg_cocycle {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a b c : K → L.ι) :
    res (inf_le_left : wchart L φ a ⊓ wchart L φ b ⊓ wchart L φ c ≤ wchart L φ a ⊓ wchart L φ b)
        (lcg L φ ε a b) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        wchart L φ a ⊓ wchart L φ b ⊓ wchart L φ c ≤ wchart L φ b ⊓ wchart L φ c)
        (lcg L φ ε b c) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        wchart L φ a ⊓ wchart L φ b ⊓ wchart L φ c ≤ wchart L φ a ⊓ wchart L φ c)
        (lcg L φ ε a c) := by
  rw [res_lcg, res_lcg, res_lcg, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow]
  exact congrArg (· ^ ε k) (pull_cocycle hL (φ k) _ _ _ _ _ _)

theorem isLB_linComb {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (LinComb L φ ε).IsLB where
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    choose j hj using fun k => mem_of_cover hL ((φ k).base y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩
  g_self := lcg_self hL φ ε
  cocycle := lcg_cocycle hL φ ε

theorem isLB_pull {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) : (L.pull f).IsLB :=
  isLB_linComb hL _ _

lemma lcg_empty (i j : PEmpty.{u+1} → L.ι) :
    lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim i j = 1 :=
  Finset.prod_eq_one fun k _ => k.elim

lemma lcg_empty_self (j : PEmpty.{u+1} → L.ι) :
    res (le_inf le_rfl le_rfl : wchart L (Y := Y) PEmpty.elim j ≤
        wchart L (Y := Y) PEmpty.elim j ⊓ wchart L (Y := Y) PEmpty.elim j)
      (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim j j) = 1 := by
  rw [lcg_empty, map_one]

lemma lcg_empty_cocycle (a b c : PEmpty.{u+1} → L.ι) :
    res (inf_le_left : wchart L (Y := Y) PEmpty.elim a ⊓ wchart L PEmpty.elim b ⊓
        wchart L PEmpty.elim c ≤ wchart L PEmpty.elim a ⊓ wchart L PEmpty.elim b)
        (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim a b) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        wchart L (Y := Y) PEmpty.elim a ⊓ wchart L PEmpty.elim b ⊓ wchart L PEmpty.elim c ≤
          wchart L PEmpty.elim b ⊓ wchart L PEmpty.elim c)
        (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim b c) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        wchart L (Y := Y) PEmpty.elim a ⊓ wchart L PEmpty.elim b ⊓ wchart L PEmpty.elim c ≤
          wchart L PEmpty.elim a ⊓ wchart L PEmpty.elim c)
        (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim a c) := by
  rw [lcg_empty, lcg_empty, lcg_empty, map_one, map_one, map_one, mul_one]

theorem isLB_linComb_empty :
    (LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).IsLB where
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨PEmpty.elim, Set.mem_iInter.2 fun k => k.elim⟩
  g_self := lcg_empty_self L
  cocycle := lcg_empty_cocycle L

lemma wchart_comp_le (h : Z ⟶ Y) (φ : K → (Y ⟶ X)) (j : K → L.ι) :
    wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ wchart L φ j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

lemma wchart_comp_le₂ (h : Z ⟶ Y) (φ : K → (Y ⟶ X)) (i j : K → L.ι) :
    wchart L (fun k => h ≫ φ k) i ⊓ wchart L (fun k => h ≫ φ k) j ≤
      h ⁻¹ᵁ (wchart L φ i ⊓ wchart L φ j) :=
  fun _ hy => ⟨wchart_comp_le L h φ i hy.1, wchart_comp_le L h φ j hy.2⟩

lemma ts_pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : Gen (LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) :
    ts (pullGen L φ ε c h) j = res (wchart_comp_le L h φ j) (pullU h _ (ts c j)) := rfl

lemma pullU_comp (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (h ≫ f) U x = pullU h (f ⁻¹ᵁ U) (pullU f U x) := by
  ext; rfl

lemma pull_res_comp (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (hV : V ≤ f ⁻¹ᵁ U)
    {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ V) (hW' : W ≤ (h ≫ f) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res hW (pullU h V (res hV (pullU f U x))) = res hW' (pullU (h ≫ f) U x) := by
  rw [pullU_res, res_res, pullU_comp]
  rfl

lemma lcg_comp (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (i j : K → L.ι) :
    lcg L (fun k => h ≫ φ k) ε i j =
      res (wchart_comp_le₂ L h φ i j) (pullU h _ (lcg L φ ε i j)) := by
  rw [lcg, lcg, map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  exact congrArg (· ^ ε k) (pull_res_comp h (φ k) _ _ _ _ _).symm

theorem isGen_pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : Gen (LinComb L φ ε)) (hc : c.IsGen)
    (h : Z ⟶ Y) : (pullGen L φ ε c h).IsGen := by
  refine (isGen_iff L _).2 fun i j => ?_
  have key := congrArg (fun x => res (wchart_comp_le₂ L h φ i j) (pullU h _ x))
    ((isGen_iff L c).1 hc i j)
  simp only [map_mul, pullU_res, res_res] at key
  rw [ts_pullGen, ts_pullGen, lcg_comp]
  simp only [res_res]
  exact key

lemma wchart_inl_le (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K ⊕ K' → L.ι) :
    wchart L (Sum.elim φ φ') j ≤ wchart L φ (j ∘ Sum.inl) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)

lemma wchart_inr_le (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K ⊕ K' → L.ι) :
    wchart L (Sum.elim φ φ') j ≤ wchart L φ' (j ∘ Sum.inr) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)

lemma wchart_inl_le₂ (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j j' : K ⊕ K' → L.ι) :
    wchart L (Sum.elim φ φ') j ⊓ wchart L (Sum.elim φ φ') j' ≤
      wchart L φ (j ∘ Sum.inl) ⊓ wchart L φ (j' ∘ Sum.inl) :=
  inf_le_inf (wchart_inl_le L φ φ' j) (wchart_inl_le L φ φ' j')

lemma wchart_inr_le₂ (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j j' : K ⊕ K' → L.ι) :
    wchart L (Sum.elim φ φ') j ⊓ wchart L (Sum.elim φ φ') j' ≤
      wchart L φ' (j ∘ Sum.inr) ⊓ wchart L φ' (j' ∘ Sum.inr) :=
  inf_le_inf (wchart_inr_le L φ φ' j) (wchart_inr_le L φ φ' j')

lemma ts_mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε')) (j : K ⊕ K' → L.ι) :
    ts (mulGen L φ ε φ' ε' t t') j =
      res (wchart_inl_le L φ φ' j) (ts t (j ∘ Sum.inl)) *
        res (wchart_inr_le L φ φ' j) (ts t' (j ∘ Sum.inr)) := rfl

lemma lcg_sum (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (j j' : K ⊕ K' → L.ι) :
    lcg L (Sum.elim φ φ') (Sum.elim ε ε') j j' =
      res (wchart_inl_le₂ L φ φ' j j') (lcg L φ ε (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        res (wchart_inr_le₂ L φ φ' j j') (lcg L φ' ε' (j ∘ Sum.inr) (j' ∘ Sum.inr)) := by
  rw [res_lcg, res_lcg, lcg, Fintype.prod_sum_type]
  rfl

theorem isGen_mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen) :
    (mulGen L φ ε φ' ε' t t').IsGen := by
  refine (isGen_iff L _).2 fun j j' => ?_
  have k₁ := congrArg (res (wchart_inl_le₂ L φ φ' j j'))
    ((isGen_iff L t).1 ht (j ∘ Sum.inl) (j' ∘ Sum.inl))
  have k₂ := congrArg (res (wchart_inr_le₂ L φ φ' j j'))
    ((isGen_iff L t').1 ht' (j ∘ Sum.inr) (j' ∘ Sum.inr))
  simp only [map_mul, res_res] at k₁ k₂
  rw [ts_mulGen, ts_mulGen, lcg_sum]
  simp only [map_mul, res_res]
  rw [k₁, k₂]
  exact mul_mul_mul_comm _ _ _ _

lemma ts_invGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : Gen (LinComb L φ ε)) (j : K → L.ι) :
    ts (invGen L φ ε t) j = (ts t j)⁻¹ := rfl

lemma lcg_neg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j : K → L.ι) :
    lcg L φ (fun k => - ε k) i j = (lcg L φ ε i j)⁻¹ := by
  simp only [lcg, zpow_neg, Finset.prod_inv_distrib]

theorem isGen_invGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : Gen (LinComb L φ ε)) (ht : t.IsGen) :
    (invGen L φ ε t).IsGen := by
  refine (isGen_iff L _).2 fun i j => ?_
  rw [ts_invGen, ts_invGen, lcg_neg, map_inv, map_inv, (isGen_iff L t).1 ht i j, mul_inv]

lemma ts_oneGen (j : PEmpty.{u+1} → L.ι) : ts (oneGen L (Y := Y)) j = 1 := rfl

theorem isGen_oneGen : (oneGen L (Y := Y)).IsGen := by
  refine (isGen_iff L _).2 fun i j => ?_
  rw [ts_oneGen, ts_oneGen, lcg_empty, map_one, map_one, one_mul]

lemma wchart_pu_le (M : LB X) (f : Y ⟶ X) (i j : PUnit.{u+1} → M.ι) :
    wchart M (K := PUnit) (fun _ => f) i ⊓ wchart M (K := PUnit) (fun _ => f) j ≤
      f ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
  wchart_inter_le M (K := PUnit) (fun _ => f) i j PUnit.unit

lemma ts_genPull (M : LB X) (c : Gen M) (f : Y ⟶ X) (j : PUnit.{u+1} → M.ι) :
    ts (genPull M c f) j =
      res (wchart_le M (K := PUnit) (fun _ => f) j PUnit.unit)
        (pullU f _ (c.s (j PUnit.unit))) := rfl

lemma lcg_pull (M : LB X) (f : Y ⟶ X) (i j : PUnit.{u+1} → M.ι) :
    lcg M (K := PUnit) (fun _ => f) (fun _ => 1) i j =
      res (wchart_pu_le M f i j) (pullU f _ (M.g (i PUnit.unit) (j PUnit.unit))) := by
  rw [lcg, Fintype.prod_unique, zpow_one]

theorem isGen_genPull (M : LB X) (c : Gen M) (hc : c.IsGen) (f : Y ⟶ X) :
    (genPull M c f).IsGen := by
  refine (isGen_iff M _).2 fun i j => ?_
  have key := congrArg (fun x => res (wchart_pu_le M f i j) (pullU f _ x))
    (hc (i PUnit.unit) (j PUnit.unit))
  simp only [map_mul, pullU_res, res_res] at key
  rw [ts_genPull, ts_genPull, lcg_pull]
  simp only [res_res]
  exact key

end LB

end

end ReciprocityTheory.ChartRestriction.G.Semi
