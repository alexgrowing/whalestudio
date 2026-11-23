import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi

lemma sec_glue {Y : Scheme.{0}} (W : Y.Opens) {ι : Type} (V : ι → Y.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : W ≤ ⨆ i, V i) (f : ∀ i, Γ(Y, V i))
    (hf : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op).hom (f i) =
      (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op).hom (f j)) :
    ∃! g : Γ(Y, W), ∀ i, (Y.presheaf.map (homOfLE (hle i)).op).hom g = f i := by
  have := TopCat.Sheaf.existsUnique_gluing' Y.sheaf V W (fun i => homOfLE (hle i)) hcov f (fun i j => hf i j)
  exact this

lemma units_glue {Y : Scheme.{0}} (W : Y.Opens) {ι : Type} (V : ι → Y.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : W ≤ ⨆ i, V i) (u : ∀ i, Γ(Y, V i)ˣ)
    (hu : ∀ i j, res (inf_le_left : V i ⊓ V j ≤ V i) (u i) = res (inf_le_right : V i ⊓ V j ≤ V j) (u j)) :
    ∃ w : Γ(Y, W)ˣ, ∀ i, res (hle i) w = u i := by
  have hv : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op).hom ((u i : Γ(Y, V i))) =
      (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op).hom ((u j : Γ(Y, V j))) :=
    fun i j => congrArg Units.val (hu i j)
  have hv' : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op).hom (((u i)⁻¹ : Γ(Y, V i)ˣ) : Γ(Y, V i)) =
      (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op).hom (((u j)⁻¹ : Γ(Y, V j)ˣ) : Γ(Y, V j)) := by
    intro i j
    have := congrArg (fun x => ((x⁻¹ : Γ(Y, V i ⊓ V j)ˣ) : Γ(Y, V i ⊓ V j))) (hu i j)
    simpa [res] using this
  obtain ⟨g, hg, -⟩ := sec_glue W V hle hcov (fun i => (u i : Γ(Y, V i))) hv
  obtain ⟨g', hg', -⟩ := sec_glue W V hle hcov (fun i => ((u i)⁻¹ : Γ(Y, V i)ˣ)) hv'
  have h1 : g * g' = 1 := by
    obtain ⟨o, -, ho⟩ := sec_glue W V hle hcov (fun _ => 1) (fun i j => by simp)
    have e1 := ho (g * g') (fun i => by rw [map_mul, hg i, hg' i]; simp)
    have e2 := ho 1 (fun i => by simp)
    rw [e1, e2]
  refine ⟨⟨g, g', h1, by rw [mul_comm]; exact h1⟩, fun i => ?_⟩
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  exact hg i

section Regroup

open scoped Classical

lemma zpow_fsum {ι M : Type} [CommGroup M] (a : M) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

lemma prod_zpow_of_sameSum {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {M : Type} [CommGroup M]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (hs : LB.SameSum φ ε φ' ε') (e : (Y ⟶ X) → M) :
    ∏ k, e (φ k) ^ ε k = ∏ k', e (φ' k') ^ ε' k' := by
  set S : Finset (Y ⟶ X) := Finset.univ.image φ ∪ Finset.univ.image φ'
  have h1 : ∏ k, e (φ k) ^ ε k = ∏ ψ ∈ S, e ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := φ)
      (fun k _ => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
    refine Finset.prod_congr rfl fun ψ _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, zpow_fsum]
    refine Finset.prod_congr (by ext; simp) fun k hk => ?_
    rw [(Finset.mem_filter.1 hk).2]
  have h2 : ∏ k', e (φ' k') ^ ε' k' = ∏ ψ ∈ S, e ψ ^ (∑ k', if φ' k' = ψ then ε' k' else 0) := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := φ')
      (fun k _ => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
    refine Finset.prod_congr rfl fun ψ _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, zpow_fsum]
    refine Finset.prod_congr (by ext; simp) fun k hk => ?_
    rw [(Finset.mem_filter.1 hk).2]
  rw [h1, h2]
  refine Finset.prod_congr rfl fun ψ _ => ?_
  have := hs ψ
  convert congrArg (fun n => e ψ ^ n) this using 2 <;> simp

end Regroup

section Tr

open scoped Classical

variable {X Y : Scheme.{0}} (L : LB X)

lemma res_refl' {Z : Scheme.{0}} {U : Z.Opens} (x : Γ(Z, U)ˣ) : res (le_refl U) x = x := by
  ext
  show (Z.presheaf.map (𝟙 (op U))).hom x.val = x.val
  rw [CategoryTheory.Functor.map_id]
  rfl

def tr (V : Y.Opens) (ψ : Y ⟶ X) (a b : L.ι) : Γ(Y, V)ˣ :=
  if h : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b) then res h (pullU ψ _ (L.g a b)) else 1

lemma tr_def {V : Y.Opens} {ψ : Y ⟶ X} {a b : L.ι} (h : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    tr L V ψ a b = res h (pullU ψ _ (L.g a b)) := by
  simp [tr, h]

lemma tr_res {V V' : Y.Opens} (hV : V' ≤ V) {ψ : Y ⟶ X} {a b : L.ι} (h : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    res hV (tr L V ψ a b) = tr L V' ψ a b := by
  rw [tr_def L h, tr_def L (hV.trans h), res_res']

lemma tr_self (hL : L.IsLB) {V : Y.Opens} {ψ : Y ⟶ X} {a : L.ι} (h : V ≤ ψ ⁻¹ᵁ L.U a) :
    tr L V ψ a a = 1 := by
  have h' : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U a) := fun y hy => ⟨h hy, h hy⟩
  rw [tr_def L h']
  have e := res_pullU_eq ψ (le_inf le_rfl le_rfl : L.U a ≤ L.U a ⊓ L.U a) h' h (L.g a a)
  rw [e, hL.g_self, map_one, map_one]

lemma tr_cocycle (hL : L.IsLB) {V : Y.Opens} {ψ : Y ⟶ X} {a b c : L.ι}
    (h : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c)) :
    tr L V ψ a b * tr L V ψ b c = tr L V ψ a c := by
  have hab : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b) := fun y hy => (h hy).1
  have hbc : V ≤ ψ ⁻¹ᵁ (L.U b ⊓ L.U c) := fun y hy => ⟨(h hy).1.2, (h hy).2⟩
  have hac : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U c) := fun y hy => ⟨(h hy).1.1, (h hy).2⟩
  rw [tr_def L hab, tr_def L hbc, tr_def L hac]
  have c1 := hL.cocycle a b c
  rw [res_pullU_eq ψ (inf_le_left : L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U b) hab h,
    res_pullU_eq ψ (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U b ⊓ L.U c) hbc h,
    res_pullU_eq ψ (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U c) hac h, ← map_mul, ← map_mul, c1]

lemma linComb_g_res {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j₂ : K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₂) :
    res h ((LB.LinComb L φ ε).g j j₂) = ∏ k, tr L V (φ k) (j k) (j₂ k) ^ ε k := by
  simp only [LB.LinComb]
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : V ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j₂ k)) := fun y hy =>
    ⟨LB.wchart_le L φ j k (h hy).1, LB.wchart_le L φ j₂ k (h hy).2⟩
  rw [map_zpow, tr_def L hk]
  erw [res_res']
  rfl

end Tr

section Transport

open scoped Classical

variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)

def piece (ρ : (Y ⟶ X) → L.ι) : Y.Opens := LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ' (ρ ∘ φ')

lemma le_iSup_piece (hL : L.IsLB) (W : Y.Opens) : W ≤ ⨆ ρ, W ⊓ piece L φ φ' ρ := by
  intro y hy
  have hex : ∀ ψ : Y ⟶ X, ∃ i, ψ.base y ∈ L.U i := fun ψ => by
    have : ψ.base y ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  choose ρ hρ using hex
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨ρ, hy, Set.mem_iInter.2 fun k => hρ (φ k),
    Set.mem_iInter.2 fun k => hρ (φ' k)⟩

variable {L φ φ'}

lemma piece_le_wchart {W : Y.Opens} {ρ : (Y ⟶ X) → L.ι} : W ⊓ piece L φ φ' ρ ≤ LB.wchart L φ (ρ ∘ φ) :=
  fun _ hy => hy.2.1

lemma piece_le_tr {j' : K' → L.ι} {V : Y.Opens} {ρ : (Y ⟶ X) → L.ι} (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ)
    (k' : K') : V ≤ φ' k' ⁻¹ᵁ (L.U (ρ (φ' k')) ⊓ L.U (j' k')) :=
  fun _ hy => ⟨LB.wchart_le L φ' (ρ ∘ φ') k' (hV hy).2.2, LB.wchart_le L φ' j' k' (hV hy).1⟩

variable (L φ φ')

def cand (t : LB.Gen (LB.LinComb L φ ε)) (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) :
    Γ(Y, LB.wchart L φ' j' ⊓ piece L φ φ' ρ)ˣ :=
  (∏ k', tr L (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ *
    res piece_le_wchart (t.s (ρ ∘ φ))

variable {L φ ε φ' ε'}

lemma cand_res (t : LB.Gen (LB.LinComb L φ ε)) (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) {V : Y.Opens}
    (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ) :
    res hV (cand L φ ε φ' ε' t j' ρ) =
      (∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ * res (hV.trans piece_le_wchart) (t.s (ρ ∘ φ)) := by
  simp only [cand, map_mul, map_inv, map_prod, map_zpow]
  erw [res_res']
  congr 2
  exact Finset.prod_congr rfl fun k' _ => by rw [tr_res L hV (piece_le_tr le_rfl k')]

lemma cand_compat (hL : L.IsLB) (hs : LB.SameSum φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (j' : K' → L.ι) (ρ ρ₂ : (Y ⟶ X) → L.ι) :
    res (inf_le_left : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (cand L φ ε φ' ε' t j' ρ) =
      res (inf_le_right : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (cand L φ ε φ' ε' t j' ρ₂) := by
  set V := (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂)
  rw [cand_res, cand_res]

  have hw : V ≤ LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ (ρ₂ ∘ φ) := fun _ hy => ⟨hy.1.2.1, hy.2.2.1⟩
  have hg := congrArg (res hw) (ht (ρ ∘ φ) (ρ₂ ∘ φ))
  erw [map_mul, res_res', res_res'] at hg
  rw [linComb_g_res L φ ε _ _ hw] at hg
  erw [hg]

  have hsum : ∏ k, tr L V (φ k) ((ρ ∘ φ) k) ((ρ₂ ∘ φ) k) ^ ε k =
      ∏ k', tr L V (φ' k') (ρ (φ' k')) (ρ₂ (φ' k')) ^ ε' k' :=
    prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => tr L V ψ (ρ ψ) (ρ₂ ψ))
  rw [hsum]
  have hcoc : ∀ k', tr L V (φ' k') (ρ (φ' k')) (j' k') =
      tr L V (φ' k') (ρ (φ' k')) (ρ₂ (φ' k')) * tr L V (φ' k') (ρ₂ (φ' k')) (j' k') := fun k' =>
    (tr_cocycle L hL (fun _ hy => ⟨⟨(piece_le_tr inf_le_left k' hy).1, (piece_le_tr inf_le_right k' hy).1⟩,
      (piece_le_tr inf_le_left k' hy).2⟩)).symm
  have hA : ∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k' =
      (∏ k', tr L V (φ' k') (ρ (φ' k')) (ρ₂ (φ' k')) ^ ε' k') *
        ∏ k', tr L V (φ' k') (ρ₂ (φ' k')) (j' k') ^ ε' k' := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k' _ => by rw [hcoc k', mul_zpow]
  rw [hA, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rfl

lemma units_ext_cover {Y : Scheme.{0}} (W : Y.Opens) {ι : Type} (V : ι → Y.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : W ≤ ⨆ i, V i) (a b : Γ(Y, W)ˣ) (h : ∀ i, res (hle i) a = res (hle i) b) : a = b := by
  have hv : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op).hom
        ((res (hle i) a : Γ(Y, V i)ˣ) : Γ(Y, V i)) =
      (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op).hom ((res (hle j) a : Γ(Y, V j)ˣ) : Γ(Y, V j)) := by
    intro i j
    have e1 := congrArg Units.val (res_res' (hle i) (inf_le_left : V i ⊓ V j ≤ V i) a)
    have e2 := congrArg Units.val (res_res' (hle j) (inf_le_right : V i ⊓ V j ≤ V j) a)
    simp only [res, Units.coe_map, MonoidHom.coe_coe] at e1 e2 ⊢
    rw [e1, e2]
  obtain ⟨g, -, hu⟩ := sec_glue W V hle hcov (fun i => ((res (hle i) a : Γ(Y, V i)ˣ) : Γ(Y, V i))) hv
  have ea := hu a.val (fun i => rfl)
  have eb := hu b.val (fun i => by rw [h i]; rfl)
  exact Units.ext (ea.trans eb.symm)

theorem gen_transport (hL : L.IsLB) (hs : LB.SameSum φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε'), t'.IsGen ∧ LB.Gen.Corr L φ ε φ' ε' t t' := by
  have glue : ∀ j' : K' → L.ι, ∃ w : Γ(Y, LB.wchart L φ' j')ˣ,
      ∀ ρ, res (inf_le_left : LB.wchart L φ' j' ⊓ piece L φ φ' ρ ≤ _) w = cand L φ ε φ' ε' t j' ρ :=
    fun j' => units_glue (LB.wchart L φ' j') (fun ρ => LB.wchart L φ' j' ⊓ piece L φ φ' ρ) (fun _ => inf_le_left)
      (le_iSup_piece L φ φ' hL _) (cand L φ ε φ' ε' t j') (fun ρ ρ₂ => cand_compat hL hs t ht j' ρ ρ₂)
  choose w hw using glue

  have hwV : ∀ (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) {V : Y.Opens} (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ),
      res (hV.trans inf_le_left) (w j') =
        (∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ * res (hV.trans piece_le_wchart) (t.s (ρ ∘ φ)) := by
    intro j' ρ V hV
    rw [← res_res' (inf_le_left : LB.wchart L φ' j' ⊓ piece L φ φ' ρ ≤ _) hV, hw j' ρ, cand_res]
  refine ⟨⟨w⟩, ?_, ?_⟩
  ·
    intro (i : K' → L.ι) (j : K' → L.ι)
    show res _ (w i) = _ * res _ (w j)
    apply units_ext_cover _ (fun ρ => (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ)
      (fun _ => inf_le_left) (le_iSup_piece L φ φ' hL _)
    intro ρ
    have hVi : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' i ⊓ piece L φ φ' ρ :=
      fun _ hy => ⟨hy.1.1, hy.2⟩
    have hVj : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' j ⊓ piece L φ φ' ρ :=
      fun _ hy => ⟨hy.1.2, hy.2⟩
    erw [map_mul, res_res', res_res']
    have hV12 : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' i ⊓ LB.wchart L φ' j :=
      fun _ hy => hy.1
    erw [hwV i ρ hVi, hwV j ρ hVj, linComb_g_res L φ' ε' i j hV12]
    have hcoc : ∀ k', tr L ((LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j k') =
        tr L _ (φ' k') (ρ (φ' k')) (i k') * tr L _ (φ' k') (i k') (j k') := fun k' =>
      (tr_cocycle L hL (fun _ hy => ⟨⟨(piece_le_tr hVi k' hy).1, (piece_le_tr hVi k' hy).2⟩,
        (piece_le_tr hVj k' hy).2⟩)).symm
    have hA : ∏ k', tr L ((LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j k') ^ ε' k' =
        (∏ k', tr L _ (φ' k') (ρ (φ' k')) (i k') ^ ε' k') * ∏ k', tr L _ (φ' k') (i k') (j k') ^ ε' k' := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k' _ => by rw [hcoc k', mul_zpow]
    rw [hA, mul_inv_rev, ← mul_assoc, mul_inv_cancel_left]
  ·
    intro j j' hj hj' hjj'
    apply units_ext_cover _ (fun ρ => (LB.wchart L φ j ⊓ LB.wchart L φ' j') ⊓ piece L φ φ' ρ)
      (fun _ => inf_le_left) (le_iSup_piece L φ φ' hL _)
    intro ρ
    set O := (LB.wchart L φ j ⊓ LB.wchart L φ' j') ⊓ piece L φ φ' ρ
    have hO' : O ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ := fun _ hy => ⟨hy.1.2, hy.2⟩
    have hOw : O ≤ LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ j := fun _ hy => ⟨hy.2.1, hy.1.1⟩
    erw [res_res', res_res', hwV j' ρ hO']
    have hg := congrArg (res hOw) (ht (ρ ∘ φ) j)
    erw [map_mul, res_res', res_res'] at hg
    rw [linComb_g_res L φ ε _ _ hOw] at hg
    erw [hg]

    let σ : (Y ⟶ X) → L.ι := fun ψ =>
      if h : ∃ k', φ' k' = ψ then j' h.choose else if h₂ : ∃ k, φ k = ψ then j h₂.choose else ρ ψ
    have hσ : ∀ k, σ (φ k) = j k := by
      intro k
      simp only [σ]
      split_ifs with h h₂
      · exact (hjj' k h.choose h.choose_spec.symm).symm
      · exact hj _ _ h₂.choose_spec
      · exact absurd ⟨k, rfl⟩ h₂
    have hσ' : ∀ k', σ (φ' k') = j' k' := by
      intro k'
      simp only [σ]
      rw [dif_pos ⟨k', rfl⟩]
      exact hj' _ _ (⟨k', rfl⟩ : ∃ k₀, φ' k₀ = φ' k').choose_spec
    have hsum : ∏ k, tr L O (φ k) ((ρ ∘ φ) k) (j k) ^ ε k = ∏ k', tr L O (φ' k') (ρ (φ' k')) (j' k') ^ ε' k' := by
      have := prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => tr L O ψ (ρ ψ) (σ ψ))
      simp only [hσ, hσ'] at this
      exact this
    rw [hsum, inv_mul_cancel_left]
    rfl

end Transport

section SecTransport

open scoped Classical

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

abbrev rs {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x : Γ(Z, U)) : Γ(Z, V) :=
  (Z.presheaf.map (homOfLE h).op).hom x

lemma rs_rs {Z : Scheme.{0}} {U W V : Z.Opens} (h : W ≤ U) (h' : V ≤ W) (x : Γ(Z, U)) :
    rs h' (rs h x) = rs (h'.trans h) x := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma rs_units {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x : Γ(Z, U)ˣ) :
    rs h (x : Γ(Z, U)) = ((res h x : Γ(Z, V)ˣ) : Γ(Z, V)) := rfl

lemma rs_mul {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x y : Γ(Z, U)) :
    rs h (x * y) = rs h x * rs h y := map_mul _ x y

lemma sec_ext_cover {Y : Scheme.{0}} (W : Y.Opens) {ι : Type} (V : ι → Y.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : W ≤ ⨆ i, V i) (a b : Γ(Y, W)) (h : ∀ i, rs (hle i) a = rs (hle i) b) : a = b := by
  obtain ⟨g, -, hu⟩ := sec_glue W V hle hcov (fun i => rs (hle i) a) (fun i j => by
    simp only [rs_rs])
  exact (hu a (fun i => rfl)).trans (hu b (fun i => (h i).symm)).symm

def candS (s : LB.Sec (LB.LinComb L φ ε)) (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) :
    Γ(Y, LB.wchart L φ' j' ⊓ piece L φ φ' ρ) :=
  (((∏ k', tr L (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ :
    Γ(Y, LB.wchart L φ' j' ⊓ piece L φ φ' ρ)ˣ) : Γ(Y, _)) * rs piece_le_wchart (s.f (ρ ∘ φ))

lemma candS_rs (s : LB.Sec (LB.LinComb L φ ε)) (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) {V : Y.Opens}
    (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ) :
    rs hV (candS (φ' := φ') (ε' := ε') s j' ρ) =
      (((∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ : Γ(Y, V)ˣ) : Γ(Y, V)) *
        rs (hV.trans piece_le_wchart) (s.f (ρ ∘ φ)) := by
  unfold candS
  rw [rs_mul, rs_units]
  congr 1
  · congr 1
    simp only [map_inv, map_prod, map_zpow]
    congr 1
    exact Finset.prod_congr rfl fun k' _ => by rw [tr_res L hV (piece_le_tr le_rfl k')]
  · exact rs_rs _ _ _

lemma sec_compat_rs (s : LB.Sec (LB.LinComb L φ ε)) (j j₂ : K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₂) :
    rs (h.trans inf_le_left) (s.f j) =
      ((∏ k, tr L V (φ k) (j k) (j₂ k) ^ ε k : Γ(Y, V)ˣ) : Γ(Y, V)) * rs (h.trans inf_le_right) (s.f j₂) := by
  have h' : V ≤ (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂ := h
  have e : rs h' (rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂ ≤ _) (s.f j)) =
      rs h' ((((LB.LinComb L φ ε).g j j₂ : Γ(Y, (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂)ˣ) :
        Γ(Y, (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂)) *
        rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j₂ ≤ _) (s.f j₂)) :=
    congrArg (rs h') (s.compat j j₂)
  rw [rs_rs, rs_mul, rs_rs, rs_units] at e
  erw [linComb_g_res L φ ε j j₂ h] at e
  exact e

lemma candS_compat (hL : L.IsLB) (hs : LB.SameSum φ ε φ' ε') (s : LB.Sec (LB.LinComb L φ ε))
    (j' : K' → L.ι) (ρ ρ₂ : (Y ⟶ X) → L.ι) :
    rs (inf_le_left : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (candS (φ' := φ') (ε' := ε') s j' ρ) =
      rs (inf_le_right : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (candS (φ' := φ') (ε' := ε') s j' ρ₂) := by
  set V := (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂)
  rw [candS_rs, candS_rs]
  have hw : V ≤ LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ (ρ₂ ∘ φ) := fun _ hy => ⟨hy.1.2.1, hy.2.2.1⟩
  have hg := sec_compat_rs s (ρ ∘ φ) (ρ₂ ∘ φ) hw
  erw [hg]
  have hsum : ∏ k, tr L V (φ k) ((ρ ∘ φ) k) ((ρ₂ ∘ φ) k) ^ ε k =
      ∏ k', tr L V (φ' k') (ρ (φ' k')) (ρ₂ (φ' k')) ^ ε' k' :=
    prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => tr L V ψ (ρ ψ) (ρ₂ ψ))
  rw [hsum]
  have hcoc : ∀ k', tr L V (φ' k') (ρ (φ' k')) (j' k') =
      tr L V (φ' k') (ρ (φ' k')) (ρ₂ (φ' k')) * tr L V (φ' k') (ρ₂ (φ' k')) (j' k') := fun k' =>
    (tr_cocycle L hL (fun _ hy => ⟨⟨(piece_le_tr inf_le_left k' hy).1, (piece_le_tr inf_le_right k' hy).1⟩,
      (piece_le_tr inf_le_left k' hy).2⟩)).symm
  have hA : ∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k' =
      (∏ k', tr L V (φ' k') (ρ (φ' k')) (ρ₂ (φ' k')) ^ ε' k') *
        ∏ k', tr L V (φ' k') (ρ₂ (φ' k')) (j' k') ^ ε' k' := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k' _ => by rw [hcoc k', mul_zpow]
  rw [hA, mul_inv_rev, ← mul_assoc, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem sec_transport (hL : L.IsLB) (hs : LB.SameSum φ ε φ' ε') (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε'), ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' →
      (∀ k k', φ k = φ' k' → j k = j' k') →
      rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (s.f j) =
        rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (s'.f j') := by
  have glue : ∀ j' : K' → L.ι, ∃ w : Γ(Y, LB.wchart L φ' j'),
      ∀ ρ, rs (inf_le_left : LB.wchart L φ' j' ⊓ piece L φ φ' ρ ≤ _) w = candS (φ' := φ') (ε' := ε') s j' ρ :=
    fun j' => (sec_glue (LB.wchart L φ' j') (fun ρ => LB.wchart L φ' j' ⊓ piece L φ φ' ρ) (fun _ => inf_le_left)
      (le_iSup_piece L φ φ' hL _) (candS (φ' := φ') (ε' := ε') s j')
      (fun ρ ρ₂ => candS_compat hL hs s j' ρ ρ₂)).exists
  choose w hw using glue
  have hwV : ∀ (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) {V : Y.Opens} (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ),
      rs (hV.trans inf_le_left) (w j') =
        (((∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ : Γ(Y, V)ˣ) : Γ(Y, V)) *
          rs (hV.trans piece_le_wchart) (s.f (ρ ∘ φ)) := by
    intro j' ρ V hV
    rw [← rs_rs (inf_le_left : LB.wchart L φ' j' ⊓ piece L φ φ' ρ ≤ _) hV, hw j' ρ, candS_rs]
  refine ⟨⟨w, ?_⟩, ?_⟩
  · intro (i : K' → L.ι) (j : K' → L.ι)
    show rs _ (w i) = _ * rs _ (w j)
    apply sec_ext_cover _ (fun ρ => (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ)
      (fun _ => inf_le_left) (le_iSup_piece L φ φ' hL _)
    intro ρ
    have hVi : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' i ⊓ piece L φ φ' ρ :=
      fun _ hy => ⟨hy.1.1, hy.2⟩
    have hVj : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' j ⊓ piece L φ φ' ρ :=
      fun _ hy => ⟨hy.1.2, hy.2⟩
    have hV12 : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' i ⊓ LB.wchart L φ' j :=
      fun _ hy => hy.1
    erw [rs_mul, rs_rs, rs_rs, rs_units]
    erw [hwV i ρ hVi, hwV j ρ hVj, linComb_g_res L φ' ε' i j hV12]
    have hcoc : ∀ k', tr L ((LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j k') =
        tr L _ (φ' k') (ρ (φ' k')) (i k') * tr L _ (φ' k') (i k') (j k') := fun k' =>
      (tr_cocycle L hL (fun _ hy => ⟨⟨(piece_le_tr hVi k' hy).1, (piece_le_tr hVi k' hy).2⟩,
        (piece_le_tr hVj k' hy).2⟩)).symm
    have hA : ∏ k', tr L ((LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j k') ^ ε' k' =
        (∏ k', tr L _ (φ' k') (ρ (φ' k')) (i k') ^ ε' k') * ∏ k', tr L _ (φ' k') (i k') (j k') ^ ε' k' := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k' _ => by rw [hcoc k', mul_zpow]
    rw [hA, mul_inv_rev, ← mul_assoc, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  · intro j j' hj hj' hjj'
    apply sec_ext_cover _ (fun ρ => (LB.wchart L φ j ⊓ LB.wchart L φ' j') ⊓ piece L φ φ' ρ)
      (fun _ => inf_le_left) (le_iSup_piece L φ φ' hL _)
    intro ρ
    set O := (LB.wchart L φ j ⊓ LB.wchart L φ' j') ⊓ piece L φ φ' ρ
    have hO' : O ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ := fun _ hy => ⟨hy.1.2, hy.2⟩
    have hOw : O ≤ LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ j := fun _ hy => ⟨hy.2.1, hy.1.1⟩
    erw [rs_rs, rs_rs, hwV j' ρ hO']
    have hg := sec_compat_rs s (ρ ∘ φ) j hOw
    erw [hg]
    let σ : (Y ⟶ X) → L.ι := fun ψ =>
      if h : ∃ k', φ' k' = ψ then j' h.choose else if h₂ : ∃ k, φ k = ψ then j h₂.choose else ρ ψ
    have hσ : ∀ k, σ (φ k) = j k := by
      intro k
      simp only [σ]
      split_ifs with h h₂
      · exact (hjj' k h.choose h.choose_spec.symm).symm
      · exact hj _ _ h₂.choose_spec
      · exact absurd ⟨k, rfl⟩ h₂
    have hσ' : ∀ k', σ (φ' k') = j' k' := by
      intro k'
      simp only [σ]
      rw [dif_pos ⟨k', rfl⟩]
      exact hj' _ _ (⟨k', rfl⟩ : ∃ k₀, φ' k₀ = φ' k').choose_spec
    have hsum : ∏ k, tr L O (φ k) ((ρ ∘ φ) k) (j k) ^ ε k = ∏ k', tr L O (φ' k') (ρ (φ' k')) (j' k') ^ ε' k' := by
      have := prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => tr L O ψ (ρ ψ) (σ ψ))
      simp only [hσ, hσ'] at this
      exact this
    rw [hsum, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

end SecTransport

section FSum

open scoped Classical

variable {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

def fsum (φ : K → (Y ⟶ X)) (ε : K → ℤ) : (Y ⟶ X) →₀ ℤ := ∑ k, Finsupp.single (φ k) (ε k)

lemma fsum_apply (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : Y ⟶ X) :
    fsum φ ε ψ = ∑ k, if φ k = ψ then ε k else 0 := by
  simp only [fsum, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]

lemma sameSum_iff_fsum (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    LB.SameSum φ ε φ' ε' ↔ fsum φ ε = fsum φ' ε' := by
  constructor
  · intro h
    ext ψ
    rw [fsum_apply, fsum_apply]
    convert h ψ using 2 <;> simp
  · intro h ψ
    have := congrArg (fun f => f ψ) h
    simp only [fsum_apply] at this
    convert this using 2 <;> simp

lemma fsum_sumElim {K₂ : Type} [Fintype K₂] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) :
    fsum (Sum.elim φ φ₂) (Sum.elim ε ε₂) = fsum φ ε + fsum φ₂ ε₂ := by
  simp [fsum, Fintype.sum_sum_type]

lemma fsum_neg (φ : K → (Y ⟶ X)) (ε : K → ℤ) : fsum φ (fun k => - ε k) = - fsum φ ε := by
  simp [fsum, Finsupp.single_neg]

lemma fsum_smul (φ : K → (Y ⟶ X)) (ε : K → ℤ) (n : ℤ) : fsum φ (fun k => n * ε k) = n • fsum φ ε := by
  simp [fsum, Finset.smul_sum, Finsupp.smul_single]

lemma fsum_comp (φ : K → (Y ⟶ X)) (ε : K → ℤ) {Z : Scheme.{0}} (h : Z ⟶ Y) :
    fsum (fun k => h ≫ φ k) ε = Finsupp.mapDomain (fun ψ => h ≫ ψ) (fsum φ ε) := by
  simp [fsum, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]

lemma fsum_empty : fsum (Y := Y) (X := X) (K := PEmpty) PEmpty.elim PEmpty.elim = 0 := by
  simp [fsum]

end FSum

end ReciprocityTheory.ChartRestriction.G.DVR
