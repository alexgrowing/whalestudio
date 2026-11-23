import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArcSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

section Stalk

variable {X Y Z : Scheme.{0}}

open Classical in

def gm (f : Y ⟶ X) (y : Y) (U : X.Opens) : Γ(X, U)ˣ →* (Y.presheaf.stalk y)ˣ :=
  if h : f y ∈ U then (Units.map (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.toMonoidHom).comp (pullU f U) else 1

theorem gm_val (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    (gm f y U a).val = (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a.val) := by
  simp [gm, h, pullU]

theorem gm_res (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)ˣ) :
    gm f y V (res hle a) = gm f y U a := by
  apply Units.ext
  rw [gm_val f y V h, gm_val f y U (hle h)]
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have e1 := Scheme.Hom.naturality f (homOfLE hle).op
  rw [← Y.presheaf.germ_res (homOfLE (Scheme.Hom.preimage_mono f hle)) y h]
  rw [CommRingCat.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e1]
  rfl

theorem gm_pull (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    gm f z (g ⁻¹ᵁ U) (pullU g U a) = gm (f ≫ g) z U a := by
  apply Units.ext
  rw [gm_val f z _ h, gm_val (f ≫ g) z U h]
  simp only [pullU, Units.coe_map, MonoidHom.coe_coe]
  rfl

theorem unit_ext {V : X.Opens} {a b : Γ(X, V)ˣ} (h : ∀ x ∈ V, gm (𝟙 X) x V a = gm (𝟙 X) x V b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext X.sheaf V
  intro x hx
  have e := congrArg Units.val (h x hx)
  rw [gm_val _ _ _ hx, gm_val _ _ _ hx] at e
  exact e

theorem glue_unit {J : Type} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V) (hc : V ≤ iSup W)
    (u : ∀ i, Γ(X, W i)ˣ)
    (h : ∀ i j, ∀ x ∈ W i ⊓ W j, gm (𝟙 X) x (W i) (u i) = gm (𝟙 X) x (W j) (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  have comp : ∀ t : ∀ i, Γ(X, W i)ˣ,
      (∀ i j, ∀ x ∈ W i ⊓ W j, gm (𝟙 X) x (W i) (t i) = gm (𝟙 X) x (W j) (t j)) →
      TopCat.Presheaf.IsCompatible X.sheaf.1 W (fun i => ((t i : Γ(X, W i)ˣ) : Γ(X, W i))) := by
    intro t ht i j
    apply TopCat.Presheaf.section_ext X.sheaf (W i ⊓ W j)
    intro x hx
    have e := congrArg Units.val (ht i j x hx)
    rw [gm_val _ _ _ hx.1, gm_val _ _ _ hx.2] at e
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact e
  have hinv : ∀ i j, ∀ x ∈ W i ⊓ W j, gm (𝟙 X) x (W i) (u i)⁻¹ = gm (𝟙 X) x (W j) (u j)⁻¹ := by
    intro i j x hx
    rw [map_inv, map_inv, h i j x hx]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun i => homOfLE (hW i)) hc _
    (comp u h)
  obtain ⟨s', hs', -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun i => homOfLE (hW i)) hc _
    (comp (fun i => (u i)⁻¹) hinv)
  have hss : s * s' = 1 := by
    apply TopCat.Presheaf.section_ext X.sheaf V
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hx)
    have a1 := congrArg (X.sheaf.presheaf.germ (W i) x hi) (hs i)
    have a2 := congrArg (X.sheaf.presheaf.germ (W i) x hi) (hs' i)
    rw [TopCat.Presheaf.germ_res_apply] at a1 a2
    rw [map_mul, map_one, a1, a2]
    have e := congrArg (X.sheaf.presheaf.germ (W i) x hi) (Units.mul_inv (u i))
    exact (map_mul _ _ _).symm.trans (e.trans (map_one _))
  refine ⟨⟨s, s', hss, (mul_comm s' s).trans hss⟩, fun i => Units.ext ?_⟩
  exact hs i

theorem exists_chart {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i := by
  have := hL.cover
  have hx : x ∈ (⨆ i, L.U i : X.Opens) := by rw [this]; trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using hx

theorem gm_cocycle {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i j k : L.ι} (hi : f y ∈ L.U i) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gm f y _ (L.g i j) * gm f y _ (L.g j k) = gm f y _ (L.g i k) := by
  have hijk : f y ∈ L.U i ⊓ L.U j ⊓ L.U k := ⟨⟨hi, hj⟩, hk⟩
  rw [← gm_res f y (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) hijk,
    ← gm_res f y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) hijk,
    ← gm_res f y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) hijk,
    ← map_mul, hL.cocycle]

theorem gm_self {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i : L.ι} (hi : f y ∈ L.U i) :
    gm f y (L.U i ⊓ L.U i) (L.g i i) = 1 := by
  rw [← gm_res f y (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) hi, hL.g_self i, map_one]

variable {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem mem_pull {x : X'} {J : PUnit → L.ι} : x ∈ (L.pull F).U J ↔ F x ∈ L.U (J PUnit.unit) := by
  simp only [LB.pull, LB.LinComb, LB.wchart]
  simp
  exact ⟨fun h => h _, fun h _ => h⟩

def gw (w : LB.Iso L' (L.pull F)) (f : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w.s (fun _ => j, k))

def PGen (w : LB.Iso L' (L.pull F)) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X') (y : Y) (j j' : L.ι) (k k' : L'.ι), F (f y) ∈ L.U j → F (f y) ∈ L.U j' → f y ∈ L'.U k →
    f y ∈ L'.U k' → gw w f y j k = gm (f ≫ F) y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gw w f y j' k'

theorem gm_div_g (f : Y ⟶ X') (y : Y) (j j' : L.ι) (k k' : L'.ι) (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j')
    (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gm f y ((L.pull F).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull F).U (fun _ => j') ⊓ L'.U k'))
      ((LB.div (L.pull F) L').g (fun _ => j, k) (fun _ => j', k')) =
      gm (f ≫ F) y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ := by
  have hW : f y ∈ ((L.pull F).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull F).U (fun _ => j') ⊓ L'.U k')) :=
    ⟨⟨mem_pull (J := fun _ => j) |>.2 hj, hk⟩, ⟨mem_pull (J := fun _ => j') |>.2 hj', hk'⟩⟩
  dsimp only [LB.div]
  rw [map_mul, map_inv]
  erw [gm_res f y _ hW, gm_res f y _ hW]
  congr 1
  dsimp only [LB.pull, LB.LinComb]
  rw [Fintype.prod_unique, zpow_one]
  have h1 : f y ∈ LB.wchart L (fun _ : PUnit => F) (fun _ => j) ⊓ LB.wchart L (fun _ : PUnit => F) (fun _ => j') :=
    ⟨mem_pull (J := fun _ => j) |>.2 hj, mem_pull (J := fun _ => j') |>.2 hj'⟩
  erw [gm_res f y _ h1,
    gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩]

theorem isGen_iff (w : LB.Iso L' (L.pull F)) : w.IsGen ↔ PGen w := by
  constructor
  · intro hg Y f y j j' k k' hj hj' hk hk'
    have hW : f y ∈ ((L.pull F).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull F).U (fun _ => j') ⊓ L'.U k')) :=
      ⟨⟨mem_pull (J := fun _ => j) |>.2 hj, hk⟩, ⟨mem_pull (J := fun _ => j') |>.2 hj', hk'⟩⟩
    have e := congrArg (gm f y _) (hg (fun _ => j, k) (fun _ => j', k'))
    erw [map_mul, gm_res f y _ hW, gm_res f y _ hW, gm_div_g f y j j' k k' hj hj' hk hk'] at e
    exact e
  · intro hp p q
    apply unit_ext
    intro x hx
    erw [map_mul, gm_res _ _ _ hx, gm_res _ _ _ hx]
    obtain ⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩⟩ := hx
    have e := hp X' (𝟙 X') x (p.1 PUnit.unit) (q.1 PUnit.unit) p.2 q.2 (mem_pull.1 hp1) (mem_pull.1 hq1) hp2 hq2
    show gw w (𝟙 X') x (p.1 PUnit.unit) p.2 =
      gm (𝟙 X') x ((L.pull F).U (fun _ => p.1 PUnit.unit) ⊓ L'.U p.2 ⊓
        ((L.pull F).U (fun _ => q.1 PUnit.unit) ⊓ L'.U q.2))
        ((LB.div (L.pull F) L').g (fun _ => p.1 PUnit.unit, p.2) (fun _ => q.1 PUnit.unit, q.2)) *
        gw w (𝟙 X') x (q.1 PUnit.unit) q.2
    rw [e, gm_div_g (𝟙 X') x (p.1 PUnit.unit) (q.1 PUnit.unit) p.2 q.2 (mem_pull.1 hp1) (mem_pull.1 hq1) hp2 hq2]

def PMaps (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι), (∀ k, F (φ' k (r z)) ∈ L.U (p k)) →
    (∀ k, φ' k (r z) ∈ L'.U (q k)) →
    gm (r ≫ h) z (LB.wchart L φ p) (t.s p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q)

private theorem mem_wchart_lemma {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (x : Y) : x ∈ LB.wchart L φ j ↔ ∀ k, φ k x ∈ L.U (j k) := by
  simp [LB.wchart]

private theorem gm_lin_lemma_2 (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Z Y' : Scheme.{0}}
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (P : K → PUnit → L.ι) (q : K → L'.ι)
    (hz : r z ∈ LB.wchart (L.pull F) φ' P ⊓ LB.wchart L' φ' q) :
    gm r z (LB.wchart (L.pull F) φ' P ⊓ LB.wchart L' φ' q) ((LB.linCombIso w φ' ε).s (P, q)) =
      ∏ k, gw w (r ≫ φ' k) z (P k PUnit.unit) (q k) ^ ε k := by
  dsimp only [LB.linCombIso]
  refine (map_prod (gm r z (LB.wchart (L.pull F) φ' P ⊓ LB.wchart L' φ' q)) _ _).trans ?_
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (map_zpow _ _ _).trans ?_
  congr 1
  have hk : r z ∈ φ' k ⁻¹ᵁ ((L.pull F).U (P k) ⊓ L'.U (q k)) :=
    ⟨(mem_wchart_lemma _ _ _ _).1 hz.1 k, (mem_wchart_lemma _ _ _ _).1 hz.2 k⟩
  erw [gm_res r z _ hz]
  exact gm_pull r (φ' k) z ((L.pull F).U (P k) ⊓ L'.U (q k)) hk (w.s (P k, q k))

theorem maps_iff (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (b : LB.Gen (LB.LinComb (L.pull F) φ' ε))
    (hle : ∀ j : K → PUnit → L.ι, LB.wchart (L.pull F) φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j k PUnit.unit))
    (hb : ∀ j, b.s j = res (hle j) (pullU h _ (t.s (fun k => j k PUnit.unit)))) :
    LB.Gen.Maps (LB.linCombIso w φ' ε) a b ↔ PMaps w φ' φ ε a t h := by
  constructor
  · intro hM Z r z p q hp hq
    have hz : r z ∈ LB.wchart (L.pull F) φ' (fun k _ => p k) ⊓ LB.wchart L' φ' q :=
      ⟨(mem_wchart_lemma _ _ _ _).2 fun k => mem_pull (J := fun _ => p k) |>.2 (hp k),
        (mem_wchart_lemma _ _ _ _).2 hq⟩
    have e := congrArg (gm r z _) (hM ((fun k _ => p k), q))
    erw [map_mul, gm_res r z _ hz, hb, gm_res r z _ hz.1, gm_pull r h z _ (hle _ hz.1),
      gm_lin_lemma_2 w φ' ε r z _ q hz, gm_res r z _ hz] at e
    exact e
  · intro hP p
    apply unit_ext
    intro x hx
    have e := hP Y' (𝟙 Y') x (fun k => p.1 k PUnit.unit) p.2
      (fun k => mem_pull.1 ((mem_wchart_lemma _ _ _ _).1 hx.1 k)) ((mem_wchart_lemma _ _ _ _).1 hx.2)
    erw [map_mul, gm_res _ x _ hx, hb, gm_res _ x _ hx.1, gm_pull _ h x _ (hle _ hx.1),
      gm_lin_lemma_2 w φ' ε (𝟙 Y') x p.1 p.2 hx, gm_res _ x _ hx]
    exact e

end Stalk

section Tri

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

def Tri (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (w'' : LB.Iso L'' (L.pull (F' ≫ F))) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : L.ι) (i : L'.ι) (k : L''.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i →
    f y ∈ L''.U k → gw w'' f y j k = gw w (f ≫ F') y j i * gw w' f y i k

theorem mem_pull₂ {x : X''} {J : PUnit → L.ι} : x ∈ (L.pull (F' ≫ F)).U J ↔ F (F' x) ∈ L.U (J PUnit.unit) := by
  simp only [LB.pull, LB.LinComb, LB.wchart]
  simp
  exact ⟨fun h => h _, fun h _ => h⟩

theorem indep_comp (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w') (hL : L.IsLB)
    (hL'' : L''.IsLB) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have e1 := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have e2 := hw' Y f y i i' k k hi hi' hk hk
  rw [e1, e2, gm_self hL ((f ≫ F') ≫ F) y hj, gm_self hL'' f y hk]
  simp only [one_mul, inv_one, mul_one]
  rw [mul_mul_mul_comm, inv_mul_cancel, one_mul]

theorem indep_cancel (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull (F' ≫ F))) (hw : PGen w) (hw'' : PGen w'')
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j j' : L.ι) (i : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hj' : F (F' (f y)) ∈ L.U j') (hi : F' (f y) ∈ L'.U i) (hk : f y ∈ L''.U k) :
    (gw w (f ≫ F') y j i)⁻¹ * gw w'' f y j k = (gw w (f ≫ F') y j' i)⁻¹ * gw w'' f y j' k := by
  have e1 := hw Y (f ≫ F') y j j' i i hj hj' hi hi
  have e2 := hw'' Y f y j j' k k hj hj' hk hk
  rw [e1, e2, gm_self hL' (f ≫ F') y hi, gm_self hL'' f y hk]
  simp only [inv_one, mul_one, Category.assoc]
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem exists_comp (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL : L.IsLB) (hL'' : L''.IsLB) :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have hsub1 : ∀ (J : PUnit → L.ι) (k : L''.ι) (i : L'.ι),
      (L.pull (F' ≫ F)).U J ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i ≤ F' ⁻¹ᵁ ((L.pull F).U J ⊓ L'.U i) :=
    fun J k i x hx => ⟨mem_pull.2 (mem_pull₂.1 hx.1.1), hx.2⟩
  have hsub2 : ∀ (J : PUnit → L.ι) (k : L''.ι) (i : L'.ι),
      (L.pull (F' ≫ F)).U J ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k :=
    fun J k i x hx => ⟨mem_pull.2 hx.2, hx.1.2⟩
  have hu : ∀ (J : PUnit → L.ι) (k : L''.ι) (i : L'.ι) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y)
      (hy : f y ∈ (L.pull (F' ≫ F)).U J ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i),
      gm f y _ (res (hsub1 J k i) (pullU F' _ (w.s (J, i))) * res (hsub2 J k i) (w'.s (fun _ => i, k))) =
        gw w (f ≫ F') y (J PUnit.unit) i * gw w' f y i k := by
    intro J k i Y f y hy
    rw [map_mul]
    erw [gm_res f y _ hy, gm_res f y _ hy]
    congr 1
    exact gm_pull f F' y _ (hsub1 J k i hy) _
  have hs : ∀ p : (LB.div (L.pull (F' ≫ F)) L'').ι, ∃ s : Γ(X'', (L.pull (F' ≫ F)).U p.1 ⊓ L''.U p.2)ˣ,
      ∀ i, res (inf_le_left : (L.pull (F' ≫ F)).U p.1 ⊓ L''.U p.2 ⊓ F' ⁻¹ᵁ L'.U i ≤ _) s =
        res (hsub1 p.1 p.2 i) (pullU F' _ (w.s (p.1, i))) * res (hsub2 p.1 p.2 i) (w'.s (fun _ => i, p.2)) := by
    intro p
    refine glue_unit _ (fun i => (L.pull (F' ≫ F)).U p.1 ⊓ L''.U p.2 ⊓ F' ⁻¹ᵁ L'.U i)
      (fun i => inf_le_left) ?_ (fun i => res (hsub1 p.1 p.2 i) (pullU F' _ (w.s (p.1, i))) *
        res (hsub2 p.1 p.2 i) (w'.s (fun _ => i, p.2))) ?_
    · intro x hx
      obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨hx, hi⟩⟩
    · intro i i' x hx
      rw [hu p.1 p.2 i (𝟙 X'') x hx.1, hu p.1 p.2 i' (𝟙 X'') x hx.2]
      exact indep_comp w w' hw hw' hL hL'' (𝟙 X'') x (p.1 PUnit.unit) i i' p.2
        (mem_pull₂.1 hx.1.1.1) hx.1.2 hx.2.2 hx.1.1.2
  choose s hs using hs
  refine ⟨⟨s⟩, ?_⟩
  intro Y f y j i k hj hi hk
  have hy : f y ∈ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i :=
    ⟨⟨mem_pull₂ (J := fun _ => j) |>.2 hj, hk⟩, hi⟩
  show gm f y _ (s (fun _ => j, k)) = _
  rw [← gm_res f y (inf_le_left : (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i ≤ _) hy,
    hs (fun _ => j, k) i, hu (fun _ => j) k i f y hy]

theorem exists_cancel (hL : L.IsLB) (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull (F' ≫ F))) (hw : PGen w)
    (hw'' : PGen w'') (hL' : L'.IsLB) (hL'' : L''.IsLB) :
    ∃ w' : LB.Iso L'' (L'.pull F'), Tri w w' w'' := by
  have hsub1 : ∀ (I : PUnit → L'.ι) (k : L''.ι) (j : L.ι),
      (L'.pull F').U I ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ≤
        F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U (I PUnit.unit)) :=
    fun I k j x hx => ⟨mem_pull.2 hx.2, mem_pull.1 hx.1.1⟩
  have hsub2 : ∀ (I : PUnit → L'.ι) (k : L''.ι) (j : L.ι),
      (L'.pull F').U I ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k :=
    fun I k j x hx => ⟨mem_pull₂.2 hx.2, hx.1.2⟩
  have hu : ∀ (I : PUnit → L'.ι) (k : L''.ι) (j : L.ι) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y)
      (hy : f y ∈ (L'.pull F').U I ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j)),
      gm f y _ ((res (hsub1 I k j) (pullU F' _ (w.s (fun _ => j, I PUnit.unit))))⁻¹ *
          res (hsub2 I k j) (w''.s (fun _ => j, k))) =
        (gw w (f ≫ F') y j (I PUnit.unit))⁻¹ * gw w'' f y j k := by
    intro I k j Y f y hy
    rw [map_mul, map_inv]
    erw [gm_res f y _ hy, gm_res f y _ hy]
    congr 2
    exact gm_pull f F' y _ (hsub1 I k j hy) _
  have hs : ∀ p : (LB.div (L'.pull F') L'').ι, ∃ s : Γ(X'', (L'.pull F').U p.1 ⊓ L''.U p.2)ˣ,
      ∀ j, res (inf_le_left : (L'.pull F').U p.1 ⊓ L''.U p.2 ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ≤ _) s =
        (res (hsub1 p.1 p.2 j) (pullU F' _ (w.s (fun _ => j, p.1 PUnit.unit))))⁻¹ *
          res (hsub2 p.1 p.2 j) (w''.s (fun _ => j, p.2)) := by
    intro p
    refine glue_unit _ (fun j => (L'.pull F').U p.1 ⊓ L''.U p.2 ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j))
      (fun j => inf_le_left) ?_ (fun j => (res (hsub1 p.1 p.2 j) (pullU F' _ (w.s (fun _ => j, p.1 PUnit.unit))))⁻¹ *
          res (hsub2 p.1 p.2 j) (w''.s (fun _ => j, p.2))) ?_
    · intro x hx
      obtain ⟨j, hj⟩ := exists_chart hL (F (F' x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, ⟨hx, hj⟩⟩
    · intro j j' x hx
      rw [hu p.1 p.2 j (𝟙 X'') x hx.1, hu p.1 p.2 j' (𝟙 X'') x hx.2]
      exact indep_cancel w w'' hw hw'' hL' hL'' (𝟙 X'') x j j' (p.1 PUnit.unit) p.2
        hx.1.2 hx.2.2 (mem_pull.1 hx.1.1.1) hx.1.1.2
  choose s hs using hs
  refine ⟨⟨s⟩, ?_⟩
  intro Y f y j i k hj hi hk
  have hy : f y ∈ (L'.pull F').U (fun _ => i) ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) :=
    ⟨⟨mem_pull (J := fun _ => i) |>.2 hi, hk⟩, hj⟩
  show _ = _ * gm f y _ (s (fun _ => i, k))
  rw [← gm_res f y (inf_le_left : (L'.pull F').U (fun _ => i) ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ≤ _) hy,
    hs (fun _ => i, k) j, hu (fun _ => i) k j f y hy, mul_inv_cancel_left]

variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}

theorem Tri.pgen_comp (T : Tri w w' w'') (hL' : L'.IsLB) (hw : PGen w) (hw' : PGen w') : PGen w'' := by
  have key : ∀ {G : Type _} [CommGroup G] (b c p q : G), b * 1⁻¹ * p * (1 * c⁻¹ * q) = b * c⁻¹ * (p * q) := by
    intro G _ b c p q
    simp only [inv_one, mul_one, one_mul]
    exact mul_mul_mul_comm _ _ _ _
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨i, hi⟩ := exists_chart hL' (F' (f y))
  rw [T Y f y j i k hj hi hk, T Y f y j' i k' hj' hi hk',
    hw Y (f ≫ F') y j j' i i hj hj' hi hi, hw' Y f y i i k k' hi hi hk hk',
    gm_self hL' (f ≫ F') y hi, Category.assoc]
  exact key _ _ _ _

theorem Tri.pgen_cancel (T : Tri w w' w'') (hL : L.IsLB) (hw : PGen w) (hw'' : PGen w'') : PGen w' := by
  have key : ∀ {G : Type _} [CommGroup G] (a d p q : G),
      (1 * a⁻¹ * p)⁻¹ * (1 * d⁻¹ * q) = a * d⁻¹ * (p⁻¹ * q) := by
    intro G _ a d p q
    simp only [one_mul]
    rw [mul_inv_rev, inv_inv, mul_comm p⁻¹ a, mul_mul_mul_comm]
  intro Y f y i i' k k' hi hi' hk hk'
  obtain ⟨j, hj⟩ := exists_chart hL (F (F' (f y)))
  have t1 := inv_mul_eq_iff_eq_mul.mpr (T Y f y j i k hj hi hk)
  have t2 := inv_mul_eq_iff_eq_mul.mpr (T Y f y j i' k' hj hi' hk')
  rw [← t1, ← t2, hw'' Y f y j j k k' hj hj hk hk', hw Y (f ≫ F') y j j i i' hj hj hi hi',
    gm_self hL (f ≫ F' ≫ F) y hj, gm_self hL ((f ≫ F') ≫ F) y hj]
  exact key _ _ _ _

variable {K : Type} [Fintype K] {Y Y' Y'' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {φ'' : K → (Y'' ⟶ X'')}
  {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L' φ' ε)} {t'' : LB.Gen (LB.LinComb L'' φ'' ε)}
  {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}

theorem Tri.prod (T : Tri w w' w'') (hc : ∀ k, φ'' k ≫ F' = h' ≫ φ' k) (Z : Scheme.{0}) (r : Z ⟶ Y'') (z : Z)
    (p : K → L.ι) (i : K → L'.ι) (q : K → L''.ι) (hp : ∀ k, F (F' (φ'' k (r z))) ∈ L.U (p k))
    (hi : ∀ k, F' (φ'' k (r z)) ∈ L'.U (i k)) (hq : ∀ k, φ'' k (r z) ∈ L''.U (q k)) :
    ∏ k, gw w'' (r ≫ φ'' k) z (p k) (q k) ^ ε k =
      (∏ k, gw w ((r ≫ h') ≫ φ' k) z (p k) (i k) ^ ε k) * ∏ k, gw w' (r ≫ φ'' k) z (i k) (q k) ^ ε k := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow, T Z (r ≫ φ'' k) z (p k) (i k) (q k) (hp k) (hi k) (hq k)]
  have e : (r ≫ φ'' k) ≫ F' = (r ≫ h') ≫ φ' k := by
    rw [Category.assoc, hc k, Category.assoc]
  rw [e]

theorem pt_eq (hc : ∀ k, φ'' k ≫ F' = h' ≫ φ' k) (k : K) (y : Y'') : φ' k (h' y) = F' (φ'' k y) := by
  rw [← Scheme.Hom.comp_apply, ← hc k]
  rfl

theorem Tri.pmaps_comp (T : Tri w w' w'') (hL' : L'.IsLB) (hc : ∀ k, φ'' k ≫ F' = h' ≫ φ' k)
    (H : PMaps w φ' φ ε t' t h) (H' : PMaps w' φ'' φ' ε t'' t' h') : PMaps w'' φ'' φ ε t'' t (h' ≫ h) := by
  intro Z r z p q hp hq
  choose i hi using fun k => exists_chart hL' (F' (φ'' k (r z)))
  have hp' : ∀ k, F (φ' k ((r ≫ h') z)) ∈ L.U (p k) := fun k => by
    rw [Scheme.Hom.comp_apply, pt_eq hc]; exact hp k
  have hi' : ∀ k, φ' k ((r ≫ h') z) ∈ L'.U (i k) := fun k => by
    rw [Scheme.Hom.comp_apply, pt_eq hc]; exact hi k
  rw [T.prod hc Z r z p i q hp hi hq, ← Category.assoc, H Z (r ≫ h') z p i hp' hi', H' Z r z i q hi hq,
    mul_assoc]

theorem Tri.pmaps_cancel (T : Tri w w' w'') (hL : L.IsLB) (hc : ∀ k, φ'' k ≫ F' = h' ≫ φ' k)
    (H : PMaps w φ' φ ε t' t h) (H'' : PMaps w'' φ'' φ ε t'' t (h' ≫ h)) : PMaps w' φ'' φ' ε t'' t' h' := by
  intro Z r z p q hp hq
  choose j hj using fun k => exists_chart hL (F (F' (φ'' k (r z))))
  have hj' : ∀ k, F (φ' k ((r ≫ h') z)) ∈ L.U (j k) := fun k => by
    rw [Scheme.Hom.comp_apply, pt_eq hc]; exact hj k
  have hp' : ∀ k, φ' k ((r ≫ h') z) ∈ L'.U (p k) := fun k => by
    rw [Scheme.Hom.comp_apply, pt_eq hc]; exact hp k
  have e1 := H Z (r ≫ h') z j p hj' hp'
  have e2 := H'' Z r z j q hj hq
  rw [Category.assoc, e2, T.prod hc Z r z j p q hj hp hq, mul_assoc] at e1
  exact (mul_left_cancel e1).symm

end Tri

theorem isPullCubical_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (m : CubeMap G' G) {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') :
    m.IsPullCubical c' c ↔ ∃ w : LB.Iso L'.L (L.L.pull m.F), PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e ∧
      PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t m.F3 := by
  unfold CubeMap.IsPullCubical
  refine exists_congr fun w => and_congr (isGen_iff w) (and_congr ?_ ?_)
  · exact maps_iff w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e
      (m.rigPull L.L L.rig) (fun j => rigPull_le m.F m.e m.e_comm L.L j) (fun j => rfl)
  · exact maps_iff w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t m.F3
      (m.thetaPull L.L c.t) (fun j => m.theta_le L.L j) (fun j => rfl)

theorem pullCubComp : PullCubCompSt := by
  intro S S' S'' G G' G'' _ _ _ _ _ _ m m' n L L' L'' c c' c'' hF hF3 he hm hm'
  obtain ⟨nF, nF3, ne, hne, hnp⟩ := n
  dsimp only at hF hF3 he
  subst hF hF3 he
  rw [isPullCubical_iff] at hm hm' ⊢
  obtain ⟨w, hw, hr, ht⟩ := hm
  obtain ⟨w', hw', hr', ht'⟩ := hm'
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' hw hw' L.isLB L''.isLB
  exact ⟨w'', T.pgen_comp L'.isLB hw hw', T.pmaps_comp L'.isLB (fun _ => m'.e_comm) hr hr',
    T.pmaps_comp L'.isLB (fun I => m'.psum_comm I.down) ht ht'⟩

theorem pullCubCancel : PullCubCancelSt := by
  intro S S' S'' G G' G'' _ _ _ _ _ _ m m' n L L' L'' c c' c'' hF hF3 he hm hn
  obtain ⟨nF, nF3, ne, hne, hnp⟩ := n
  dsimp only at hF hF3 he
  subst hF hF3 he
  rw [isPullCubical_iff] at hm hn ⊢
  obtain ⟨w, hw, hr, ht⟩ := hm
  obtain ⟨w'', hw'', hr'', ht''⟩ := hn
  obtain ⟨w', T⟩ := exists_cancel L.isLB w w'' hw hw'' L'.isLB L''.isLB
  exact ⟨w', T.pgen_cancel L.isLB hw hw'', T.pmaps_cancel L.isLB (fun _ => m'.e_comm) hr hr'',
    T.pmaps_cancel L.isLB (fun I => m'.psum_comm I.down) ht ht''⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
