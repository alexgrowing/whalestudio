import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

private lemma res_res_lemma {S : Scheme.{0}} {U V W : S.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(S, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  have hc : S.presheaf.map (homOfLE h1).op ≫ S.presheaf.map (homOfLE h2).op =
      S.presheaf.map (homOfLE (h2.trans h1)).op := by
    rw [← Functor.map_comp]
    rfl
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← hc]
  rfl

private lemma res_pullU_res_eq_res_pullU {S T : Scheme.{0}} (h : T ⟶ S) {U V : S.Opens} {W : T.Opens} (hVU : V ≤ U)
    (hW : W ≤ h ⁻¹ᵁ V) (hW' : W ≤ h ⁻¹ᵁ U) (t : Γ(S, U)ˣ) :
    res hW (pullU h V (res hVU t)) = res hW' (pullU h U t) := by
  have hn := h.naturality (homOfLE hVU).op
  have key : S.presheaf.map (homOfLE hVU).op ≫ h.app V ≫ T.presheaf.map (homOfLE hW).op =
      h.app U ≫ T.presheaf.map (homOfLE hW').op := by
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
    rfl
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  exact congrArg (fun φ => φ.hom t.val) key

lemma pullU_units_compat_generic (h : Z ⟶ Y) {Ui Uj : Y.Opens} {Wi Wj : Z.Opens} (hi : Wi ≤ h ⁻¹ᵁ Ui)
    (hj : Wj ≤ h ⁻¹ᵁ Uj) (ti : Γ(Y, Ui)ˣ) (tj : Γ(Y, Uj)ˣ) (g : Γ(Y, Ui ⊓ Uj)ˣ)
    (hc : res (inf_le_left : Ui ⊓ Uj ≤ Ui) ti = g * res (inf_le_right : Ui ⊓ Uj ≤ Uj) tj)
    (g' : Γ(Z, Wi ⊓ Wj)ˣ)
    (hg' : g' = res (le_inf (inf_le_left.trans hi) (inf_le_right.trans hj) : Wi ⊓ Wj ≤ h ⁻¹ᵁ (Ui ⊓ Uj))
      (pullU h _ g)) :
    res (inf_le_left : Wi ⊓ Wj ≤ Wi) (res hi (pullU h Ui ti)) =
      g' * res (inf_le_right : Wi ⊓ Wj ≤ Wj) (res hj (pullU h Uj tj)) := by
  subst hg'
  have hW : Wi ⊓ Wj ≤ h ⁻¹ᵁ (Ui ⊓ Uj) := le_inf (inf_le_left.trans hi) (inf_le_right.trans hj)
  have h1 : res (X := Z) (U := h ⁻¹ᵁ (Ui ⊓ Uj)) (V := Wi ⊓ Wj) hW
        (pullU h (Ui ⊓ Uj) (res (inf_le_left : Ui ⊓ Uj ≤ Ui) ti)) =
      res (X := Z) (U := h ⁻¹ᵁ (Ui ⊓ Uj)) (V := Wi ⊓ Wj) hW (pullU h (Ui ⊓ Uj) g) *
        res (X := Z) (U := h ⁻¹ᵁ (Ui ⊓ Uj)) (V := Wi ⊓ Wj) hW
          (pullU h (Ui ⊓ Uj) (res (inf_le_right : Ui ⊓ Uj ≤ Uj) tj)) := by
    rw [hc, map_mul, map_mul]
  rw [res_pullU_res_eq_res_pullU h inf_le_left hW (inf_le_left.trans hi),
    res_pullU_res_eq_res_pullU h inf_le_right hW (inf_le_right.trans hj)] at h1
  rw [res_res_lemma, res_res_lemma]
  exact h1

lemma pullGen_isGen_of_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (h : Z ⟶ Y) : (LB.pullGen L φ ε t h).IsGen := by
  intro i j
  exact pullU_units_compat_generic h (wchart_comp_le φ h i) (wchart_comp_le φ h j) (t.s i) (t.s j) _ (ht i j) _
    (linComb_g_comp φ ε h i j)

def scaleGen {M : LB Y} (c : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M where
  s j := res le_top c * t.s j

lemma scaleGen_isGen {M : LB Y} (c : Γ(Y, ⊤)ˣ) (t : LB.Gen M) (ht : t.IsGen) : (scaleGen c t).IsGen := by
  intro i j
  simp only [scaleGen, map_mul]
  rw [ht i j, res_res_lemma, res_res_lemma, mul_left_comm]

lemma wchart_empty (j : PEmpty → L.ι) : LB.wchart L (Y := Y) (K := PEmpty) PEmpty.elim j = ⊤ := by
  ext x
  simp [LB.wchart]

lemma pullU_of_eq_id (f : Z ⟶ Z) (hf : f = 𝟙 Z) (U V : Z.Opens) (hV : V ≤ f ⁻¹ᵁ U) (hV' : V ≤ U)
    (c : Γ(Z, U)ˣ) : res hV (pullU f U c) = res hV' c := by
  subst hf
  ext
  simp [res, pullU, CommRingCat.hom_id, Units.coe_map] <;> rfl

open scoped Classical in

theorem exists_value (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (z : Z ⟶ Y) (h0 : fsum (fun k => z ≫ φ k) ε = 0) :
    ∃ c : Γ(Z, ⊤)ˣ, ∀ j : K → L.ι, LB.Coh L (fun k => z ≫ φ k) j →
      res (le_top : LB.wchart L (fun k => z ≫ φ k) j ≤ ⊤) c = (LB.pullGen L φ ε t z).s j := by
  have hs : LB.SameSum (fun k => z ≫ φ k) ε (K' := PEmpty) PEmpty.elim PEmpty.elim := by
    rw [sameSum_iff_fsum, h0, fsum_empty]
  obtain ⟨te, -, hc⟩ := gen_transport hL hs (LB.pullGen L φ ε t z) (pullGen_isGen_of_isGen φ ε t ht z)
  let j0 : PEmpty → L.ι := PEmpty.elim
  refine ⟨res (le_of_eq (wchart_empty j0).symm) (te.s j0), fun j hj => ?_⟩
  have e := hc j j0 hj (fun k _ => k.elim) (fun _ k => k.elim)
  have hle : LB.wchart L (fun k => z ≫ φ k) j ≤ LB.wchart L (fun k => z ≫ φ k) j ⊓ LB.wchart L PEmpty.elim j0 :=
    le_inf le_rfl (by rw [wchart_empty]; exact le_top)
  have e2 := congrArg (res hle) e
  erw [res_res'] at e2
  have e3 := e2.symm
  erw [res_res', res_refl'] at e3
  erw [res_res']
  exact e3

private lemma pullU_comp_lemma_3 {S T R : Scheme.{0}} (g : R ⟶ T) (f : T ⟶ S) (U : S.Opens) (x : Γ(S, U)ˣ) :
    pullU (g ≫ f) U x = pullU g (f ⁻¹ᵁ U) (pullU f U x) := by
  first
  | rfl
  | (ext; simp [pullU, Scheme.comp_app])

lemma pull_pull_id (z : Z ⟶ Y) (p : Y ⟶ Z) (hzp : z ≫ p = 𝟙 Z) {W : Y.Opens} {V : Z.Opens}
    (hW : W ≤ p ⁻¹ᵁ ⊤) (hV : V ≤ z ⁻¹ᵁ W) (c : Γ(Z, ⊤)ˣ) :
    res hV (pullU z W (res hW (pullU p ⊤ c))) = res (le_top : V ≤ ⊤) c := by
  have hV' : V ≤ z ⁻¹ᵁ (p ⁻¹ᵁ ⊤) := fun x hx => hW (hV hx)
  rw [res_pullU_res_eq_res_pullU z hW hV hV', ← pullU_comp_lemma_3]
  exact pullU_of_eq_id (z ≫ p) hzp ⊤ V hV' le_top c

theorem exists_normalized (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z) (h0 : fsum (fun k => z ≫ φ k) ε = 0) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      ∀ j : K → L.ι, LB.Coh L (fun k => z ≫ φ k) j → (LB.pullGen L φ ε t' z).s j = 1 := by
  obtain ⟨c, hc⟩ := exists_value hL φ ε t ht z h0
  let c' : Γ(Y, ⊤)ˣ := res (fun _ _ => trivial : (⊤ : Y.Opens) ≤ p ⁻¹ᵁ ⊤) (pullU p ⊤ c⁻¹)
  refine ⟨scaleGen c' t, scaleGen_isGen c' t ht, fun j hj => ?_⟩
  have e := hc j hj
  show res _ (pullU z _ (res le_top c' * t.s j)) = 1
  rw [map_mul, map_mul]
  have e1 : res (wchart_comp_le φ z j) (pullU z _ (res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) c')) =
      res (le_top : LB.wchart L (fun k => z ≫ φ k) j ≤ ⊤) c⁻¹ := by
    simp only [c']
    erw [res_res']
    exact pull_pull_id z p hzp _ _ c⁻¹
  erw [e1]
  have e2 : res (wchart_comp_le φ z j) (pullU z _ (t.s j)) = (LB.pullGen L φ ε t z).s j := rfl
  erw [e2, ← e, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem gen_of_top (hL : L.IsLB) {S : Scheme.{0}} {W : Over S} (ψ : K → (W.left ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L (fun k => (W.hom ⁻¹ᵁ ⊤).ι ≫ ψ k) ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L ψ ε), t'.IsGen := by
  have e : ∀ k, W.left.topIso.inv ≫ (W.hom ⁻¹ᵁ ⊤).ι ≫ ψ k = ψ k := fun k =>
    W.left.toIso_inv_ι_assoc (ψ k)
  have hs : LB.SameSum (fun k => W.left.topIso.inv ≫ (W.hom ⁻¹ᵁ ⊤).ι ≫ ψ k) ε ψ ε := by
    rw [sameSum_iff_fsum]
    exact congrArg (fun f => fsum f ε) (funext e)
  obtain ⟨t', ht', -⟩ := gen_transport hL hs _ (pullGen_isGen_of_isGen _ ε t ht W.left.topIso.inv)
  exact ⟨t', ht'⟩

theorem gen_of_local_base {V : Type} [CommRing V] [IsLocalRing V] (hL : L.IsLB)
    {W : Over (Spec (CommRingCat.of V))} (ψ : K → (W.left ⟶ X)) (ε : K → ℤ)
    (h : ∀ s : Spec (CommRingCat.of V), ∃ U : (Spec (CommRingCat.of V)).Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb L (fun k => (W.hom ⁻¹ᵁ U).ι ≫ ψ k) ε), t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L ψ ε), t'.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := h (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff (R := V) U).1 hU
  exact gen_of_top hL ψ ε t ht

end ReciprocityTheory.ChartRestriction.G.DVR
