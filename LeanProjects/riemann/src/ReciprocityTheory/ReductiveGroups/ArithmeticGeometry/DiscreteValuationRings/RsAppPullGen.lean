import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpIdentRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {X Y Y' Z : Scheme.{0}} (L : LB X) {K₁ K₂ K₃ K K' : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃]
  [Fintype K] [Fintype K']

theorem secRel_pull (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y)
    (φ₃ : K₃ → (Y' ⟶ X)) (ε₃ : K₃ → ℤ) (u : LB.Gen (LB.LinComb L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u)
    (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι) (j₃ : K₃ → L.ι)
    (hcoh : LB.Coh L (Sum.elim φ₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃)) (Sum.elim j₁ (Sum.elim j₂ j₃)))
    (q : Z ⟶ Y') {O : Z.Opens}
    (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ₁ j₁) (h₂ : O ≤ (q ≫ h) ⁻¹ᵁ LB.wchart L φ₂ j₂)
    (h₃ : O ≤ q ⁻¹ᵁ LB.wchart L φ₃ j₃) :
    rs h₁ ((q.app _).hom (s₁.f j₁)) =
      rs h₂ (((q ≫ h).app _).hom (s₂.f j₂)) * rs h₃ ((q.app _).hom (u.s j₃).val) := by
  have hOb : O ≤ q ⁻¹ᵁ (LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃) := by
    intro z hz
    refine ⟨⟨h₁ hz, Set.mem_iInter.2 fun k => ?_⟩, h₃ hz⟩
    have := Set.mem_iInter.1 (h₂ hz) k
    simpa [Scheme.Hom.comp_apply] using this
  have key : rs (inf_le_left.trans inf_le_left : _ ≤ LB.wchart L φ₁ j₁) (s₁.f j₁) =
      rs ((inf_le_left.trans inf_le_right).trans (wchart_comp_le φ₂ h j₂)) ((h.app _).hom (s₂.f j₂)) *
      rs (inf_le_right : _ ≤ LB.wchart L φ₃ j₃) (u.s j₃).val := hrel j₁ j₂ j₃ hcoh
  have ha : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤ LB.wchart L φ₁ j₁ :=
    inf_le_left.trans inf_le_left
  have hb : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
      h ⁻¹ᵁ LB.wchart L φ₂ j₂ := (inf_le_left.trans inf_le_right).trans (wchart_comp_le φ₂ h j₂)
  have hc : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
      LB.wchart L φ₃ j₃ := inf_le_right
  have e1 : rs hOb ((q.app _).hom (rs ha (s₁.f j₁))) = rs h₁ ((q.app _).hom (s₁.f j₁)) :=
    (congrArg (rs hOb) (app_rs q ha (s₁.f j₁))).trans (rs_rs _ _ _)
  have e2 : rs hOb ((q.app _).hom (rs hb ((h.app _).hom (s₂.f j₂)))) =
      rs h₂ (((q ≫ h).app _).hom (s₂.f j₂)) := by
    rw [app_rs, rs_rs]
    rfl
  have e3 : rs hOb ((q.app _).hom (rs hc (u.s j₃).val)) = rs h₃ ((q.app _).hom (u.s j₃).val) :=
    (congrArg (rs hOb) (app_rs q hc (u.s j₃).val)).trans (rs_rs _ _ _)
  rw [← e1, ← e2, ← e3, ← rs_mul, ← map_mul]
  exact congrArg (fun x => rs hOb ((q.app _).hom x)) key

theorem corr_pull (φ : K → (Y' ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (hc : LB.Gen.Corr L φ ε φ' ε' t t') (j : K → L.ι) (j' : K' → L.ι) (hj : LB.Coh L φ j)
    (hj' : LB.Coh L φ' j') (hjj : ∀ k k', φ k = φ' k' → j k = j' k')
    (q : Z ⟶ Y') {O : Z.Opens} (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ j) (h₂ : O ≤ q ⁻¹ᵁ LB.wchart L φ' j') :
    rs h₁ ((q.app _).hom (t.s j).val) = rs h₂ ((q.app _).hom (t'.s j').val) := by
  have hO : O ≤ q ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun z hz => ⟨h₁ hz, h₂ hz⟩
  have key : rs (inf_le_left : _ ≤ LB.wchart L φ j) (t.s j).val =
      rs (inf_le_right : _ ≤ LB.wchart L φ' j') (t'.s j').val := by
    exact congrArg Units.val (hc j j' hj hj' hjj)
  have e1 : rs hO ((q.app _).hom (rs (inf_le_left : _ ≤ LB.wchart L φ j) (t.s j).val)) =
      rs h₁ ((q.app _).hom (t.s j).val) :=
    (congrArg (rs hO) (app_rs q (inf_le_left : _ ≤ LB.wchart L φ j) (t.s j).val)).trans (rs_rs _ _ _)
  have e2 : rs hO ((q.app _).hom (rs (inf_le_right : _ ≤ LB.wchart L φ' j') (t'.s j').val)) =
      rs h₂ ((q.app _).hom (t'.s j').val) :=
    (congrArg (rs hO) (app_rs q (inf_le_right : _ ≤ LB.wchart L φ' j') (t'.s j').val)).trans (rs_rs _ _ _)
  rw [← e1, ← e2]
  exact congrArg (fun x => rs hO ((q.app _).hom x)) key

lemma rs_app_comp' {Z Y X : Scheme.{0}} (h : Z ⟶ Y) (ψ : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    {V : Z.Opens} (hW : W ≤ ψ ⁻¹ᵁ U) (hV : V ≤ h ⁻¹ᵁ W) (hV' : V ≤ (h ≫ ψ) ⁻¹ᵁ U) (x : Γ(X, U)) :
    rs hV ((h.app W).hom (rs hW ((ψ.app U).hom x))) = rs hV' (((h ≫ ψ).app U).hom x) := by
  rw [app_rs, rs_rs, Scheme.Hom.comp_app]
  rfl

theorem rs_app_mulGen (φ : K → (Y' ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι)
    (q : Z ⟶ Y') {O : Z.Opens} (h : O ≤ q ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j)
    (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ (j ∘ Sum.inl)) (h₂ : O ≤ q ⁻¹ᵁ LB.wchart L φ' (j ∘ Sum.inr)) :
    rs h ((q.app _).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val) =
      rs h₁ ((q.app _).hom (t.s (j ∘ Sum.inl)).val) * rs h₂ ((q.app _).hom (t'.s (j ∘ Sum.inr)).val) := by
  simp only [LB.mulGen, Units.val_mul, map_mul, rs_mul]
  congr 1
  · exact (congrArg (rs h) (app_rs q _ (t.s (j ∘ Sum.inl)).val)).trans (rs_rs _ _ _)
  · exact (congrArg (rs h) (app_rs q _ (t'.s (j ∘ Sum.inr)).val)).trans (rs_rs _ _ _)

theorem rs_app_pullGen {W : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε))
    (g : W ⟶ Y) (j : K → L.ι) (q : Z ⟶ W) {O : Z.Opens}
    (h : O ≤ q ⁻¹ᵁ LB.wchart L (fun k => g ≫ φ k) j) (h' : O ≤ (q ≫ g) ⁻¹ᵁ LB.wchart L φ j) :
    rs h ((q.app _).hom ((LB.pullGen L φ ε c g).s j).val) = rs h' (((q ≫ g).app _).hom (c.s j).val) :=
  (congrArg (rs h) (app_rs q (wchart_comp_le φ g j) ((g.app _).hom (c.s j).val))).trans (rs_rs _ _ _)

end ReciprocityTheory.ChartRestriction.G.DVR
