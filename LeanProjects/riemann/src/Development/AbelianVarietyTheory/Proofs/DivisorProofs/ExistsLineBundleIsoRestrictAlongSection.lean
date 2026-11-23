import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

noncomputable section

namespace GlobalTheory.IsoRes

variable {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb}

theorem comp_pt {A B C : Scheme.{0}} (f : A ⟶ B) (h : B ⟶ C) (x : A) : (f ≫ h) x = h (f x) := by
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]

theorem sec_apply (hgi : gi ≫ g = 𝟙 XT) (x : XT) : g (gi x) = x := by
  rw [← comp_pt, hgi]; rfl

theorem chart_le (hgi : gi ≫ g = 𝟙 XT) (J : PUnit → LG.ι) (k : LT.ι) :
    (LG.pull (gi ≫ c)).U J ⊓ LT.U k ≤ gi ⁻¹ᵁ ((LG.pull c).U J ⊓ (LT.pull g).U (fun _ => k)) := by
  intro x hx
  refine ⟨mem_pull.2 ?_, mem_pull.2 ?_⟩
  · have := mem_pull.1 hx.1
    rwa [comp_pt] at this
  · rw [sec_apply hgi]; exact hx.2

def resIso (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) : LB.Iso LT (LG.pull (gi ≫ c)) where
  s := fun p => res (chart_le hgi p.1 p.2) (pullU gi _ (w₀.s (p.1, fun _ => p.2)))

theorem gw_resIso (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) {Z : Scheme.{0}} (r : Z ⟶ XT) (z : Z)
    (j : LG.ι) (k : LT.ι) : gw (resIso hgi w₀) r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  by_cases h : r z ∈ (LG.pull (gi ≫ c)).U (fun _ => j) ⊓ LT.U k
  · have h' : gi (r z) ∈ (LG.pull c).U (fun _ => j) ⊓ (LT.pull g).U (fun _ => k) := chart_le hgi _ _ h
    exact (gm_res r z _ h _).trans (gm_pull r gi z _ h' _)
  · have h' : ¬ (r ≫ gi) z ∈ (LG.pull c).U (fun _ => j) ⊓ (LT.pull g).U (fun _ => k) := by
      intro hm
      apply h
      rw [comp_pt] at hm
      refine ⟨mem_pull.2 ?_, ?_⟩
      · rw [comp_pt]; exact mem_pull.1 hm.1
      · have := mem_pull.1 hm.2
        rwa [sec_apply hgi] at this
    show gm r z _ _ = gm (r ≫ gi) z _ _
    rw [gm, gm, dif_neg h, dif_neg h']; rfl

theorem resIso_pgen (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : PGen w₀) :
    PGen (resIso hgi w₀) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_resIso, gw_resIso]
  rw [comp_pt] at hj hj'
  have hj0 : c ((f ≫ gi) y) ∈ LG.U j := by rw [comp_pt]; exact hj
  have hj0' : c ((f ≫ gi) y) ∈ LG.U j' := by rw [comp_pt]; exact hj'
  have hk0 : (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k) := mem_pull.2 (by rw [comp_pt, sec_apply hgi]; exact hk)
  have hk0' : (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k') := mem_pull.2 (by rw [comp_pt, sec_apply hgi]; exact hk')
  have e := hw₀ Y (f ≫ gi) y j j' (fun _ => k) (fun _ => k') hj0 hj0' hk0 hk0'
  have e2 : gm (f ≫ gi) y ((LT.pull g).U (fun _ => k) ⊓ (LT.pull g).U (fun _ => k'))
      ((LT.pull g).g (fun _ => k) (fun _ => k')) = gm f y _ (LT.g k k') := by
    show gm (f ≫ gi) y _ (∏ _k : PUnit, (res _ (pullU g _ (LT.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (f ≫ gi) y _
      (show (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k) ⊓ (LT.pull g).U (fun _ => k') from ⟨hk0, hk0'⟩) _).trans
      ((gm_pull (f ≫ gi) g y (LT.U k ⊓ LT.U k') ⟨mem_pull.1 hk0, mem_pull.1 hk0'⟩ _).trans ?_)
    rw [Category.assoc, hgi, Category.comp_id]
  rw [e, e2, Category.assoc]

theorem exists_iso_restrict : ∀ {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} (hG : LG.IsLB) (hT : LT.IsLB) {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb} (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : w₀.IsGen), ∃ w : LB.Iso LT (LG.pull (gi ≫ c)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ XT) (z : Z) (j : LG.ι) (k : LT.ι), gw w r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  intro XG XT Pb LG LT hG hT c g gi hgi w₀ hw₀
  exact ⟨resIso hgi w₀, (isGen_iff _).2 (resIso_pgen hgi w₀ ((isGen_iff _).1 hw₀)),
    fun Z r z j k => gw_resIso hgi w₀ r z j k⟩

end GlobalTheory.IsoRes
