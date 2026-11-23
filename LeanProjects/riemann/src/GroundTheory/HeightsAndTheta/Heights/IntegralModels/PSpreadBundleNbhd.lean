import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

theorem SpreadsOn.toNbhd (f : X ⟶ SpecZ) (R : Type) [CommRing R] {E : (baseChange f R).Modules}
    {W : X.Opens} (hE : SpreadsOn f R E W) (htop : ⊤ ≤ baseChangeMap f R ⁻¹ᵁ W) :
    ∃ (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) (E' : (W : Scheme.{0}).Modules),
      IsVectorBundle E' ∧ Nonempty ((Scheme.Modules.pullback (toOpen f R W hW)).obj E' ≅ E) := by
  obtain ⟨E', hE', ⟨α⟩⟩ := hE
  have hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact htop (Set.mem_univ y)
  let U := baseChangeMap f R ⁻¹ᵁ W
  let u : baseChange f R ⟶ U := IsOpenImmersion.lift U.ι (𝟙 _) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact htop (Set.mem_univ y))
  have hu : u ≫ U.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  have hcomp : u ≫ (baseChangeMap f R ∣_ W) = toOpen f R W hW := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hu,
      Category.id_comp, toOpen_ι]
  exact ⟨hW, E', hE', ⟨pullbackCompIso hcomp α ≪≫ (Scheme.Modules.pullbackComp u U.ι).app E ≪≫
    (Scheme.Modules.pullbackCongr hu).app E ≪≫ (Scheme.Modules.pullbackId _).app E⟩⟩

theorem spreadNbhd_of_isEmpty (f : X ⟶ SpecZ) (R : Type) [CommRing R] [IsEmpty (baseChange f R)]
    (E : (baseChange f R).Modules) :
    ∃ (W : X.Opens) (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι)
      (E' : (W : Scheme.{0}).Modules), IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (toOpen f R W hW)).obj E' ≅ E) := by
  have hW : Set.range (baseChangeMap f R) ⊆ Set.range (⊥ : X.Opens).ι := by
    rintro _ ⟨y, rfl⟩
    exact isEmptyElim y
  have : IsEmpty ((⊥ : X.Opens) : Scheme.{0}) := ⟨fun x => x.2⟩
  let i : ((⊥ : X.Opens) : Scheme.{0}) ⟶ baseChange f R := isInitialOfIsEmpty.to _
  have hi : toOpen f R ⊥ hW ≫ i = 𝟙 _ := isInitialOfIsEmpty.hom_ext _ _
  exact ⟨⊥, hW, (Scheme.Modules.pullback i).obj E, fun x => isEmptyElim x,
    ⟨(Scheme.Modules.pullbackComp _ i).app E ≪≫ (Scheme.Modules.pullbackCongr hi).app E ≪≫
      (Scheme.Modules.pullbackId _).app E⟩⟩

theorem SpreadBundleNbhd.proof (h₁ : SpreadLocal.Statement) (h₂ : SpreadStep.Statement) :
    SpreadBundleNbhd.Statement := by
  intro X f _ _ p E hE
  classical
  rcases isEmpty_or_nonempty (baseChange f (ZLoc p)) with hX | hne
  · exact spreadNbhd_of_isEmpty f (ZLoc p) E
  obtain ⟨x₀⟩ := hne
  choose Wx hxW hWx using h₁ X f p E hE
  have hcov : Set.univ ⊆ ⋃ x, ((baseChangeMap f (ZLoc p) ⁻¹ᵁ Wx x :
      (baseChange f (ZLoc p)).Opens) : Set (baseChange f (ZLoc p))) :=
    fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩
  have hc : IsCompact (Set.univ : Set (baseChange f (ZLoc p))) := isCompact_univ
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover _ (fun x => (baseChangeMap f (ZLoc p) ⁻¹ᵁ Wx x).isOpen) hcov
  have key : ∀ s : Finset (baseChange f (ZLoc p)), ∃ W : X.Opens,
      (∀ x ∈ s, baseChangeMap f (ZLoc p) ⁻¹ᵁ Wx x ≤ baseChangeMap f (ZLoc p) ⁻¹ᵁ W) ∧
        SpreadsOn f (ZLoc p) E W := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨Wx x₀, fun x hx => absurd hx (Finset.notMem_empty x), hWx x₀⟩
    | insert a s ha ih =>
      obtain ⟨W, hW, hEW⟩ := ih
      obtain ⟨W', hW', hEW'⟩ := h₂ X f p E (Wx a) W (hWx a) hEW
      refine ⟨W', fun x hx => ?_, hEW'⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_sup_left.trans hW'
      · exact (hW x hx).trans (le_sup_right.trans hW')
  obtain ⟨W, hW, hEW⟩ := key t
  obtain ⟨hW', E', hE', hiso⟩ := hEW.toNbhd f (ZLoc p) (fun y _ => by
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact hW x hx hy)
  exact ⟨W, hW', E', hE', hiso⟩

end

end GroundTheory.Heights₂.Heights.Model
