import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart

theorem isAffineOpen_fst_inf_snd {S X Y : Scheme.{0}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S) {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine V.toScheme := hV
  let m := pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S) (by simp) (by simp)
  haveI : IsOpenImmersion m :=
    MorphismProperty.pullback_map (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl
  have e : m.opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    ext1
    refine (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).trans ?_
    simp
  rw [← e]
  exact isAffineOpen_opensRange m

theorem spec_rat_ext {C : Type} [CommRing C] (u v : Sp C ⟶ Sp ℚ) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v]
  congr 1
  ext1
  exact Subsingleton.elim _ _

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {X Y : Scheme.{0}} (f : X ⟶ Sp ℚ) (g : Y ⟶ Sp ℚ)
  {U : X.Opens} {V : Y.Opens}

theorem val_mem_of_components (hU : IsAffineOpen U) (hV : IsAffineOpen V) (C : Subalgebra ℚ Ω)
    (p : Sp Ω ⟶ pullback f g) (hA : ⊤ ≤ (p ≫ pullback.fst f g) ⁻¹ᵁ U) (hB : ⊤ ≤ (p ≫ pullback.snd f g) ⁻¹ᵁ V)
    (mA : ∀ s, (valMap (p ≫ pullback.fst f g) U hA).hom s ∈ C)
    (mB : ∀ s, (valMap (p ≫ pullback.snd f g) V hB).hom s ∈ C)
    (h : ⊤ ≤ p ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V))
    (t : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) :
    (valMap p _ h).hom t ∈ C := by
  let ι : CommRingCat.of C ⟶ CommRingCat.of Ω := CommRingCat.ofHom C.val.toRingHom
  let φA : Γ(X, U) ⟶ CommRingCat.of C := CommRingCat.ofHom ((valMap _ U hA).hom.codRestrict C mA)
  let φB : Γ(Y, V) ⟶ CommRingCat.of C := CommRingCat.ofHom ((valMap _ V hB).hom.codRestrict C mB)
  have eA : φA ≫ ι = valMap _ U hA := rfl
  have eB : φB ≫ ι = valMap _ V hB := rfl
  have hfg : (Spec.map φA ≫ hU.fromSpec) ≫ f = (Spec.map φB ≫ hV.fromSpec) ≫ g := spec_rat_ext _ _
  let q : Sp C ⟶ pullback f g := pullback.lift _ _ hfg
  have hq : Spec.map ι ≫ q = p := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, ← Spec.map_comp, eA,
        specMap_valMap_fromSpec hU]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← Spec.map_comp, eB,
        specMap_valMap_fromSpec hV]
  have h₃ : ⊤ ≤ (q ≫ pullback.fst f g) ⁻¹ᵁ U := by
    rw [pullback.lift_fst]
    exact le_preimage_specMap_fromSpec hU φA
  have h₄ : ⊤ ≤ (q ≫ pullback.snd f g) ⁻¹ᵁ V := by
    rw [pullback.lift_snd]
    exact le_preimage_specMap_fromSpec hV φB
  have hqW : ⊤ ≤ q ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) :=
    fun y hy => ⟨h₃ hy, h₄ hy⟩
  have key : ∀ h' : ⊤ ≤ (Spec.map ι ≫ q) ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V),
      valMap (Spec.map ι ≫ q) _ h' = valMap q _ hqW ≫ ι := fun h' => by
    rw [← appLE_valMap (Spec.map ι) q hqW (le_preimage_top _) h', valMap_specMap]
    simp only [valMap, Category.assoc]
  have h' : ⊤ ≤ (Spec.map ι ≫ q) ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
    rw [hq]
    exact h
  have e : (valMap p _ h).hom t = (valMap (Spec.map ι ≫ q) _ h').hom t := by
    rw [← valR_eq, ← valR_eq, hq]
  rw [e, key]
  exact ((valMap q _ hqW).hom t).2

theorem closed_prod_chart {Z : Scheme.{0}} (j : Z ⟶ pullback f g) [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z)
    (pX : Sp Ω ⟶ X) (pY : Sp Ω ⟶ Y) (h₁ : ζ ≫ j ≫ pullback.fst f g = pX) (h₂ : ζ ≫ j ≫ pullback.snd f g = pY)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hA : ⊤ ≤ pX ⁻¹ᵁ U) (hB : ⊤ ≤ pY ⁻¹ᵁ V) (R₁ R₂ : Set Ω)
    (e₁ : Set.range (valMap pX U hA).hom = Algebra.adjoin ℚ R₁)
    (e₂ : Set.range (valMap pY V hB).hom = Algebra.adjoin ℚ R₂) :
    IsAffineOpen ((j ≫ pullback.fst f g) ⁻¹ᵁ U ⊓ (j ≫ pullback.snd f g) ⁻¹ᵁ V) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst f g) ⁻¹ᵁ U ⊓ (j ≫ pullback.snd f g) ⁻¹ᵁ V),
        Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (R₁ ∪ R₂) := by
  subst h₁ h₂
  have hW := isAffineOpen_fst_inf_snd f g hU hV
  have hZ : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst f g) ⁻¹ᵁ U ⊓ (j ≫ pullback.snd f g) ⁻¹ᵁ V) :=
    fun y hy => ⟨hA hy, hB hy⟩
  have hp : ⊤ ≤ (ζ ≫ j) ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := hZ
  have hA' : ⊤ ≤ ((ζ ≫ j) ≫ pullback.fst f g) ⁻¹ᵁ U := by rwa [Category.assoc]
  have hB' : ⊤ ≤ ((ζ ≫ j) ≫ pullback.snd f g) ⁻¹ᵁ V := by rwa [Category.assoc]
  have vA : ∀ s, (valMap ((ζ ≫ j) ≫ pullback.fst f g) U hA').hom s = (valMap (ζ ≫ j ≫ pullback.fst f g) U hA).hom s := by
    intro s
    rw [← valR_eq, ← valR_eq, Category.assoc]
  have vB : ∀ s, (valMap ((ζ ≫ j) ≫ pullback.snd f g) V hB').hom s = (valMap (ζ ≫ j ≫ pullback.snd f g) V hB).hom s := by
    intro s
    rw [← valR_eq, ← valR_eq, Category.assoc]
  refine ⟨hW.preimage j, hZ, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := j.app_surjective _ hW s
    have e : (valMap (ζ ≫ j) _ hp).hom t = (valMap ζ _ hZ).hom ((j.app _).hom t) :=
      (valR_eq _ _ hp t).symm.trans ((valR_comp ζ j _ t).trans (valR_eq ζ (j ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) hZ _))
    rw [← e]
    refine val_mem_of_components f g hU hV _ (ζ ≫ j) hA' hB' (fun s => ?_) (fun s => ?_) hp t
    · rw [vA]
      have m : (valMap (ζ ≫ j ≫ pullback.fst f g) U hA).hom s ∈ (Algebra.adjoin ℚ R₁ : Set Ω) := by
        rw [← e₁]
        exact Set.mem_range_self s
      exact Algebra.adjoin_mono Set.subset_union_left m
    · rw [vB]
      have m : (valMap (ζ ≫ j ≫ pullback.snd f g) V hB).hom s ∈ (Algebra.adjoin ℚ R₂ : Set Ω) := by
        rw [← e₂]
        exact Set.mem_range_self s
      exact Algebra.adjoin_mono Set.subset_union_right m
  · let F : Z ⟶ Sp ℚ := j ≫ pullback.fst f g ≫ f
    let S : Subalgebra ℚ Ω :=
      { (valMap ζ _ hZ).hom.range with
        algebraMap_mem' := fun c => ⟨(GlobalTheory.QCoh.Qcqs.baseRingHom F _).hom c,
          RingHom.congr_fun (Subsingleton.elim
            ((valMap ζ _ hZ).hom.comp (GlobalTheory.QCoh.Qcqs.baseRingHom F _).hom) (algebraMap ℚ Ω)) c⟩ }
    have hS : Algebra.adjoin ℚ (R₁ ∪ R₂) ≤ S := by
      refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
      · intro w hw
        obtain ⟨s, rfl⟩ : w ∈ Set.range (valMap (ζ ≫ j ≫ pullback.fst f g) U hA).hom :=
          e₁.symm ▸ (Algebra.subset_adjoin hw : w ∈ (Algebra.adjoin ℚ R₁ : Set Ω))
        exact ⟨((j ≫ pullback.fst f g).appLE U _ inf_le_left).hom s,
          congrArg (fun φ => φ.hom s) (appLE_valMap ζ (j ≫ pullback.fst f g) inf_le_left hZ hA)⟩
      · intro w hw
        obtain ⟨s, rfl⟩ : w ∈ Set.range (valMap (ζ ≫ j ≫ pullback.snd f g) V hB).hom :=
          e₂.symm ▸ (Algebra.subset_adjoin hw : w ∈ (Algebra.adjoin ℚ R₂ : Set Ω))
        exact ⟨((j ≫ pullback.snd f g).appLE V _ inf_le_right).hom s,
          congrArg (fun φ => φ.hom s) (appLE_valMap ζ (j ≫ pullback.snd f g) inf_le_right hZ hB)⟩
    exact hS

theorem prod_chart (Ω : Type) [Field Ω] [CharZero Ω] (N r : ℕ) (Z : Scheme.{0})
    (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r)) [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z)
    (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0)
    (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx')
    (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0) :
    IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l),
        Set.range (valMap ζ _ h).hom =
          Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) :=
  closed_prod_chart _ _ j ζ _ _ h₁ h₂ (isAffineOpen_chart ℚ N a) (isAffineOpen_chart ℚ r l)
    ((le_point_preimage_iff a).2 ha) ((le_point_preimage_iff l).2 hl) _ _
    (range_valMap_point _) (range_valMap_point _)

end GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart
