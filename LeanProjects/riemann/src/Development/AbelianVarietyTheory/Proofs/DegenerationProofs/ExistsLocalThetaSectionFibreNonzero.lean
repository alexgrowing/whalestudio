import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LocThetaConv

variable {X Y : Scheme.{0}}

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem appLE_resG (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) {U : Y.Opens} (e : U ≤ f ⁻¹ᵁ W')
    (a : Γ(X, W)) : (f.appLE W' U e).hom (resG X h a) =
      (f.appLE W U (e.trans fun _ hy => h hy)).hom a := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem resG_appLE (f : Y ⟶ X) {W : X.Opens} {U U' : Y.Opens} (h : U' ≤ U) (e : U ≤ f ⁻¹ᵁ W)
    (a : Γ(X, W)) : resG Y h ((f.appLE W U e).hom a) = (f.appLE W U' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem g_val (L : LB X) {K : Type} [Fintype K] [Subsingleton K] (φ : K → (Y ⟶ X)) (k : K)
    (i j : K → L.ι) : ((LB.LinComb L φ (fun _ => 1)).g i j).val =
      ((φ k).appLE (L.U (i k) ⊓ L.U (j k)) (LB.wchart L φ i ⊓ LB.wchart L φ j)
        (le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))).hom
        (L.g (i k) (j k)).val := by
  simp only [LB.LinComb, zpow_one]
  erw [Fintype.prod_subsingleton _ k]
  rfl

theorem mem_one {L : LB X} {j : Fin 1 → L.ι} {x : X} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_pull' {L : LB X} (f : Y ⟶ X) {j : L.ι} {y : Y} :
    y ∈ (L.pull f).U (fun _ => j) ↔ f y ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_secOn (L : LB X) (V : X.Opens) (σ : LB.Sec (L.pull V.ι)) :
    ∃ τ ∈ secOn (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) V,
      ∀ y ∈ nonzeroLocus σ, ∃ j, V.ι y ∈ X.basicOpen (τ j) := by
  set L₁ := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1) with hL₁
  have e : ∀ j : Fin 1 → L.ι, (L.pull V.ι).U (fun _ => j 0) ≤ V.ι ⁻¹ᵁ (V ⊓ L₁.U j) :=
    fun j y hy => ⟨y.2, mem_one.2 ((mem_pull' _).1 hy)⟩
  have e' : ∀ j : Fin 1 → L.ι, V.ι ⁻¹ᵁ (V ⊓ L₁.U j) ≤ (L.pull V.ι).U (fun _ => j 0) :=
    fun j y hy => (mem_pull' _).2 (mem_one.1 hy.2)
  have hV : V ≤ V.ι.opensRange := V.opensRange_ι.ge
  choose τ hτ using fun j : Fin 1 → L.ι =>
    (bijective_appLE V.ι _ (inf_le_left.trans hV) _ (e j) (e' j)).2 (σ.f fun _ => j 0)
  refine ⟨τ, fun i j => ?_, fun y hy => ?_⟩
  · apply (bijective_appLE V.ι (V ⊓ L₁.U i ⊓ L₁.U j) ((inf_le_left.trans inf_le_left).trans hV)
      ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
      (fun y hy => ⟨e i hy.1, (e j hy.2).2⟩) (fun y hy => ⟨e' i hy.1, e' j ⟨hy.1.1, hy.2⟩⟩)).1
    have h := σ.compat (fun _ => i 0) (fun _ => j 0)
    rw [← hτ i, ← hτ j] at h
    rw [map_mul]
    refine ((appLE_resG _ _ _ _).trans (resG_appLE _ _ _ _).symm).trans (h.trans ?_)
    congr 1
    · have h1 : ((L.pull V.ι).g (fun _ => i 0) (fun _ => j 0)).val =
          (V.ι.appLE (L.U (i 0) ⊓ L.U (j 0)) ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
            (fun y hy => ⟨(mem_pull' _).1 hy.1, (mem_pull' _).1 hy.2⟩)).hom
            (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : PUnit => V.ι) PUnit.unit _ _).trans (by rfl)
      have h2 : (L₁.g i j).val = resG X (fun y hy => ⟨mem_one.1 hy.1, mem_one.1 hy.2⟩ :
          L₁.U i ⊓ L₁.U j ≤ L.U (i 0) ⊓ L.U (j 0)) (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : Fin 1 => 𝟙 X) 0 _ _).trans (by rfl)
      rw [h1, h2]
      exact ((appLE_resG _ _ _ _).trans (appLE_resG _ _ _ _)).symm
    · exact (resG_appLE _ _ _ _).trans (appLE_resG _ _ _ _).symm
  · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    have h := Scheme.basicOpen_appLE V.ι _ _ (e fun _ => k PUnit.unit) (τ fun _ => k PUnit.unit)
    have h' := hτ fun _ => k PUnit.unit
    have hk' : y ∈ V.toScheme.basicOpen (σ.f fun _ => k PUnit.unit) := hk
    rw [← h'] at hk'
    exact (h.le hk').2

theorem exists_point {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
    (x : Sp K ⟶ Y) (O : X.Opens) (p : X) (hp : p ∈ O) (hx : π p = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ⊤ ≤ g ⁻¹ᵁ O := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _))
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

theorem exists_secFam_fibNe : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q H z
  obtain ⟨N, σ, hz, hσ⟩ := H z
  obtain ⟨τ, hτ, hne⟩ := exists_secOn Q.L.L _ σ
  refine ⟨N, τ, hz, hτ, fun K _ _ x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hσ _ (hx ⟨IsLocalRing.closedPoint K, rfl⟩)
  obtain ⟨j, hj⟩ := hne y hy
  have := Q.dim
  have : Smooth Q.G.hom := SmoothOfRelativeDimension.smooth S.g _
  obtain ⟨g, hg, hO⟩ := exists_point Q.G.hom x _ _ hj hyx
  exact ⟨g, j, hg, ((GlobalTheory.Points.le_preimage_basicOpen_iff g
    (GlobalTheory.Points.le_preimage_mono g (Scheme.basicOpen_le _ _) hO) (τ j)).1 hO).ne_zero⟩

end GlobalTheory.ZH.LocThetaConv
end
