import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibreStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BaseVar

open GlobalTheory.Toroidal (gen genι genStr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem j_mem_range_π {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (x : Xo.XF c) :
    Y.j x ∈ Set.range X.π := by
  let xF : Sp ((Xo.XF c).residueField x) ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField x
  letI : Algebra c.F ((Xo.XF c).residueField x) := (Spec.preimage (xF ≫ pullback.snd _ _)).hom.toAlgebra
  have hsnd : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F ((Xo.XF c).residueField x)) :=
    (Spec.map_preimage _).symm
  obtain ⟨P, hP⟩ := GlobalTheory.FlagTan.exists_frPt (S := (Xo.XF c).residueField x) (Xo := Xo) (c := c)
    (xF ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd, sOf, ← Spec.map_comp]; rfl)
  have hx : xF = GlobalTheory.FlagMod.frX P := GlobalTheory.FlagMod.eq_frX P hP.symm hsnd
  let pt : Sp ((Xo.XF c).residueField x) := IsLocalRing.closedPoint _
  refine ⟨X.ptY P pt, ?_⟩
  have e1 : X.π (X.ptY P pt) = (X.ptY P ≫ X.π) pt := (Scheme.Hom.comp_apply _ _ _).symm
  rw [e1, (X.lies_ptY P).1, ← hx, Scheme.Hom.comp_apply]
  exact congrArg Y.j (Scheme.fromSpecResidueField_apply x _)

theorem surjective_π {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) : Function.Surjective X.π := by
  have := X.proper
  have hc : IsClosed (Set.range X.π) := X.π.isClosedMap.isClosed_range
  have hd : closure (Set.range Y.j) ⊆ Set.range X.π :=
    closure_minimal (by rintro _ ⟨x, rfl⟩; exact j_mem_range_π X x) hc
  exact fun y => hd (LogKS.dense_interior Y y)

theorem surjective_π₀ {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) :
    Function.Surjective (π₀ X Z) := by
  intro y
  obtain ⟨z, hz⟩ := surjective_π X ((barComp Y Z).ι y)
  have hzU : z ∈ X.π ⁻¹ᵁ barComp Y Z := by
    show X.π z ∈ barComp Y Z
    have : (barComp Y Z).ι y ∈ Set.range (barComp Y Z).ι := ⟨y, rfl⟩
    rwa [Scheme.Opens.range_ι, ← hz] at this
  obtain ⟨z', hz'⟩ : z ∈ Set.range (inc₀ X Z) := by rwa [Scheme.Opens.range_ι]
  refine ⟨z', (barComp Y Z).ι.isOpenEmbedding.injective ?_⟩
  have e1 := Scheme.Hom.comp_apply (π₀ X Z) (barComp Y Z).ι z'
  have e2 := Scheme.Hom.comp_apply (inc₀ X Z) X.π z'
  rw [morphismRestrict_ι] at e1
  rw [← e1, e2, hz', hz]

theorem exists_var (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed Xo c) :
    ∃ (B : GlobalTheory.ProjVar.Var c.F) (φ : B.X ⟶ X₀ TF.Y Z), IsIso φ ∧ φ ≫ s₀ TF.Y Z = B.str ∧ B.dim = Dw.dim := by
  have hsm := GlobalTheory.VarFlag.smooth_gen TF.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) TF.Y c.F (RingEquiv.refl _) hF hsm
  have hJ : ∀ w : gen TF.Y, genι TF.Y w ∈ barComp TF.Y Z ↔ w ∈ Set.range (j Z) :=
    GlobalTheory.VarFlag.barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have := (hB Z).1
  have hr : Set.range (j Z ≫ genι TF.Y) ⊆ Set.range (barComp TF.Y Z).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨b, rfl⟩
    exact (hJ _).2 ⟨b, rfl⟩
  let φ := IsOpenImmersion.lift (barComp TF.Y Z).ι (j Z ≫ genι TF.Y) hr
  have hφ : φ ≫ (barComp TF.Y Z).ι = j Z ≫ genι TF.Y := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (φ ≫ (barComp TF.Y Z).ι) := by rw [hφ]; infer_instance
  have : IsOpenImmersion φ := IsOpenImmersion.of_comp φ (barComp TF.Y Z).ι
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨w, hw⟩ : ∃ w, genι TF.Y w = (barComp TF.Y Z).ι y :=
      ⟨inv (genι TF.Y) ((barComp TF.Y Z).ι y), by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have hm : genι TF.Y w ∈ barComp TF.Y Z := by
      have : (barComp TF.Y Z).ι y ∈ Set.range (barComp TF.Y Z).ι := ⟨y, rfl⟩
      rwa [Scheme.Opens.range_ι, ← hw] at this
    obtain ⟨b, rfl⟩ := (hJ w).1 hm
    refine ⟨b, (barComp TF.Y Z).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply, hw]
  have hiso : IsIso φ := (isIso_iff_isOpenImmersion_and_surjective φ).2 ⟨inferInstance, ⟨hsurj⟩⟩
  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  refine ⟨B Z, φ, hiso, ?_, (hB Z).2.1⟩
  have h3 := (hB Z).2.2.1
  rw [hspid, Category.comp_id] at h3
  rw [← h3, GlobalTheory.VarFlag.genStr_eq, s₀, ← Category.assoc, hφ, Category.assoc]

theorem isVariety_barComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ _ : IsIntegral (X₀ TF.Y Z), SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z) ∧ IsProjOver (s₀ TF.Y Z) ∧ GeometricallyConnected (s₀ TF.Y Z) ∧ Surjective (π₀ TF.X Z) ∧ GlobalTheory.IsNormalScheme (V₀ TF.Y Z) ∧ ∀ v : V₀ TF.Y Z, i₀ TF.Y Z v = genPt Z → j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  intro E _ _ _ H Dw l Xo c TF Z hF
  obtain ⟨B, φ, hφ, hs, hd⟩ := exists_var TF Z hF
  have hs' : s₀ TF.Y Z = inv φ ≫ B.str := by rw [← hs, IsIso.inv_hom_id_assoc]
  have : Nonempty (X₀ TF.Y Z) := ⟨φ (genericPoint B.X)⟩
  have hint : IsIntegral (X₀ TF.Y Z) := isIntegral_of_isOpenImmersion (inv φ)
  refine ⟨hint, ?_, ?_, ?_, ⟨surjective_π₀ TF.X Z⟩, ?_, ?_⟩
  · rw [hs', ← hd]
    exact GlobalTheory.VarFlag.smooth_iso _ _ B.smooth
  · obtain ⟨N, i, hi, hs2⟩ := B.isProjOver
    exact ⟨N, inv φ ≫ i, inferInstance, by rw [Category.assoc, hs2, hs']⟩
  · rw [hs']
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (inv φ) (inv φ ≫ B.str) B.str (𝟙 _)) inferInstance
  · haveI : GlobalTheory.IsNormalScheme TF.Y.X := GlobalTheory.IsNormalScheme.of_pred TF.Y.normal
    exact GlobalTheory.IsNormalScheme.of_isOpenImmersion (i₀ TF.Y Z ≫ TF.Y.j)
  · intro v hv
    have : IsOpenImmersion (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) := by rw [j₀_ι]; infer_instance
    have : IsOpenImmersion (j₀ TF.Y Z) := IsOpenImmersion.of_comp _ (barComp TF.Y Z).ι
    have hgen : IsGenericPoint (genPt Z) (Z : Set (Xo.XF c)) := by
      have hirr : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
      exact IsIrreducible.isGenericPoint_genericPoint hirr (isClosed_of_mem_irreducibleComponents _ Z.2)
    have hsub : Set.range (j₀ TF.Y Z) ⊆ closure {j₀ TF.Y Z v} := by
      rintro _ ⟨w, rfl⟩
      have hw : i₀ TF.Y Z w ∈ (Z : Set (Xo.XF c)) := (j_mem_barComp (Y := TF.Y) Z _).1 w.2
      have h1 : i₀ TF.Y Z v ⤳ i₀ TF.Y Z w := hv ▸ hgen.specializes hw
      have h2 : v ⤳ w := (i₀ TF.Y Z).isOpenEmbedding.isInducing.specializes_iff.1 h1
      exact specializes_iff_mem_closure.1 (h2.map (j₀ TF.Y Z).continuous)
    have hdense : Dense (Set.range (j₀ TF.Y Z)) :=
      (j₀ TF.Y Z).isOpenEmbedding.isOpen_range.dense ⟨_, ⟨v, rfl⟩⟩
    have hg : IsGenericPoint (j₀ TF.Y Z v) (Set.univ : Set (X₀ TF.Y Z)) := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← hdense.closure_eq]
      exact closure_minimal hsub isClosed_closure
    exact hg.eq (genericPoint_spec (X₀ TF.Y Z))

end GlobalTheory.BaseVar
