import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirational
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.FiniteBirationalIso

theorem isIso_restrict_of_section {U M : Scheme.{0}} [IsReduced U] (u : U ⟶ M) [IsSeparated u] (W : M.Opens)
    (j : W.toScheme ⟶ U) [IsDominant j] (h : j ≫ u = W.ι) :
    IsIso (u ∣_ W) ∧ Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) := by
  have hr : Set.range j ⊆ Set.range (u ⁻¹ᵁ W).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    show u (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h]
    exact w.2
  refine ⟨?_, j.denseRange.mono (hr.trans (Scheme.Opens.range_ι _).le)⟩
  let σ := IsOpenImmersion.lift (u ⁻¹ᵁ W).ι j hr
  have hσ : σ ≫ (u ⁻¹ᵁ W).ι = j := IsOpenImmersion.lift_fac _ _ _
  have h₁ : σ ≫ u ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hσ, h, Category.id_comp]
  have : IsDominant σ := by
    constructor
    have hd := Dense.preimage j.denseRange (u ⁻¹ᵁ W).ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, (u ⁻¹ᵁ W).ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hσ]; rfl
  refine ⟨σ, ?_, h₁⟩
  refine ext_of_isDominant_of_isSeparated (u ∣_ W) ?_ σ ?_
  · rw [Category.assoc, h₁, Category.comp_id, Category.id_comp]
  · rw [reassoc_of% h₁, Category.comp_id]

theorem main : ∀ (V S T : Scheme.{0}) (e : S ⟶ T) (jS : V ⟶ S) (jT : V ⟶ T), IsFinite e → IsReduced S →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsLocallyNoetherian T → IsOpenImmersion jS → IsOpenImmersion jT →
    jS ≫ e = jT → Dense (Set.range jS) → Dense (Set.range jT) → e ⁻¹' Set.range jT = Set.range jS → IsIso e := by
  intro V S T e jS jT _ _ hT _ _ _ hc hdS hdT _
  let W : T.Opens := jT.opensRange
  let i : V ≅ W.toScheme := jT.isoOpensRange
  have hi : i.hom ≫ W.ι = jT := jT.isoOpensRange_hom_ι
  let j : W.toScheme ⟶ S := i.inv ≫ jS
  have hj : j ≫ e = W.ι := by
    rw [Category.assoc, hc, ← hi, Iso.inv_hom_id_assoc]
  have : IsDominant j := by
    constructor
    have : Set.range j = Set.range jS := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        (ConcreteCategory.bijective_of_isIso i.inv.base).2.range_eq, Set.image_univ]
    rw [DenseRange, this]
    exact hdS
  obtain ⟨hiso, hd⟩ := isIso_restrict_of_section e W j hj
  have hW : Dense (W : Set T) := by
    show Dense (Set.range jT)
    exact hdT
  have hV : ∀ x : T, ∃ V' : T.Opens, x ∈ V' ∧ IsIso (e ∣_ V') := fun x =>
    GlobalTheory.FiniteBirationalNear.main S T e W ‹_› ‹_› hiso hW hd x (hT x).1 (hT x).2
  choose U hxU hU using hV
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U ?_ hU
  exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩

end GlobalTheory.FiniteBirationalIso
