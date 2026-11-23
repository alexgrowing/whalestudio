import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotIsGaloisCoverTrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfFiniteGeneratingAutomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem spMap_mul_aut {K' : Type} [Field K'] (a b : K' ≃+* K') :
    spMap ((a * b : K' ≃+* K') : K' →+* K') = spMap (a : K' →+* K') ≫ spMap (b : K' →+* K') := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem lbIso_pull_comp_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a b : X ⟶ X)
    (ha : LBIso L (L.pull a)) (hb : LBIso L (L.pull b)) : LBIso L (L.pull (a ≫ b)) :=
  LBIso.trans hL (pull_isLB hL a) (pull_isLB hL _) ha
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L a a rfl) (chartPullSame L _ (fun _ => b) _ a fun _ => rfl) hb)

theorem exists_lb_descent_of_finite_aut : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ L' : LB A'.left, L'.IsLB → (∀ g, ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧ ψ ≫ A'.hom = A'.hom ≫ spMap (s g).toRingHom ∧ LBIso L' (L'.pull ψ)) → ∃ L : LB A.left, L.IsLB ∧ LBIso L' (L.pull φ) := by
  intro K K' _ _ i hfin Γ _ s hs hfix A _ A' _ φ hA hp L' hL' hinv
  letI : Algebra K K' := i.toAlgebra
  obtain ⟨hgal, hgen⟩ := GlobalTheory.T.isGalois_of_finite_fixed_automorphisms K K' i hfin Γ s hs hfix
  haveI : FiniteDimensional K K' := hfin
  have hc0 := GlobalTheory.ZM.DwModel.isGaloisCover_field K K'
  have hfixσ : ∀ σ : K' ≃ₐ[K] K', ∀ x, (σ : K' ≃+* K') (i x) = i x := fun σ x => σ.commutes x
  have hσi : ∀ σ : K' ≃ₐ[K] K', spMap (σ : K' →+* K') ≫ spMap i = spMap i := fun σ => by
    simp only [spMap, ← Spec.map_comp]
    congr 1
    ext x
    exact σ.commutes x
  have hw : ∀ σ : K' ≃ₐ[K] K', (A'.hom ≫ spMap (σ : K' →+* K')) ≫ spMap i = φ ≫ A.hom := fun σ => by
    rw [Category.assoc, hσi σ, hp.1.w]
  let t : (K' ≃ₐ[K] K') → (A'.left ⟶ A'.left) := fun σ =>
    hp.1.lift φ (A'.hom ≫ spMap (σ : K' →+* K')) (hw σ).symm
  have ht1 : ∀ σ, t σ ≫ φ = φ := fun σ => hp.1.lift_fst _ _ _
  have ht2 : ∀ σ, t σ ≫ A'.hom = A'.hom ≫ spMap (σ : K' →+* K') := fun σ => hp.1.lift_snd _ _ _
  have hGC : GlobalTheory.ZM.IsGaloisCover (K' ≃ₐ[K] K') t φ :=
    hc0.of_isPullback (u := A'.hom) (v := A.hom) hp.1.flip (fun a => ht2 a) ht1

  have hQ : ∀ τ ∈ Submonoid.closure (Set.range s), ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧
      ψ ≫ A'.hom = A'.hom ≫ spMap (τ : K' →+* K') ∧ LBIso L' (L'.pull ψ) := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hinv g
    | one =>
      refine ⟨𝟙 _, Category.id_comp _, ?_, ?_⟩
      · rw [Category.id_comp]
        have : ((1 : K' ≃+* K') : K' →+* K') = RingHom.id K' := rfl
        rw [this]
        exact (Category.comp_id _).symm.trans (by simp [spMap])
      · exact LBIso.symm (lbIso_of_chartPull (chartPullPull L' (𝟙 _)) hL')
    | mul x y _ _ hx hy =>
      obtain ⟨ψ₁, a1, b1, c1⟩ := hx
      obtain ⟨ψ₂, a2, b2, c2⟩ := hy
      refine ⟨ψ₁ ≫ ψ₂, by rw [Category.assoc, a2, a1], ?_, lbIso_pull_comp_self hL' _ _ c1 c2⟩
      rw [Category.assoc, b2, ← Category.assoc, b1, Category.assoc, spMap_mul_aut]
  have hall : ∀ σ : K' ≃ₐ[K] K', LBIso L' (L'.pull (t σ)) := fun σ => by
    obtain ⟨ψ, a1, b1, c1⟩ := hQ (σ : K' ≃+* K') (hgen _ (hfixσ σ))
    have : ψ = t σ := hp.1.hom_ext (by rw [a1, ht1]) (by rw [b1, ht2]; rfl)
    exact this ▸ c1
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hp
  have hsurj : Function.Surjective A'.hom.appTop.hom := (GlobalTheory.globalFns_holds (Sp K') A' hA').2
  let e : Sp K' ⟶ A'.left := hp.1.lift (spMap i ≫ eSec A) (𝟙 _) (by
    rw [Category.id_comp, Category.assoc, show eSec A ≫ A.hom = 𝟙 _ from Over.w η[A]]; exact Category.comp_id _)
  have he : e ≫ A'.hom = 𝟙 _ := hp.1.lift_snd _ _ _
  have heθ : ∀ σ : K' ≃ₐ[K] K', e ≫ t σ = spMap (σ : K' →+* K') ≫ e := fun σ => by
    refine hp.1.hom_ext ?_ ?_
    · rw [Category.assoc, ht1, Category.assoc, hp.1.lift_fst, ← Category.assoc, hσi σ]
    · rw [Category.assoc, ht2, ← Category.assoc, he, Category.assoc, he]
      simp
  obtain ⟨u, hu, hcoc⟩ := GlobalTheory.T.exists_linearisation_invariant_rigidified_bundle (Sp K') A'.left A'.hom e he hsurj L' hL'
    (GlobalTheory.SS.HtForm.gen_field _ (pull_isLB hL' e)) (K' ≃ₐ[K] K') t (fun σ => spMap (σ : K' →+* K'))
    (fun a c => hGC.mul a c) (fun a c => hc0.mul a c) heθ hall
  exact GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ φ _ t L' hGC hL' u hu hcoc

end GlobalTheory.Mum.GenDesc
