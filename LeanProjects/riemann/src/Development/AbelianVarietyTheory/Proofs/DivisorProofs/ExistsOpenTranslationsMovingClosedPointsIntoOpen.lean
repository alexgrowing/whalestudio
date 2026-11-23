import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSemiAbelianSquareSameProjectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_open_mul_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (V : G.left.Opens), (∃ v ∈ V, G.hom v = closedPoint R) → ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R ∧ IsClosed ({x} : Set G.left)) → ∃ O : G.left.Opens, (∃ u ∈ O, G.hom u = closedPoint R) ∧ ∀ (Ω : Type) [Field Ω] (t : Sp Ω ⟶ Sp R) (x a : Over.mk t ⟶ G), (∀ z, x.left z ∈ s) → (∀ z, a.left z ∈ O) → ∀ z, (x * a).left z ∈ V := by
  intro R _ _ _ G _ _ hG V hV s hs
  obtain ⟨v, hvV, hvc⟩ := hV
  set F : Set G.left := G.hom ⁻¹' {closedPoint R} with hFdef
  have hFc : IsClosed F := (isClosed_singleton_closedPoint R).preimage G.hom.continuous
  have hcond : ∀ p : (G ⊗ G).left, G.hom ((snd G G).left p) = G.hom ((fst G G).left p) := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun h : (G ⊗ G).left ⟶ Sp R => h p) pullback.condition.symm
  have hsurj : ∀ x : G.left, G.hom x = closedPoint R → (snd G G).left '' ((fst G G).left ⁻¹' {x}) = F := by
    intro x hx
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      show G.hom _ = closedPoint R
      rw [hcond p, show (fst G G).left p = x from hp, hx]
    · intro hw
      obtain ⟨p, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) x w (hx.trans hw.symm)
      exact ⟨p, h1, h2⟩
  have hmu : ∀ p : (G ⊗ G).left, G.hom (μ[G].left p) = G.hom ((fst G G).left p) := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w μ[G]]
    rfl
  let Ψ : G ⊗ G ⟶ G ⊗ G := lift (fst G G) ((fst G G)⁻¹ * snd G G)
  have hΨ1 : Ψ ≫ fst G G = fst G G := lift_fst _ _
  have hΨ2 : Ψ ≫ μ[G] = snd G G := by
    show fst G G * ((fst G G)⁻¹ * snd G G) = snd G G
    exact mul_inv_cancel_left _ _
  have hmsurj : ∀ x : G.left, G.hom x = closedPoint R → μ[G].left '' ((fst G G).left ⁻¹' {x}) = F := by
    intro x hx
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      show G.hom _ = closedPoint R
      rw [hmu p, show (fst G G).left p = x from hp, hx]
    · intro hw
      obtain ⟨q, hq, rfl⟩ := (hsurj x hx).symm ▸ hw
      refine ⟨Ψ.left q, ?_, ?_⟩
      · show (fst G G).left (Ψ.left q) = x
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hΨ1]; exact hq
      · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hΨ2]
  have hFirr : IsIrreducible F := by
    rw [← hsurj v hvc]
    exact (GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian R G hG v).image _ (snd G G).left.continuous.continuousOn
  set gpt := hFirr.genericPoint
  have hgp : IsGenericPoint gpt F := by
    have := hFirr.isGenericPoint_genericPoint_closure
    rwa [hFc.closure_eq] at this

  have gen_of : ∀ (f : (G ⊗ G).left → G.left), Continuous f → ∀ (Z : Set (G ⊗ G).left) (ξ : (G ⊗ G).left),
      IsGenericPoint ξ Z → f '' Z = F → f ξ = gpt := by
    intro f hf Z ξ hξ hZ
    refine IsGenericPoint.eq ?_ hgp
    show closure {f ξ} = F
    apply le_antisymm
    · exact hFc.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hZ ▸ ⟨ξ, hξ.mem, rfl⟩))
    · rw [← hZ, ← hξ.def, ← Set.image_singleton]
      exact image_closure_subset_closure_image hf
  let T : G.left → Set G.left := fun x =>
    (snd G G).left '' ((fst G G).left ⁻¹' {x} ∩ μ[G].left ⁻¹' (V : Set G.left)ᶜ)
  have hTc : ∀ x ∈ s, IsClosed (T x) := by
    intro x hx
    refine GlobalTheory.T.isClosed_image_snd_of_subset_semiAbelian_fibre R G hG x (hs x hx).1 (hs x hx).2 _ ?_ Set.inter_subset_left
    exact ((hs x hx).2.preimage (fst G G).left.continuous).inter
      (V.isOpen.isClosed_compl.preimage μ[G].left.continuous)
  have hgpV : gpt ∈ (V : Set G.left) := (hgp.specializes (show v ∈ F from hvc)).mem_open V.isOpen hvV
  have hgpT : ∀ x ∈ s, gpt ∉ T x := by
    intro x hx ⟨n, ⟨hn1, hn2⟩, hn3⟩
    have hZc : IsClosed ((fst G G).left ⁻¹' {x}) := (hs x hx).2.preimage (fst G G).left.continuous
    have hZi := GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian R G hG x
    have hξ : IsGenericPoint hZi.genericPoint ((fst G G).left ⁻¹' {x}) := by
      have := hZi.isGenericPoint_genericPoint_closure
      rwa [hZc.closure_eq] at this
    have e2 := gen_of _ (snd G G).left.continuous _ _ hξ (hsurj x (hs x hx).1)
    have em := gen_of _ μ[G].left.continuous _ _ hξ (hmsurj x (hs x hx).1)
    have hnξ : hZi.genericPoint = n :=
      GlobalTheory.T.eq_of_specializes_semiAbelian_square_same_projections R G hG x (hs x hx).1 (hs x hx).2 _ _ hξ.mem hn1 (e2.trans hn3.symm) (hξ.specializes hn1)
    exact hn2 (hnξ ▸ em ▸ hgpV)
  refine ⟨⟨(⋃ x ∈ (s : Set G.left), T x)ᶜ,
    isOpen_compl_iff.2 (s.finite_toSet.isClosed_biUnion hTc)⟩, ⟨gpt, ?_, hgp.mem⟩, ?_⟩
  · show gpt ∉ ⋃ x ∈ (s : Set G.left), T x
    simp only [Set.mem_iUnion, not_exists]
    exact fun x hx => hgpT x hx
  · intro Ω _ t x a hx ha z
    by_contra hz
    let q : Over.mk t ⟶ G ⊗ G := lift x a
    have h1 : (fst G G).left (q.left z) = x.left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    have h2 : (snd G G).left (q.left z) = a.left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    have h3 : μ[G].left (q.left z) = (x * a).left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left]; rfl
    have hO := ha z
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hO
    exact hO (x.left z) (hx z) ⟨q.left z, ⟨h1, by simp only [Set.mem_preimage, Set.mem_compl_iff, h3]; exact hz⟩, h2⟩

end GlobalTheory.Mum
