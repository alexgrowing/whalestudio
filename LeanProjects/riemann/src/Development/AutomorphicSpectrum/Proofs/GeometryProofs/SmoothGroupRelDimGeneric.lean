import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

private theorem smoothOfRelativeDimension_restrict_of_le {A S : Scheme.{0}} (f : A ⟶ S) {n : ℕ} {V W : A.Opens} (h : V ≤ W)
    (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) : SmoothOfRelativeDimension n (V.ι ≫ f) := by
  have := smoothOfRelativeDimension_comp 0 n (A.homOfLE h) (W.ι ≫ f)
  rw [zero_add, ← Category.assoc, Scheme.homOfLE_ι] at this
  exact this

private theorem relDim_eq_of_mem_of_mem {A S : Scheme.{0}} (f : A ⟶ S) {n m : ℕ} {V W : A.Opens}
    (hV : SmoothOfRelativeDimension n (V.ι ≫ f)) (hW : SmoothOfRelativeDimension m (W.ι ≫ f))
    {x : A} (hxV : x ∈ V) (hxW : x ∈ W) : n = m :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ (smoothOfRelativeDimension_restrict_of_le f inf_le_left hV) (smoothOfRelativeDimension_restrict_of_le f inf_le_right hW)
    ⟨x, hxV, hxW⟩

theorem reldim_eq_of_two_pullbacks {P A S : Scheme.{0}} {f : A ⟶ S} {b : A ⟶ S} {p : P ⟶ A} {a₁ a₂ : P ⟶ A}
    (h₁ : IsPullback a₁ p f b) (h₂ : IsPullback a₂ p f b) {n₁ n₂ : ℕ} {W₁ W₂ : A.Opens}
    (d₁ : SmoothOfRelativeDimension n₁ (W₁.ι ≫ f)) (d₂ : SmoothOfRelativeDimension n₂ (W₂.ι ≫ f))
    (z : P) (hz₁ : a₁ z ∈ W₁) (hz₂ : a₂ z ∈ W₂) : n₁ = n₂ := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₁
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₂
  have e₁ : SmoothOfRelativeDimension n₁ ((a₁ ⁻¹ᵁ W₁).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₁)
      ((isPullback_morphismRestrict a₁ W₁).paste_vert h₁) d₁
  have e₂ : SmoothOfRelativeDimension n₂ ((a₂ ⁻¹ᵁ W₂).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₂)
      ((isPullback_morphismRestrict a₂ W₂).paste_vert h₂) d₂
  exact relDim_eq_of_mem_of_mem p e₁ e₂ hz₁ hz₂

theorem isPullback_fst_snd {X : Scheme.{0}} (G : Over X) :
    IsPullback (fst G G) (snd G G) (toUnit G) (toUnit G) := by
  exact IsPullback.of_is_product (tensorProductIsBinaryProduct G G) isTerminalTensorUnit

theorem isPullback_mul_snd {X : Scheme.{0}} (G : Over X) [GrpObj G] :
    IsPullback (fst G G * snd G G) (snd G G) (toUnit G) (toUnit G) := by
  refine IsPullback.of_is_product (c := BinaryFan.mk (fst G G * snd G G) (snd G G)) ?_ isTerminalTensorUnit
  refine BinaryFan.IsLimit.mk _ (fun u v => lift (u * v⁻¹) v) ?_ ?_ ?_
  · intro T u v
    simp [comp_mul]
  · intro T u v
    simp
  · intro T u v m h₁ h₂
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h₁ h₂
    have h₃ : m ≫ fst G G * v = u := by
      rw [← h₂]
      exact (comp_mul m (fst G G) (snd G G)).symm.trans h₁
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simpa using eq_mul_inv_of_mul_eq h₃
    · simpa using h₂

theorem toUnit_left {X : Scheme.{0}} (G : Over X) : (toUnit G).left = G.hom := by
  simpa using Over.w (toUnit G)

theorem reldim_eq_unit {X : Scheme.{0}} (G : Over X) [GrpObj G] {n m : ℕ} {W V : G.left.Opens}
    (dW : SmoothOfRelativeDimension n (W.ι ≫ G.hom)) (dV : SmoothOfRelativeDimension m (V.ι ≫ G.hom))
    (g : G.left) (hg : g ∈ W) (hV : eSec G (G.hom g) ∈ V) : n = m := by
  have h₁ := (isPullback_fst_snd G).map (Over.forget X)
  have h₂ := (isPullback_mul_snd G).map (Over.forget X)
  simp only [Over.forget_map, toUnit_left] at h₁ h₂
  have p₁ : (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    simp
  have p₂ : (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = (η[G]).left (G.hom g) := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, comp_mul, lift_fst, lift_snd, mul_inv_cancel,
      Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply, toUnit_left]
  refine reldim_eq_of_two_pullbacks h₁ h₂ dW dV ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ?_ ?_
  · show (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ W
    rw [p₁]
    exact hg
  · show (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ V
    rw [p₂]
    unfold eSec at hV
    exact hV

private theorem smoothOfRelativeDimension_of_local {A S : Scheme.{0}} (f : A ⟶ S) (n : ℕ)
    (h : ∀ x : A, ∃ W : A.Opens, x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  rw [smoothOfRelativeDimension_iff]
  intro x
  obtain ⟨W, hxW, hW⟩ := h x
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := (smoothOfRelativeDimension_iff n (W.ι ≫ f)).1 hW ⟨x, hxW⟩
  have e₁ : W.ι ''ᵁ V ≤ f ⁻¹ᵁ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact e hv
  have e₂ : V ≤ W.ι ⁻¹ᵁ (W.ι ''ᵁ V) := fun v hv => ⟨v, hv, rfl⟩
  have hcomp := Scheme.Hom.appLE_comp_appLE W.ι f U (W.ι ''ᵁ V) V e₁ e₂
  have hiso : W.ι.appLE (W.ι ''ᵁ V) V e₂ = (W.ι.appIso V).hom := (Scheme.Hom.appIso_hom' W.ι V).symm
  have key : f.appLE U (W.ι ''ᵁ V) e₁ = (W.ι ≫ f).appLE U V e ≫ (W.ι.appIso V).inv := by
    rw [← hcomp, hiso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨U, hU, W.ι ''ᵁ V, hV.image_of_isOpenImmersion W.ι, ⟨⟨x, hxW⟩, hxV, rfl⟩, e₁, ?_⟩
  rw [key, CommRingCat.hom_comp]
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0 (W.ι.appIso V).inv.hom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv (W.ι.appIso V).symm.commRingCatIsoToRingEquiv
  have h1 := h0.comp hstd
  rwa [zero_add] at h1

theorem smoothGrp_relDim : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [Smooth G.hom],
    (∀ q : X, genPt ξ ⤳ q) → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro X Ω _ ξ G _ _ hgen
  obtain ⟨n₀, W₀, hW₀, d₀⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (genPt ξ))
  refine ⟨n₀, smoothOfRelativeDimension_of_local G.hom n₀ fun g => ?_⟩
  obtain ⟨n, W, hgW, dW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom g
  obtain ⟨m, V, hV, dV⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (G.hom g))
  have h₁ : n = m := reldim_eq_unit G dW dV g hgW hV
  have hsp : eSec G (genPt ξ) ⤳ eSec G (G.hom g) := (hgen (G.hom g)).map (eSec G).base.hom.continuous
  have h₂ : m = n₀ := relDim_eq_of_mem_of_mem G.hom dV d₀ (hsp.mem_open V.isOpen hV) hW₀
  rw [h₁, h₂] at dW
  exact ⟨W, hgW, dW⟩

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
