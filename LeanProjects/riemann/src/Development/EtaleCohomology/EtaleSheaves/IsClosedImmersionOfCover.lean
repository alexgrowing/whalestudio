import Development.EtaleCohomology.EtaleSheaves.CorePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.CorePf2

theorem isClosedImmersion_of_cover {X Y : Scheme.{0}} (f : X ⟶ Y) {ι : Type} (O : ι → Y.Opens)
    (hcl : IsClosed (Set.range f)) (hcov : Set.range f ⊆ ⋃ i, (O i : Set Y))
    (hloc : ∀ i, IsClosedImmersion (f ∣_ O i)) : IsClosedImmersion f := by
  let O' : Option ι → Y.Opens := fun o => o.elim ⟨(Set.range f)ᶜ, hcl.isOpen_compl⟩ O
  refine IsZariskiLocalAtTarget.of_iSup_eq_top O' ?_ ?_
  · rw [eq_top_iff]
    intro y _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hy : y ∈ Set.range f
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
      exact ⟨some i, hi⟩
    · exact ⟨none, hy⟩
  · intro o
    cases o with
    | none =>
      have : IsEmpty (f ⁻¹ᵁ O' none).toScheme := ⟨fun x => x.2 ⟨x.1, rfl⟩⟩
      infer_instance
    | some i => exact hloc i

theorem range_closed {S X₁ P : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁] (q : P ⟶ S) {V : Scheme.{0}}
    (γ : V ⟶ pullback p₁ q) : IsClosed (Set.range (γ.imageι ≫ pullback.snd p₁ q)) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact (pullback.snd p₁ q).isClosedMap _ γ.imageι.isClosedEmbedding.isClosed_range

def Covered : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁]
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    ∀ (V : X₁.Opens), IsAffineOpen V → ∀ (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q),
      γ ≫ pullback.fst p₁ q = V.ι → (∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) →
      Set.range (γ.imageι ≫ pullback.snd p₁ q) ⊆ ⋃ j, ((π j ⁻¹ᵁ W j : P.Opens) : Set P)

def Piece : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁]
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    ∀ (V : X₁.Opens), IsAffineOpen V → ∀ (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q),
      γ ≫ pullback.fst p₁ q = V.ι → (∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) →
      ∀ j, IsClosedImmersion ((γ.imageι ≫ pullback.snd p₁ q) ∣_ (π j ⁻¹ᵁ W j))

theorem Core_of (hC : Covered) (hP : Piece) : LateralTheory.E.ChowGraphCut.Core := by
  intro S X₁ p₁ _ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  obtain ⟨x₀⟩ : Nonempty X₁ := inferInstance
  obtain ⟨j₀, -⟩ := hUc x₀
  let V₀ : X₁.Opens := Finset.univ.inf U
  have hV₀ : ∀ j, V₀ ≤ U j := fun j => Finset.inf_le (Finset.mem_univ j)
  obtain ⟨x, hx⟩ := LateralTheory.E.CorePf.inf_nonempty U hUn _ ⟨j₀, Finset.mem_univ _⟩
  obtain ⟨V', hVa, hxV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₁.isBasis_affineOpens (U := V₀) hx
  obtain ⟨V, rfl⟩ : ∃ V : X₁.Opens, V = V' := ⟨V', rfl⟩
  replace hVa : IsAffineOpen V := hVa
  have hV : ∀ j, (V : X₁.Opens) ≤ U j := fun j => hVle.trans (hV₀ j)
  obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := hUP ((V : X₁.Opens).ι ≫ p₁) (fun j => X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) (by
    intro j
    simp only [Category.assoc, hc j, Scheme.homOfLE_ι_assoc])
  let γ : (V : X₁.Opens).toScheme ⟶ pullback p₁ q := pullback.lift (V : X₁.Opens).ι g hg1.symm
  have hγ1 : γ ≫ pullback.fst p₁ q = (V : X₁.Opens).ι := pullback.lift_fst _ _ _
  have hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι := by
    intro j; rw [pullback.lift_snd_assoc, hg2 j]
  refine ⟨γ.image, γ.imageι, V, γ.toImage, inferInstance,
    isClosedImmersion_of_cover _ (fun j => π j ⁻¹ᵁ W j) (range_closed p₁ q γ)
      (hC p₁ n U Pj qj W e P q π hUc hsep he hc hπ V hVa hV γ hγ1 hγ2)
      (hP p₁ n U Pj qj W e P q π hUc hsep he hc hπ V hVa hV γ hγ1 hγ2), ⟨x, hxV⟩, ?_⟩
  rw [Scheme.Hom.toImage_imageι_assoc, hγ1]

end LateralTheory.E.CorePf2

end
