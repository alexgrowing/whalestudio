import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.TwoTorsionInclusion

private noncomputable abbrev Two (S : Scheme.{0}) : Scheme.{0} := ∐ fun _ : Fin 2 ↦ S

private noncomputable abbrev inc (S : Scheme.{0}) (i : Fin 2) : S ⟶ Two S :=
  Sigma.ι (fun _ : Fin 2 ↦ S) i

private noncomputable abbrev cd (S : Scheme.{0}) : Two S ⟶ S := Sigma.desc fun _ ↦ 𝟙 S

private lemma mem_zero_iff (S : Scheme.{0}) (x : Two S) :
    x ∈ (inc S 0).opensRange ↔ x ∉ (inc S 1).opensRange := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun _ : Fin 2 ↦ S)).surjective x
  simp only [sigmaMk_mk, Scheme.Hom.mem_opensRange, inc, sigmaι_eq_iff]
  fin_cases i <;> simp

private lemma isClosed_one (S : Scheme.{0}) : IsClosed ((inc S 1).opensRange : Set (Two S)) := by
  rw [← isOpen_compl_iff]
  have : ((inc S 1).opensRange : Set (Two S))ᶜ = ((inc S 0).opensRange : Set (Two S)) := by
    ext x
    exact (mem_zero_iff S x).symm
  rw [this]
  exact (inc S 0).opensRange.isOpen

private lemma restrict_eq {S X Z : Scheme.{0}} (y : X ⟶ Two S) (i : Fin 2) (j : Z ⟶ X)
    (h : ∀ z, y (j z) ∈ (inc S i).opensRange) : j ≫ y = j ≫ y ≫ cd S ≫ inc S i := by
  have hr : Set.range (j ≫ y).base ⊆ Set.range (inc S i).base := by
    rintro _ ⟨z, rfl⟩
    exact h z
  set L := IsOpenImmersion.lift (inc S i) (j ≫ y) hr
  have e : L ≫ inc S i = j ≫ y := IsOpenImmersion.lift_fac _ _ _
  rw [← reassoc_of% e, ← e]
  simp [inc, cd]

private lemma core {S X : Scheme.{0}} (f : X ⟶ S) (W : X.Opens) (hW : IsClosed (W : Set X)) :
    ∃! y : X ⟶ Two S, y ≫ cd S = f ∧ y ⁻¹ᵁ (inc S 1).opensRange = W := by
  let W' : X.Opens := ⟨(W : Set X)ᶜ, hW.isOpen_compl⟩
  have hc : IsCompl W'.ι.opensRange W.ι.opensRange := by
    simp only [Scheme.Opens.opensRange_ι]
    constructor
    · rw [disjoint_iff, ← SetLike.coe_set_eq]
      ext x
      simp [W']
    · rw [codisjoint_iff, ← SetLike.coe_set_eq]
      ext x
      simp [W']
  obtain ⟨hcol⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl W'.ι W.ι hc
  have ext : ∀ {T : Scheme.{0}} (a b : X ⟶ T), W'.ι ≫ a = W'.ι ≫ b → W.ι ≫ a = W.ι ≫ b → a = b :=
    fun a b h0 h1 ↦ BinaryCofan.IsColimit.hom_ext hcol h0 h1
  have key : ∀ y' : X ⟶ Two S, y' ≫ cd S = f → y' ⁻¹ᵁ (inc S 1).opensRange = W →
      W'.ι ≫ y' = W'.ι ≫ f ≫ inc S 0 ∧ W.ι ≫ y' = W.ι ≫ f ≫ inc S 1 := by
    intro y' h1 h2
    constructor
    · rw [restrict_eq y' 0 W'.ι, reassoc_of% h1]
      intro z
      rw [mem_zero_iff]
      intro hz
      have hm : W'.ι z ∈ y' ⁻¹ᵁ (inc S 1).opensRange := hz
      rw [h2] at hm
      have hz' : z.1 ∉ W := z.2
      exact hz' hm
    · rw [restrict_eq y' 1 W.ι, reassoc_of% h1]
      intro z
      have hm : W.ι z ∈ y' ⁻¹ᵁ (inc S 1).opensRange := by
        rw [h2]
        exact z.2
      exact hm
  obtain ⟨y0, hy0, hy1⟩ := BinaryCofan.IsColimit.desc' hcol (W'.ι ≫ f ≫ inc S 0) (W.ι ≫ f ≫ inc S 1)
  obtain ⟨y, rfl⟩ : ∃ y : X ⟶ Two S, y = y0 := ⟨y0, rfl⟩
  change W'.ι ≫ y = _ at hy0
  change W.ι ≫ y = _ at hy1
  refine ⟨y, ⟨ext (y ≫ cd S) f (by rw [reassoc_of% hy0]; simp [inc, cd])
    (by rw [reassoc_of% hy1]; simp [inc, cd]), ?_⟩, ?_⟩
  · ext x
    by_cases hx : x ∈ W
    · obtain ⟨z, rfl⟩ : ∃ z : W.toScheme, W.ι z = x := ⟨⟨x, hx⟩, rfl⟩
      have e : y (W.ι z) = inc S 1 (f (W.ι z)) := by
        rw [show y (W.ι z) = (W.ι ≫ y) z from rfl, hy1] <;> rfl
      refine iff_of_true ?_ hx
      show y (W.ι z) ∈ (inc S 1).opensRange
      rw [e]
      exact ⟨_, rfl⟩
    · obtain ⟨z, rfl⟩ : ∃ z : W'.toScheme, W'.ι z = x := ⟨⟨x, hx⟩, rfl⟩
      have e : y (W'.ι z) = inc S 0 (f (W'.ι z)) := by
        rw [show y (W'.ι z) = (W'.ι ≫ y) z from rfl, hy0] <;> rfl
      refine iff_of_false ?_ hx
      show y (W'.ι z) ∉ (inc S 1).opensRange
      rw [e, ← mem_zero_iff]
      exact ⟨_, rfl⟩
  · rintro y' ⟨h1, h2⟩
    obtain ⟨k0, k1⟩ := key y' h1 h2
    exact ext _ _ (k0.trans hy0.symm) (k1.trans hy1.symm)

private lemma isIso_fst {S : Scheme.{0}} (T : Over S) : IsIso (fst T (Over.mk (𝟙 S))) := by
  have ht : IsTerminal (Over.mk (𝟙 S)) := Over.mkIdTerminal
  refine ⟨⟨lift (𝟙 T) (ht.from T), ?_, by simp⟩⟩
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · exact ht.hom_ext _ _

end UpperTheory.TwoTorsionInclusion

open UpperTheory.TwoTorsionInclusion in
theorem UpperTheory.exists_clopRep_trivial :
    ∀ (S : Scheme.{0}), ∃ (Y : Over S) (U : (Y ⊗ Over.mk (𝟙 S)).left.Opens), UpperTheory.RepresentationRank.Rep (Over.mk (𝟙 S)) Y U ∧ IsFinite Y.hom ∧ Etale Y.hom := by
  intro S
  refine ⟨Over.mk (cd S), (fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange,
    ⟨(isClosed_one S).preimage (Scheme.Hom.continuous _), ?_⟩,
    (GlobalTheory.FinEt.isSplitOfRank_sigmaDesc S 2).isFinite, (GlobalTheory.FinEt.isSplitOfRank_sigmaDesc S 2).etale⟩
  intro T V hV
  have hiso : IsIso (fst T (Over.mk (𝟙 S))).left := by
    have := isIso_fst T
    exact (inferInstance : IsIso ((Over.forget S).map (fst T (Over.mk (𝟙 S)))))
  set φ := (fst T (Over.mk (𝟙 S))).left with hφ
  have h1 : ∀ x, inv φ (φ x) = x := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  have h2 : ∀ t, φ (inv φ t) = t := fun t ↦ by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hpre : ∀ (y : T ⟶ Over.mk (cd S)) x,
      x ∈ (y ▷ Over.mk (𝟙 S)).left ⁻¹ᵁ
        ((fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange) ↔
        y.left (φ x) ∈ (inc S 1).opensRange := by
    intro y x
    show (fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ((y ▷ Over.mk (𝟙 S)).left x) ∈
      (inc S 1).opensRange ↔ _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerRight_fst, Over.comp_left,
      Scheme.Hom.comp_apply]
  let W : T.left.Opens := (inv φ) ⁻¹ᵁ V
  have hW : IsClosed (W : Set T.left) := hV.preimage (Scheme.Hom.continuous _)
  have hiff : ∀ y : T ⟶ Over.mk (cd S), (y ▷ Over.mk (𝟙 S)).left ⁻¹ᵁ
      ((fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange) = V ↔
      y.left ⁻¹ᵁ (inc S 1).opensRange = W := by
    intro y
    constructor
    · intro h
      refine SetLike.ext fun t ↦ ?_
      show y.left t ∈ (inc S 1).opensRange ↔ inv φ t ∈ V
      rw [← h, hpre, h2]
    · intro h
      refine SetLike.ext fun x ↦ ?_
      rw [hpre]
      show φ x ∈ y.left ⁻¹ᵁ (inc S 1).opensRange ↔ x ∈ V
      rw [h]
      show inv φ (φ x) ∈ V ↔ x ∈ V
      rw [h1]
  obtain ⟨y0, ⟨e0, e1⟩, hu⟩ := core T.hom W hW
  refine ⟨Over.homMk y0 e0, (hiff _).2 e1, fun y hy ↦ ?_⟩
  exact Over.OverMorphism.ext (hu y.left ⟨Over.w y, (hiff y).1 hy⟩)
