import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.G3

private theorem ordExStep (hS : OrdStep) {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hcf : IsFinite c) (hce : Etale c) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (huniv : ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin d → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
      ∃! w : U ⟶ W, w ≫ c = z ∧ ∀ j, w ≫ σ j = y j) :
    ∃ (W' : Scheme.{0}) (c' : W' ⟶ Z) (σ' : Fin (d + 1) → (W' ⟶ Y)), IsFinite c' ∧ Etale c' ∧
      (∀ j, σ' j ≫ s = c') ∧
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W'), Function.Injective fun j => x ≫ σ' j) ∧
      ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin (d + 1) → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
        (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
        ∃! w : U ⟶ W', w ≫ c' = z ∧ ∀ j, w ≫ σ' j = y j := by
  haveI := hcf
  haveI := hce
  let P := pullback s c
  have hsq : ∀ j, σ j ≫ s = 𝟙 W ≫ c := fun j => by rw [hσ j, Category.id_comp]
  let sec : Fin d → (W ⟶ P) := fun j => pullback.lift (σ j) (𝟙 W) (hsq j)
  have hsec1 : ∀ j, sec j ≫ pullback.fst s c = σ j := fun j => pullback.lift_fst _ _ _
  have hsec2 : ∀ j, sec j ≫ pullback.snd s c = 𝟙 W := fun j => pullback.lift_snd _ _ _
  haveI hOP : MorphismProperty.HasOfPostcompProperty (@IsOpenImmersion : MorphismProperty Scheme)
      (@Etale : MorphismProperty Scheme) := by
    apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2
    intro X Y f hf
    haveI : Etale f := hf
    exact inferInstanceAs <| IsOpenImmersion (pullback.diagonal f)
  have hopen : ∀ j, IsOpenImmersion (sec j) := fun j =>
    MorphismProperty.of_postcomp (W := (@IsOpenImmersion : MorphismProperty Scheme))
      (W' := (@Etale : MorphismProperty Scheme)) (sec j) (pullback.snd s c)
      (inferInstanceAs (Etale (pullback.snd s c)))
      (by rw [hsec2]; exact inferInstanceAs (IsOpenImmersion (𝟙 W)))
  have hclosed : ∀ j, IsClosedImmersion (sec j) := fun j => by
    haveI : IsClosedImmersion (sec j ≫ pullback.snd s c) := by
      rw [hsec2]; infer_instance
    exact IsClosedImmersion.of_comp (sec j) (pullback.snd s c)
  let S : Set P := ⋃ j, Set.range (sec j).base
  have hSc : IsClosed S := isClosed_iUnion_of_finite fun j => (hclosed j).isClosedEmbedding.isClosed_range
  have hSo : IsOpen S := isOpen_iUnion fun j => (hopen j).base_open.isOpen_range
  let O : P.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hOr : Set.range O.ι.base = Sᶜ := O.range_ι
  haveI : IsClosedImmersion O.ι := .of_isPreimmersion _ (by rw [hOr]; exact hSo.isClosed_compl)
  have hpt : ∀ (j : Fin d) (Ω : Type) [Field Ω] (x : sp Ω ⟶ P),
      x.base (IsLocalRing.closedPoint Ω) ∈ Set.range (sec j).base →
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j Ω _ x hx
    have hr : Set.range x.base ⊆ Set.range (sec j).base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint Ω)]
    haveI := hopen j
    have hf := IsOpenImmersion.lift_fac (sec j) x hr
    rw [← hf, Category.assoc, Category.assoc, hsec1, reassoc_of% hsec2]
  have hback : ∀ (j : Fin d) {T : Scheme.{0}} (x : T ⟶ P),
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j → x = (x ≫ pullback.snd s c) ≫ sec j := by
    intro j T x hx
    apply pullback.hom_ext
    · rw [Category.assoc, hsec1, hx, Category.assoc]
    · rw [Category.assoc, hsec2, Category.comp_id]
  refine ⟨O, O.ι ≫ pullback.snd s c ≫ c,
    Fin.snoc (α := fun _ => ((O : Scheme) ⟶ Y)) (fun j => O.ι ≫ pullback.snd s c ≫ σ j)
      (O.ι ≫ pullback.fst s c), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.snoc_last, Category.assoc, pullback.condition]
    · simp only [Fin.snoc_castSucc, Category.assoc, hσ j]
  · intro Ω _ x
    have key : ∀ j : Fin d, x ≫ O.ι ≫ pullback.fst s c ≠ x ≫ O.ι ≫ pullback.snd s c ≫ σ j := by
      intro j h
      have h2 := hback j (x ≫ O.ι) (by simpa only [Category.assoc] using h)
      have hin : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ S := by
        rw [h2]
        exact Set.mem_iUnion.2 ⟨j, _, rfl⟩
      have hO : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ Set.range O.ι.base :=
        ⟨x.base (IsLocalRing.closedPoint Ω), rfl⟩
      rw [hOr] at hO
      exact hO hin
    intro a b hab
    simp only at hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab (key j)
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab.symm (key i)
      | cast j =>
        simp only [Fin.snoc_castSucc] at hab
        exact congrArg Fin.castSucc (hinj Ω (x ≫ O.ι ≫ pullback.snd s c) (by simpa only [Category.assoc] using hab))
  · intro U z y hy hinjU
    obtain ⟨w0, ⟨hw0c, hw0σ⟩, hw0u⟩ := huniv U z (fun j => y j.castSucc) (fun j => hy _)
      (fun Ω _ x a b h => Fin.castSucc_injective _ (hinjU Ω x h))
    let φ : U ⟶ P := pullback.lift (y (Fin.last d)) w0 (by rw [hy, hw0c])
    have hφ1 : φ ≫ pullback.fst s c = y (Fin.last d) := pullback.lift_fst _ _ _
    have hφ2 : φ ≫ pullback.snd s c = w0 := pullback.lift_snd _ _ _
    have hrange : Set.range φ.base ⊆ Set.range O.ι.base := by
      rintro _ ⟨u, rfl⟩
      rw [hOr]
      intro hu
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hu
      let x := U.fromSpecResidueField u
      have hxu : x.base (IsLocalRing.closedPoint (U.residueField u)) = u :=
        U.fromSpecResidueField_apply u _
      have := hpt j (U.residueField u) (x ≫ φ) (by
        show φ.base (x.base _) ∈ _
        rw [hxu]
        exact hj)
      rw [Category.assoc, Category.assoc, hφ1, reassoc_of% hφ2, hw0σ] at this
      exact (Fin.castSucc_lt_last j).ne (hinjU _ x this).symm
    refine ⟨IsOpenImmersion.lift O.ι φ hrange, ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0c]
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [Fin.snoc_last, IsOpenImmersion.lift_fac_assoc, hφ1]
      · rw [Fin.snoc_castSucc, IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0σ]
    · rintro w' ⟨hw'c, hw'σ⟩
      rw [← cancel_mono O.ι, IsOpenImmersion.lift_fac]
      have e2 : w' ≫ O.ι ≫ pullback.snd s c = w0 := by
        refine hw0u _ ⟨by simpa only [Category.assoc] using hw'c, fun j => ?_⟩
        have := hw'σ j.castSucc
        rw [Fin.snoc_castSucc] at this
        simpa only [Category.assoc] using this
      apply pullback.hom_ext
      · have := hw'σ (Fin.last d)
        rw [Fin.snoc_last] at this
        rw [Category.assoc, this, hφ1]
      · rw [Category.assoc, e2, hφ2]

theorem pOrdEx : OrdStep → OrdEx := by
  intro hS Z Y s _ _ d
  induction d with
  | zero =>
    refine ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0, ?_, ?_⟩
    · intro Ω _ x a
      exact a.elim0
    · intro U z y _ _
      exact ⟨z, ⟨Category.comp_id _, fun j => j.elim0⟩, fun w hw => by simpa using hw.1⟩
  | succ d ih =>
    obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := ih
    exact ordExStep hS s d c σ hcf hce hσ hinj huniv

end UpperTheory.Gal.G3

end
