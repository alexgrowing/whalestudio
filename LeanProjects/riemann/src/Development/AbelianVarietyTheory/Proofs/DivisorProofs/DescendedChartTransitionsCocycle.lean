import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumDescent.cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → ∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k := by
  intro R _ _ _ _ S X π hπp hπs hS U hU J e he V τ hV hτ i j k T x y w hxy hw
  set pP := pullback.fst U.hom π with hpP

  set O : U.left.Opens := V i j ⊓ V i k with hO
  let m₁ : O.toScheme ⟶ (V i j).toScheme := U.left.homOfLE inf_le_left
  let m₂ : O.toScheme ⟶ (V i k).toScheme := U.left.homOfLE inf_le_right
  have hm₁ : m₁ ≫ (V i j).ι = O.ι := Scheme.homOfLE_ι _ _
  have hm₂ : m₂ ≫ (V i k).ι = O.ι := Scheme.homOfLE_ι _ _

  let FinalForm : (pullback U.hom π).Opens := pP ⁻¹ᵁ O
  let p' : FinalForm.toScheme ⟶ O.toScheme := pP ∣_ O
  have hp' : p' ≫ O.ι = FinalForm.ι ≫ pP := morphismRestrict_ι _ _
  have hsq : IsPullback p' (FinalForm.ι ≫ pullback.snd U.hom π) (O.ι ≫ U.hom) π :=
    (isPullback_morphismRestrict pP O).paste_vert (IsPullback.of_hasPullback U.hom π)
  have hp'surj : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hπs
  have hZ : ∀ (l : J) (z : FinalForm.toScheme), (FinalForm.ι ≫ e i) z ∈ Set.range (e l) ↔ pP (FinalForm.ι z) ∈ V i l := by
    intro l z; rw [hV]; rfl
  have hZO : ∀ z : FinalForm.toScheme, pP (FinalForm.ι z) ∈ O := by
    intro z
    have : (FinalForm.ι ≫ pP) z ∈ O := by
      rw [← hp']; exact (Scheme.Opens.range_ι O).subset ⟨p' z, rfl⟩
    exact this
  have rj : Set.range (FinalForm.ι ≫ e i) ⊆ Set.range (e j) := by
    rintro _ ⟨z, rfl⟩; exact (hZ j z).2 (hZO z).1
  have rk : Set.range (FinalForm.ι ≫ e i) ⊆ Set.range (e k) := by
    rintro _ ⟨z, rfl⟩; exact (hZ k z).2 (hZO z).2
  let b := IsOpenImmersion.lift (e j) (FinalForm.ι ≫ e i) rj
  let c := IsOpenImmersion.lift (e k) (FinalForm.ι ≫ e i) rk
  have hb : b ≫ e j = FinalForm.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
  have hc : c ≫ e k = FinalForm.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _

  have h1 : p' ≫ m₁ ≫ τ i j = b ≫ pP :=
    hτ i j _ FinalForm.ι b (p' ≫ m₁) hb.symm (by rw [Category.assoc, hm₁, hp'])
  have h2 : p' ≫ m₂ ≫ τ i k = c ≫ pP :=
    hτ i k _ FinalForm.ι c (p' ≫ m₂) hc.symm (by rw [Category.assoc, hm₂, hp'])

  have rw₀ : Set.range (m₁ ≫ τ i j) ⊆ Set.range (V j k).ι := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨z, rfl⟩ := hp'surj.surj o
    have e1 : (p' ≫ m₁ ≫ τ i j) z = (b ≫ pP) z := by rw [h1]
    have e2 : (b ≫ e j) z = (c ≫ e k) z := by rw [hb, hc]
    simp only [Scheme.Hom.comp_apply] at e1 e2
    rw [Scheme.Opens.range_ι]
    show (m₁ ≫ τ i j) (p' z) ∈ V j k
    simp only [Scheme.Hom.comp_apply]
    rw [e1, hV, e2]
    exact ⟨_, rfl⟩
  let w₀ := IsOpenImmersion.lift (V j k).ι (m₁ ≫ τ i j) rw₀
  have hw₀ : w₀ ≫ (V j k).ι = m₁ ≫ τ i j := IsOpenImmersion.lift_fac _ _ _
  have h3 : p' ≫ w₀ ≫ τ j k = c ≫ pP :=
    hτ j k _ b c (p' ≫ w₀) (hb.trans hc.symm) (by rw [Category.assoc, hw₀, h1])
  haveI := hU
  have heq : pullback.fst p' p' ≫ c ≫ pP = pullback.snd p' p' ≫ c ≫ pP := by
    rw [← h2, pullback.condition_assoc]
  obtain ⟨h₀, -, huniq⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S O.toScheme FinalForm.toScheme U.left π (O.ι ≫ U.hom) p'
    (FinalForm.ι ≫ pullback.snd U.hom π) hπp hπs hS inferInstance hsq (c ≫ pP) heq
  have E : w₀ ≫ τ j k = m₂ ≫ τ i k := (huniq _ h3).trans (huniq _ h2).symm

  have rt : Set.range (x ≫ (V i j).ι) ⊆ Set.range O.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← Scheme.Opens.range_ι (V i j)]; exact ⟨x s, rfl⟩
    · rw [hxy, ← Scheme.Opens.range_ι (V i k)]; exact ⟨y s, rfl⟩
  let t := IsOpenImmersion.lift O.ι (x ≫ (V i j).ι) rt
  have ht : t ≫ O.ι = x ≫ (V i j).ι := IsOpenImmersion.lift_fac _ _ _
  have tx : t ≫ m₁ = x := (cancel_mono (V i j).ι).1 (by rw [Category.assoc, hm₁, ht])
  have ty : t ≫ m₂ = y := (cancel_mono (V i k).ι).1 (by rw [Category.assoc, hm₂, ht, hxy])
  have tw : w = t ≫ w₀ := (cancel_mono (V j k).ι).1 (by rw [← hw, Category.assoc, hw₀, ← Category.assoc, tx])
  rw [tw, Category.assoc, E, ← Category.assoc, ty]
