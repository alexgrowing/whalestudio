import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfEtaleOfSurjectiveOfUniversallyInjectiveAlStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNearPointOfEtaleOnFibreSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_common_ext_of_apply_eq {T : Scheme.{0}} (K Ω : Type) [Field K] [Field Ω]
    (a : Sp K ⟶ T) (b : Sp Ω ⟶ T)
    (u : Sp K) (v : Sp Ω) (e : a u = b v) :
    ∃ (L : Type) (_ : Field L) (j₁ : K →+* L) (j₂ : Ω →+* L), spMap j₁ ≫ a = spMap j₂ ≫ b := by
  obtain ⟨⟨s₁, φ₁⟩, e₁⟩ := (Scheme.SpecToEquivOfField K T).symm.surjective a
  obtain ⟨⟨s₂, φ₂⟩, e₂⟩ := (Scheme.SpecToEquivOfField Ω T).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at e₁ e₂
  have hs : s₁ = s₂ := by
    rw [← e₁, ← e₂] at e
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply,
      Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hs
  obtain ⟨L, _, j₁, j₂, hj⟩ := GlobalTheory.exists_common_field_extension (T.residueField s₁) K Ω φ₁.hom φ₂.hom
  refine ⟨L, inferInstance, j₁, j₂, ?_⟩
  rw [← e₁, ← e₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext1
  exact hj

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem universallyInjective_of_fieldPoints' {G P : Scheme.{0}} (h : G ⟶ P)
    (H : ∀ (K : Type) [Field K] (z z' : Sp K ⟶ G), z ≫ h = z' ≫ h → z = z') :
    UniversallyInjective h := by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  intro x
  let w := (Limits.pullback h h).fromSpecResidueField x
  have e : w ≫ Limits.pullback.fst h h = w ≫ Limits.pullback.snd h h :=
    H ((Limits.pullback h h).residueField x) _ _ (by
      simp only [Category.assoc, Limits.pullback.condition])
  have e2 : (w ≫ Limits.pullback.fst h h) ≫ Limits.pullback.diagonal h = w := by
    apply Limits.pullback.hom_ext
    · simp
    · simp [e]
  let pt : Spec ((Limits.pullback h h).residueField x) := IsLocalRing.closedPoint _
  refine ⟨(w ≫ Limits.pullback.fst h h) pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, e2, Scheme.fromSpecResidueField_apply]

theorem isIso_of_isIso_fibres : ∀ (T X Z : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p), Smooth p → Smooth q → (∀ s : T, ∃ (Ω : Type) (_ : Field Ω) (x : Sp Ω ⟶ T), s ∈ Set.range x ∧ IsIso (pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp))) → IsIso h := by
  intro T X Z p q h hh hp hq H
  apply GlobalTheory.T.isIso_of_etale_of_surjective_of_universallyInjective' X Z h
  ·
    have hloc : ∀ z : X, ∃ V : X.Opens, z ∈ V ∧ Etale (V.ι ≫ h) := by
      intro z
      obtain ⟨Ω, _, x, ⟨t, ht⟩, hiso⟩ := H (p z)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x) z t ht.symm
      have hE : Etale ((⊤ : (pullback p x).Opens).ι ≫
          pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) := inferInstance
      obtain ⟨V, hV, hVe⟩ := GlobalTheory.T.etale_near_point_of_etale_on_fibre_smooth T X Z p q h hh hp hq Ω x ⊤ w trivial hE
      exact ⟨V, hw ▸ hV, hVe⟩
    choose V hV hVe using hloc
    have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) V ?_ hVe
    exact top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hV z⟩
  ·
    refine ⟨fun y => ?_⟩
    obtain ⟨Ω, _, x, ⟨t, ht⟩, hiso⟩ := H (q y)
    obtain ⟨v, hv, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := x) y t ht.symm
    let m := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)
    refine ⟨pullback.fst p x (inv m v), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.lift_fst (f := q) (g := x) (pullback.fst p x ≫ h)
      (pullback.snd p x ≫ 𝟙 _) (by simp [hh, pullback.condition]), Scheme.Hom.comp_apply]
    change pullback.fst q x (m (inv m v)) = y
    rw [← Scheme.Hom.comp_apply m, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]
    exact hv
  ·
    refine universallyInjective_of_fieldPoints' h fun K _ z z' hz => ?_
    let u : Sp K := IsLocalRing.closedPoint K
    obtain ⟨Ω, _, x, ⟨t, ht⟩, hiso⟩ := H ((z ≫ p) u)
    obtain ⟨L, _, j₁, j₂, hj⟩ := exists_common_ext_of_apply_eq K Ω (z ≫ p) x u t ht.symm
    have hj' : spMap j₁ ≫ z' ≫ p = spMap j₂ ≫ x := by
      rw [← hh, ← Category.assoc z', ← hz, Category.assoc, hh, hj]
    let m := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)
    let a := pullback.lift (f := p) (g := x) (spMap j₁ ≫ z) (spMap j₂) (by rw [Category.assoc, hj])
    let a' := pullback.lift (f := p) (g := x) (spMap j₁ ≫ z') (spMap j₂) (by rw [Category.assoc, hj'])
    have haa : a ≫ m = a' ≫ m := by
      apply pullback.hom_ext
      · simp only [m, a, a', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hz]
      · simp only [m, a, a', pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.comp_id]
    have haa' : a = a' := (cancel_mono m).1 haa
    have := congrArg (· ≫ pullback.fst p x) haa'
    simp only [a, a', pullback.lift_fst] at this
    exact GlobalTheory.Mum.spMap_field_cancel K L j₁ X z z' this

end GlobalTheory.Mum
