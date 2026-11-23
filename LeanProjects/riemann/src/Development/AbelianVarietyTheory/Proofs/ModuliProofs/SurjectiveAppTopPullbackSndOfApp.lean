import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

private theorem surjective_comp_isIso_of_surjective {A B C : CommRingCat} (a : A ⟶ B) (b : B ⟶ C) [IsIso b]
    (ha : Function.Surjective a.hom) : Function.Surjective (a ≫ b).hom := by
  intro y
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso b).2 y
  obtain ⟨w, rfl⟩ := ha z
  exact ⟨w, rfl⟩

theorem surjective_appTop_pullback_snd_of_app {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : ∀ U : S.Opens, Function.Surjective (f.app U).hom) :
    Function.Surjective (pullback.snd f V.ι).appTop.hom := by
  have hr : Function.Surjective (f ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    exact @surjective_comp_isIso_of_surjective _ _ _ _ _ (Functor.map_isIso _ _) (h _)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop]
  exact @surjective_comp_isIso_of_surjective _ _ _ _ _
    (inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))) hr

theorem exists_gen_of_local_of_section : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (σ : S ⟶ X) (N : LB X), N.IsLB →
    σ ≫ f = 𝟙 S → (∀ U : S.Opens, Function.Surjective (f.app U).hom) →
    (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (N.pull (f ⁻¹ᵁ U).ι).Gen, t.IsGen) →
    (∃ t : (N.pull σ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro X S f σ N hN hσ hf hl hg
  obtain ⟨c, hc⟩ := hg
  have hp : ∀ V : S.Opens, Function.Surjective (pullback.snd f V.ι).appTop.hom :=
    fun V => surjective_appTop_pullback_snd_of_app f V hf
  have e : σ ≫ f ≫ σ = σ := by rw [← Category.assoc, hσ, Category.id_comp]
  have h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U),
      ∏ k, h (σ ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by
    intro U _ h
    simp [Fin.prod_univ_two, e]
  have hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb N (fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k)
        (![1, -1] : Fin 2 → ℤ)), t.IsGen := by
    intro s
    obtain ⟨U, hsU, t, ht⟩ := hl s
    refine ⟨U, hsU, ?_⟩
    let c₁ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c ((f ⁻¹ᵁ U).ι ≫ f)
    have hc₁ : c₁.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc _
    let c₂ := LB.invGen N _ _ c₁
    have hc₂ : c₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ c₁ hc₁
    let m := LB.mulGen N (fun _ : PUnit => (f ⁻¹ᵁ U).ι) (fun _ => 1) _ _ t c₂
    have hm : m.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ t c₂ ht hc₂
    obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
      (φ' := fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) (ε' := (![1, -1] : Fin 2 → ℤ))
      (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m hm
    exact ⟨g, hg⟩
  obtain ⟨u, hu⟩ := exists_gen_of_local_on_base hN (K := Fin 2) ![𝟙 X, f ≫ σ] ![1, -1] f σ hσ hp h0 hloc
  let c₃ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c f
  have hc₃ : c₃.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc f
  let m₂ := LB.mulGen N _ _ _ _ u c₃
  have hm₂ : m₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ u c₃ hu hc₃
  obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN (φ' := fun _ : PUnit => 𝟙 X) (ε' := fun _ => 1)
    (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m₂ hm₂
  exact BoxTheta.exists_gen_of_section N (𝟙 X) (𝟙 X) (Category.id_comp _) g hg

end GlobalTheory
