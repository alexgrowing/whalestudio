import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.TorsionLiftVal

theorem sections_restrict_bijective (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω]
    [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k)
    {X : Scheme.{0}} (p : X ⟶ Sp U) [IsFinite p] [Etale p] :
    Function.Bijective (fun s : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} =>
      (⟨spMap h ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ : {x : Sp k ⟶ X // x ≫ p = spMap h})) := by
  have inj : Function.Injective (fun s : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} =>
      (⟨spMap h ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ : {x : Sp k ⟶ X // x ≫ p = spMap h})) := by
    rintro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ e
    have e' : spMap h ≫ s₁ = spMap h ≫ s₂ := congrArg Subtype.val e
    haveI : LocallyOfFiniteType (Over.mk p).hom := inferInstanceAs (LocallyOfFiniteType p)
    haveI : FormallyUnramified (Over.mk p).hom := inferInstanceAs (FormallyUnramified p)
    haveI : IsSeparated (Over.mk p).hom := inferInstanceAs (IsSeparated p)
    let f₁ : Over.mk (𝟙 (Sp U)) ⟶ Over.mk p := Over.homMk s₁ h₁
    let f₂ : Over.mk (𝟙 (Sp U)) ⟶ Over.mk p := Over.homMk s₂ h₂
    have hr := (FinEt.comp_eq_comp_iff_range f₁ f₂ (spMap h)).1 e'
    haveI : PreconnectedSpace (Over.mk (𝟙 (Sp U))).left := inferInstanceAs (PreconnectedSpace (Sp U))
    have hc : IsClopen (Set.range (FinEt.agreeι f₁ f₂)) :=
      ⟨(FinEt.agreeι f₁ f₂).isClosedEmbedding.isClosed_range, (FinEt.agreeι f₁ f₂).isOpenEmbedding.isOpen_range⟩
    obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
    have hu : Set.range (FinEt.agreeι f₁ f₂) = Set.univ := hc.eq_univ ⟨_, hr ⟨z, rfl⟩⟩
    have := (FinEt.comp_eq_comp_iff_range f₁ f₂ (𝟙 _)).2 (by rw [hu]; exact Set.subset_univ _)
    apply Subtype.ext
    simpa [f₁, f₂] using this
  obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨w⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨hBfin, hB⟩ := FinEt.card_points_eq_finrank p (spMap h) z
  obtain ⟨-, hC⟩ := FinEt.card_points_eq_finrank p (spMap (algebraMap U Ω)) w
  haveI := hBfin
  haveI : Finite {s : Sp U ⟶ X // s ≫ p = 𝟙 _} := Finite.of_injective _ inj
  have hv : ValuativeCriterion p := by
    have hp : IsProper p := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let r : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} → {x : Sp Ω ⟶ X // x ≫ p = spMap (algebraMap U Ω)} :=
    fun s => ⟨spMap (algebraMap U Ω) ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩
  have hrs : Function.Surjective r := by
    rintro ⟨x, hx⟩
    let Q : ValuativeCommSq p :=
      { R := U, K := Ω, i₁ := x, i₂ := 𝟙 _, commSq := ⟨hx.trans (Category.comp_id _).symm⟩ }
    obtain ⟨W⟩ := hv Q
    exact ⟨⟨W.default.l, W.default.fac_right⟩, Subtype.ext W.default.fac_left⟩
  have hle := Nat.card_le_card_of_surjective r hrs
  have hrank := (Scheme.Hom.isLocallyConstant_finrank p).apply_eq_of_preconnectedSpace (spMap h z)
    (spMap (algebraMap U Ω) w)
  refine inj.bijective_of_nat_card_le ?_
  rw [hB, hrank, ← hC]
  exact hle

theorem torsion_lift_unique : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ y : Over.mk (spMap h ≫ u) ⟶ G, y ^ n = 1 → ∃! P : Over.mk u ⟶ G, P ^ n = 1 ∧ y.left = spMap h ≫ P.left := by
  intro U Ω k _ _ _ _ _ _ _ _ _ h S G _ hA u n hn y hy
  letI : GrpObj ((Over.pullback u).obj G) := Functor.grpObjObj
  have hgp : IsGrpPullback ((Over.pullback u).obj G) G u (pullback.fst G.hom u) := isGrpPullback_pullback G u
  haveI : IsAbelianScheme ((Over.pullback u).obj G) := GlobalTheory.isAbelianScheme_pullback_obj u G hA
  have hnU : IsUnit (n : Γ(Sp U, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of U)).inv.hom
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion ((Over.pullback u).obj G) hnU
  have key : ∀ {X : Scheme.{0}} (t : X ⟶ Sp U) (b : X ⟶ S), b = t ≫ u →
      ∃ Φ : (Over.mk t ⟶ torsion ((Over.pullback u).obj G) n) → (Over.mk b ⟶ G),
        Function.Injective Φ ∧ (∀ a, Φ a ^ n = 1) ∧ (∀ w : Over.mk b ⟶ G, w ^ n = 1 → ∃ a, Φ a = w) ∧
        ∀ a, (Φ a).left = a.left ≫ (torsion.ι ((Over.pullback u).obj G) n).left ≫ pullback.fst G.hom u := by
    intro X t b hb
    obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hgp t b hb
    refine ⟨fun a => e ((TorsionUnram.torsionEquiv _ n _) a).1, ?_, ?_, ?_, ?_⟩
    · intro a₁ a₂ h12
      exact (TorsionUnram.torsionEquiv _ n _).injective (Subtype.ext (e.injective h12))
    · intro a
      rw [← map_pow, ((TorsionUnram.torsionEquiv _ n _) a).2, map_one]
    · intro w hw
      refine ⟨(TorsionUnram.torsionEquiv _ n _).symm ⟨e.symm w, by rw [← map_pow, hw, map_one]⟩, ?_⟩
      simp
    · intro a
      rw [he, ← Category.assoc]
      rfl
  obtain ⟨Φk, injk, -, surjk, hk⟩ := key (spMap h) (spMap h ≫ u) rfl
  obtain ⟨ΦU, -, powU, surjU, hUl⟩ := key (𝟙 (Sp U)) u (Category.id_comp u).symm
  obtain ⟨τ, rfl⟩ := surjk y hy
  have hb := sections_restrict_bijective U Ω k h (torsion ((Over.pullback u).obj G) n).hom
  obtain ⟨⟨s, hs⟩, hs'⟩ := hb.2 ⟨τ.left, Over.w τ⟩
  have hs'' : spMap h ≫ s = τ.left := congrArg Subtype.val hs'
  let σ : Over.mk (𝟙 (Sp U)) ⟶ torsion ((Over.pullback u).obj G) n := Over.homMk s hs
  refine ⟨ΦU σ, ⟨powU σ, ?_⟩, ?_⟩
  · rw [hk, hUl, ← hs'']
    simp [σ]
  · rintro P ⟨hP, hPy⟩
    obtain ⟨σ', rfl⟩ := surjU P hP
    have hσ' : σ'.left ≫ (torsion ((Over.pullback u).obj G) n).hom = 𝟙 _ := Over.w σ'
    let τ' : Over.mk (spMap h) ⟶ torsion ((Over.pullback u).obj G) n :=
      Over.homMk (spMap h ≫ σ'.left) (by rw [Category.assoc, hσ']; exact Category.comp_id _)
    have e0 : Φk τ' = Φk τ := by
      apply Over.OverMorphism.ext
      rw [hk, hPy, hUl]
      simp [τ']
    have e1 : spMap h ≫ σ'.left = τ.left := congrArg (fun q => q.left) (injk e0)
    have e2 := hb.1 (a₁ := ⟨σ'.left, hσ'⟩) (a₂ := ⟨s, hs⟩) (Subtype.ext (e1.trans hs''.symm))
    have e3 : σ' = σ := Over.OverMorphism.ext (congrArg Subtype.val e2)
    rw [e3]

end GlobalTheory.TorsionLiftVal
