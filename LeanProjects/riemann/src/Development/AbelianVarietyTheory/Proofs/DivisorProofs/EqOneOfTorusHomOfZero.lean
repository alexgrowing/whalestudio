import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section SlopeTestRemainingChoices

variable {S T : Scheme.{0}} (f : T ⟶ S)

theorem pullback_prod_hom_ext {X Y : Over S} {W : Over T}
    {u v : W ⟶ (Over.pullback f).obj (X ⊗ Y)}
    (h₁ : u ≫ (Over.pullback f).map (fst X Y) = v ≫ (Over.pullback f).map (fst X Y))
    (h₂ : u ≫ (Over.pullback f).map (snd X Y) = v ≫ (Over.pullback f).map (snd X Y)) : u = v :=
  BinaryFan.IsLimit.hom_ext ((isLimitMapConeBinaryFanEquiv (Over.pullback f) _ _)
    (isLimitOfPreserves (Over.pullback f) (tensorProductIsBinaryProduct X Y))) h₁ h₂

theorem pullback_map_one {X G : Over S} [MonObj G] :
    (Over.pullback f).map (1 : X ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, Functor.map_comp]
  change _ = toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[G]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (Functor.OplaxMonoidal.η (Over.pullback f))]
  exact toUnit_unique _ _

end SlopeTestRemainingChoices

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section Torus

variable {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂]

theorem torusHomOf_iff_appTop' (h : X₂ → X₁) (t : splitTorus S X₁ ⟶ splitTorus S X₂) : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X₂ χ).val = (charUnit S X₁ (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) : Γ((splitTorus S X₁).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X₂ χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {h : X₂ → X₁} {t t' : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht,
    (torusHomOf_iff_appTop' _ _).1 ht']

theorem eq_one_of_torusHomOf_zero {t : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf (fun _ => (0 : X₁)) t) : t = 1 := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective ?_
  rw [map_one]
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  have k : ∀ χ : X₂, (GlobalTheory.splitTorusPointsEquiv S X₂ _ t (Multiplicative.ofAdd χ)).val =
      (charUnit S X₁ 0).val := fun χ => by
    rw [GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht]
  rw [k χ, ← k 0, ofAdd_zero, map_one]
  rfl

theorem torusHomOf_torusMap (q : X₂ →+ X₁) : TorusHomOf q (GlobalTheory.SplitTorusPow.torusMap S q) :=
  (torusHomOf_iff_appTop' _ _).2 fun χ => GlobalTheory.SplitTorusPow.torusMap_char q χ

end Torus

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem IsProdUnif.linHom_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → LinHom U₁ U i₁ q₁ (lift (𝟙 G₁) 1) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₁ hi₁ hi₂
  have h1 : IsMonHom (1 : G₁ ⟶ G₂) := inferInstanceAs (IsMonHom (toUnit G₁ ≫ η[G₂]))
  have hi₂' : i₁ ≫ p₂ = 1 := hi₂.trans Hom.one_def.symm
  have hlim := hD.lim
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  ·
    have := (U₂.gt e).q_hom
    rw [← cancel_mono ((Over.pullback (thick R I e)).map (lift p₁ p₂))]
    refine pullback_prod_hom_ext _ ?_ ?_
    · simp only [Category.assoc, ← Functor.map_comp, lift_fst]
      rw [hU.q_pr₁ e, ← Category.assoc, ← Functor.map_comp, lift_fst, hi₁, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, ← Functor.map_comp, lift_snd]
      rw [hU.q_pr₂ e, ← Category.assoc, ← Functor.map_comp, lift_snd, hi₂', pullback_map_one,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]
  ·
    have := (U₂.gt e).i_hom
    let E := Equiv.ofBijective _ hD.xsum
    let j₁ : D₁.toPre.X → D.toPre.X := fun y => E.symm (y, 0)
    let j₂ : D₂.toPre.X → D.toPre.X := fun y => E.symm (0, y)
    have hj₁ : ∀ y, q₁ (j₁ y) = y ∧ q₂ (j₁ y) = 0 := fun y => by
      have := E.apply_symm_apply (y, 0)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    have hj₂ : ∀ y, q₁ (j₂ y) = 0 ∧ q₂ (j₂ y) = y := fun y => by
      have := E.apply_symm_apply (0, y)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    obtain ⟨t₁, ht₁, hf⟩ := hU.i_pr₁ e j₁ (fun y => (hj₁ y).1) (fun y => (hj₁ y).2)
    obtain ⟨t₂, ht₂, hs⟩ := hU.i_pr₂ e j₂ (fun y => (hj₂ y).1) (fun y => (hj₂ y).2)
    let t := GlobalTheory.SplitTorusPow.torusMap (Sp (R ⧸ I ^ (e + 1))) q₁
    have ht : TorusHomOf q₁ t := torusHomOf_torusMap q₁
    have e₁ : t ≫ t₁ = 𝟙 _ := by
      have k := ht.comp ht₁
      simp only [fun y => (hj₁ y).1] at k
      exact torusHomOf_unique k (TorusHomOf.id _)
    have e₂ : t ≫ t₂ = 1 := by
      have k := ht.comp ht₂
      simp only [fun y => (hj₂ y).1] at k
      exact eq_one_of_torusHomOf_zero k
    refine ⟨t, ht, pullback_prod_hom_ext _ ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id, hf,
        ← Category.assoc, e₁, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_snd, hs, ← Category.assoc, e₂,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.MumProd
