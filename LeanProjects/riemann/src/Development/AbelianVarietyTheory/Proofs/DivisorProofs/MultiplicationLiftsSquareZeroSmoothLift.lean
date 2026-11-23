import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RetractionLiftObstructionZeroOfLiftedSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairLiftsGlueToMorphismOfLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsNaturalOfObstructionOneZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeOneObstructionClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijectiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.MulLift

variable {S S' : Scheme.{0}}

theorem isPullback_tensor {A' B' : Over S'} {A B : Over S} {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsPullback f A'.hom A.hom b) (n : IsPullback g B'.hom B.hom b) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsPullback h (A' ⊗ B').hom (A ⊗ B).hom b := by
  have p : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  have p' : IsPullback (fst A' B').left (snd A' B').left A'.hom B'.hom := IsPullback.of_hasPullback _ _
  have q := p'.paste_horiz m
  rw [← h₁, ← n.w] at q
  have r := (IsPullback.of_right q h₂ p).paste_vert n
  rwa [Over.w, Over.w] at r

theorem smooth_tensor {X Y : Over S} (hX : Smooth X.hom) (hY : Smooth Y.hom) : Smooth (X ⊗ Y).hom := by
  haveI := hX
  haveI := hY
  rw [Over.tensorObj_hom, Limits.pullback.condition]
  infer_instance

theorem toUnit_left (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem lift_match {A : Over S'} {X : Over S} {i : A.left ⟶ X.left} {l : (A ⊗ A).left ⟶ (X ⊗ X).left}
    (hl₁ : l ≫ (fst X X).left = (fst A A).left ≫ i) (hl₂ : l ≫ (snd X X).left = (snd A A).left ≫ i)
    (u v : A ⟶ A) (U V : X ⟶ X) (hu : i ≫ U.left = u.left ≫ i) (hv : i ≫ V.left = v.left ≫ i) :
    i ≫ (lift U V).left = (lift u v).left ≫ l := by
  have p : IsPullback (fst X X).left (snd X X).left X.hom X.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [Category.assoc, ← Over.comp_left, lift_fst, hu, Category.assoc, hl₁, ← Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, hv, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left,
      lift_snd]

theorem one_match {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀} {A : Over (Sp R₀)} [GrpObj A]
    {X : Over (Sp R)} {i : A.left ⟶ X.left} (h : IsPullback i A.hom X.hom (spMap π)) {e : Sp R ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 _) (hie : (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A).left ≫ i = spMap π ≫ e) :
    i ≫ (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X)).left = (1 : A ⟶ A).left ≫ i := by
  have e₁ : (1 : 𝟙_ (Over (Sp R₀)) ⟶ A) = η[A] := by simp [Hom.one_def]
  change _ = (toUnit A ≫ η[A]).left ≫ i
  rw [Over.comp_left, Over.comp_left, toUnit_left, toUnit_left]
  change i ≫ X.hom ≫ e = (A.hom ≫ η[A].left) ≫ i
  rw [← Category.assoc i, h.w, Category.assoc, Category.assoc, ← e₁]
  exact congrArg (A.hom ≫ ·) hie.symm

end GlobalTheory.Obs.MulLift

namespace GlobalTheory.Obs

open MulLift in

theorem mul_lifts : FormSt → AxesVanishingExtendedDegOne → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left),
    IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom → ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left),
    l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∃ m : X ⊗ X ⟶ X, l ≫ m.left = (μ[A₀]).left ≫ i := by
  intro hF hAx R R₀ _ _ I hI π hπ hk A₀ _ g hab hg X i h hX e he hie l hl₁ hl₂
  have hl : IsPullback l (A₀ ⊗ A₀).hom (X ⊗ X).hom (spMap π) := isPullback_tensor h h hl₁ hl₂
  have hsm : Smooth (X ⊗ X).hom := smooth_tensor hX hX
  obtain ⟨S, ⟨P⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
  obtain ⟨S', ⟨P'⟩⟩ :=
    GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk (A₀ ⊗ A₀).left (A₀ ⊗ A₀).hom (X ⊗ X).left (X ⊗ X).hom l hl hsm
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.T.exists_squareZeroAugmentedAlgebra R R₀ I hI π hπ hk
  have hh : (μ[A₀]).left ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀) := overW μ[A₀]
  have hlift : ∀ T : (Pair (μ[A₀]).left)ᵒᵖ,
      ∃ ρ : (ofSys S).B ((pairPull hh).G.obj T) →ₐ[R] (pairPre S' (μ[A₀]).left).B T,
        ∀ b, (pairPre S' (μ[A₀]).left).p T (ρ b) = (pairPull hh).α T ((ofSys S).p _ b) := fun T ↦ by
    haveI := (ofSys S).smooth ((pairPull hh).G.obj T)
    exact GlobalTheory.T.exists_lift_hom_of_reduction_squareZero_smooth R R₀ I hI π hπ hk _ _ ((ofSys S).p _) ((ofSys S).semi _) ((ofSys S).surj _)
      ((ofSys S).ker _) _ _ ((pairPre S' (μ[A₀]).left).p T) ((pairPre S' (μ[A₀]).left).semi T)
      ((pairPre S' (μ[A₀]).left).surj T) ((pairPre S' (μ[A₀]).left).ker T) (coefHom (pairPull hh) T)
  choose l₀ hl₀ using hlift
  have hL : (ofSys S).IsLift (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ := hl₀
  obtain ⟨Pp, Fa, -⟩ := hF R₀ A₀ g hab hg
  have hu : (lift (𝟙 A₀) 1).left ≫ (μ[A₀]).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one, Over.id_left]
  have hu' : (lift 1 (𝟙 A₀)).left ≫ (μ[A₀]).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.one_mul, Over.id_left]
  have hob : ∀ w, (ofSys S).IsOb1 (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ α w 0 := by
    intro w
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_degreeOneObstructionClass R R₀ I hI π hπ hk R₁ α _ _ _ _ (ofSys S) (pairPre S' (μ[A₀]).left) (pairPull hh)
      l₀ (ofSys_isFun S) ((ofSys_isFun S').restrict _) hL w
    obtain ⟨⟨-, hsurj⟩, -⟩ := (GlobalTheory.T.cechPairRestrict_baseChange_bijective R₀ R₁ _ _ (A₀ ⊗ A₀).hom (μ[A₀]).left).1
    obtain ⟨c', rfl⟩ := hsurj c
    have ax₁ : IsExtendedPullbackDegOne R₁ (overW (lift (𝟙 A₀) 1)) c' 0 :=
      GlobalTheory.T.retractionLiftObstruction_zero_of_liftedSection R R₀ I hI π hπ hk R₁ α _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl S S' P P'
        (μ[A₀]).left hh (lift (𝟙 A₀) 1).left (overW _)
        (lift (𝟙 X) (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X))).left hu
        (Over.w _) (lift_match hl₁ hl₂ _ _ _ _ (by simp) (one_match h he hie)) l₀ hL w c' hc
    have ax₂ : IsExtendedPullbackDegOne R₁ (overW (lift 1 (𝟙 A₀))) c' 0 :=
      GlobalTheory.T.retractionLiftObstruction_zero_of_liftedSection R R₀ I hI π hπ hk R₁ α _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl S S' P P'
        (μ[A₀]).left hh (lift 1 (𝟙 A₀)).left (overW _)
        (lift (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X)) (𝟙 X)).left hu'
        (Over.w _) (lift_match hl₁ hl₂ _ _ _ _ (one_match h he hie) (by simp)) l₀ hL w c' hc
    have h0 : c' = 0 := hAx R₀ R₁ α.q α.sq A₀ g hab hg c' ax₁ ax₂
    subst h0
    simpa using hc
  obtain ⟨l', hL', hN'⟩ := GlobalTheory.T.lifts_natural_of_obstructionOne_zero R R₀ I hI π hπ hk R₁ α A₀.left A₀.hom Pp Fa _ _ (ofSys S)
    (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ hL hob
  obtain ⟨f, hfs, hfk⟩ := GlobalTheory.T.affinePairLifts_glue_to_morphism_of_lifts R R₀ I hI π hπ hk _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl
    S S' P P' (μ[A₀]).left hh l' hL' hN'
  exact ⟨Over.homMk f hfs, hfk⟩

end GlobalTheory.Obs
