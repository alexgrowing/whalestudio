import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGroupSectionsDenseInFibresStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Cover

theorem comp_one_pt {S : Scheme.{0}} {G X Y : Over S} [GrpObj G] (f : X ⟶ Y) : f ≫ (1 : Y ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]

theorem exists_section_translate_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : G.left.Opens), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → ∀ x : G.left, ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, (𝟙 G * (toUnit G ≫ a)).left x ∈ O := by
  intro R _ _ _ hB G _ _ hG O hO x
  obtain ⟨hN, -, -, hC⟩ := hB
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have hGI : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth G.hom

  have hη : ∀ P : Sp R, (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left P ∈ O := by
    intro P
    have hc : G.hom ((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left (closedPoint R)) = closedPoint R := by
      change ((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R
      rw [Over.w]
      rfl
    exact ((IsLocalRing.specializes_closedPoint P).map (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left.continuous).mem_open
      O.2 (hO _ hc)
  by_cases hx : G.hom x = closedPoint R
  · refine ⟨η[G], ?_⟩
    have : toUnit G ≫ (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := (Hom.one_def).symm
    rw [this, _root_.mul_one]
    exact hO x hx

  haveI := hN
  let k := G.left.residueField x
  let xp : Sp k ⟶ G.left := G.left.fromSpecResidueField x
  let s : Sp k ⟶ Sp R := xp ≫ G.hom
  have hrange : Set.range xp = {x} := Scheme.range_fromSpecResidueField x
  have hxp : ∀ p, xp p = x := fun p => by
    have h : xp p ∈ Set.range xp := ⟨p, rfl⟩
    rw [hrange] at h
    exact h
  obtain ⟨p0⟩ : Nonempty (Sp k) := inferInstance
  have hs : closedPoint R ∉ Set.range s := by
    rintro ⟨p, hp⟩
    apply hx
    rw [← hp, ← hxp p]
    rfl
  have hirr : IrreducibleSpace (pullback G.hom s : Scheme.{0}) := by
    have : IsIntegral (pullback G.hom s) := hGI.geometrically_isIntegral s _ _ (IsPullback.of_hasPullback _ _)
    infer_instance
  let Sx : Over (Sp R) := Over.mk s
  let T : Over (Sp R) := Over.mk (pullback.snd G.hom s ≫ s)
  let X' : Sx ⟶ G := Over.homMk xp rfl
  let p1 : T ⟶ G := Over.homMk (pullback.snd G.hom s ≫ xp) (by simp [T, s])
  let p2 : T ⟶ G := Over.homMk (pullback.fst G.hom s) (by simp [T, pullback.condition])
  let m : T ⟶ G := p1 * p2
  let l : Sp k ⟶ pullback G.hom s := pullback.lift (X'⁻¹).left (𝟙 _) (by simpa [Sx] using Over.w (X'⁻¹))
  have hl1 : l ≫ pullback.fst G.hom s = (X'⁻¹).left := pullback.lift_fst _ _ _
  have hl2 : l ≫ pullback.snd G.hom s = 𝟙 _ := pullback.lift_snd _ _ _
  let σ : Sx ⟶ T := Over.homMk l (by
    change l ≫ pullback.snd G.hom s ≫ s = s
    rw [reassoc_of% hl2])
  have hσ : σ ≫ m = 1 := by
    have e1 : σ ≫ p1 = X' := by
      ext
      change l ≫ pullback.snd G.hom s ≫ xp = xp
      rw [reassoc_of% hl2]
    have e2 : σ ≫ p2 = X'⁻¹ := by
      ext
      exact hl1
    rw [comp_mul, e1, e2, _root_.mul_inv_cancel]
  have hne : ((m.left ⁻¹ᵁ O : (pullback G.hom s).Opens) : Set (pullback G.hom s : Scheme.{0})).Nonempty := by
    refine ⟨σ.left p0, ?_⟩
    change (σ.left ≫ m.left) p0 ∈ O
    rw [← Over.comp_left, hσ, Hom.one_def, Over.comp_left]
    exact hη _
  have he : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom = 𝟙 _ := (Over.w _).trans (by simp)
  obtain ⟨a, aΩ, ha, h1, h2, h3⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hC G ‹_› _ he k s hs hirr _ hne
  let A : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk a (ha.trans (by simp))
  let AΩ : Sx ⟶ T := Over.homMk aΩ (by simp [T, Sx, reassoc_of% h2])
  have f1 : AΩ ≫ p1 = X' := by ext; simp [AΩ, p1, X', reassoc_of% h2]
  have f2 : AΩ ≫ p2 = toUnit Sx ≫ A := by ext; simp [AΩ, p2, A, h1, Sx]
  have key : X' ≫ (𝟙 G * (toUnit G ≫ A)) = AΩ ≫ m := by
    rw [comp_mul, comp_mul, f1, f2, Category.comp_id, comp_toUnit_assoc]
  refine ⟨A, ?_⟩
  rw [← hxp p0]
  change (X' ≫ (𝟙 G * (toUnit G ≫ A))).left p0 ∈ O
  rw [key]
  exact h3 ⟨p0, rfl⟩

end GlobalTheory.Mum.Cover
