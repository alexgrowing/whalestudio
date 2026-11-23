import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

theorem finite_of_isClosed_of_finite_inter_closedPoints {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {S : Set T} (hS : IsClosed S) (h : (S ∩ closedPoints T).Finite) :
    S.Finite := by
  have hc : IsClosed (S ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (S ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← JacobsonSpace.closure_inter_closedPoints hS, hc.closure_eq]
  exact h

theorem finite_pullback_over_closedPoint {X Z P : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] (s : X ⟶ Z) (t : P ⟶ Z) (σ : X) (hσ : IsClosed ({σ} : Set X))
    {F : Set P} (hF : F.Finite) :
    {w : ↑(pullback s t) | pullback.fst s t w = σ ∧ pullback.snd s t w ∈ F}.Finite := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hσ
  let i := X.fromSpecResidueField σ
  have h1 : LocallyOfFiniteType ((i ≫ s) ≫ specZIsTerminal.from Z) := by
    rw [specZIsTerminal.hom_ext ((i ≫ s) ≫ specZIsTerminal.from Z) (i ≫ π)]
    infer_instance
  have h2 : LocallyOfFiniteType (i ≫ s) := locallyOfFiniteType_of_comp _ (specZIsTerminal.from Z)
  have h3 : LocallyQuasiFinite (i ≫ s) :=
    .of_injective (Function.injective_of_subsingleton _)
  have h4 : QuasiCompact (i ≫ s) := ⟨fun U _ _ ↦ (Set.toFinite _).isCompact⟩
  have H := (IsPullback.of_hasPullback (pullback.fst s t) i).paste_horiz
    (IsPullback.of_hasPullback s t).flip
  have h5 : LocallyQuasiFinite (pullback.fst (pullback.fst s t) i ≫ pullback.snd s t) :=
    MorphismProperty.of_isPullback H.flip h3
  have h6 : QuasiCompact (pullback.fst (pullback.fst s t) i ≫ pullback.snd s t) :=
    MorphismProperty.of_isPullback H.flip h4
  refine (((pullback.fst (pullback.fst s t) i ≫ pullback.snd s t).finite_preimage hF).image
    (pullback.fst (pullback.fst s t) i)).subset ?_
  rintro w ⟨hw, hw'⟩
  have : w ∈ Set.range (pullback.fst (pullback.fst s t) i) := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    exact hw
  obtain ⟨v, rfl⟩ := this
  exact ⟨v, by simpa using hw', rfl⟩

theorem locallyQuasiFinite_of_finite_fibres_closedPoints {Y X : Scheme.{0}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {f y}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  refine subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_
  have : Finite (f.fiber (f y)) := (f.fiberHomeo (f y)).finite_iff.mpr (h y hy)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem existsUnique_extension_of_finite_specializations :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π], IsNormalScheme X → ∀ (Z P : Scheme.{0}) (s : X ⟶ Z) (t : P ⟶ Z) [IsProper t] (G : P.Opens) (U : X.Opens) (φ : U.toScheme ⟶ P), (U : Set X).Nonempty → φ ≫ t = U.ι ≫ s → (∀ σ : X, IsClosed ({σ} : Set X) → ∃ F : Set P, F.Finite ∧ F ⊆ G ∧ ∀ (p : ℕ) [Fact p.Prime] (a : Sp (OO p) ⟶ X) (a₀ : Sp (PadicAlgCl p) ⟶ U.toScheme) (b : Sp (OO p) ⟶ P), a (cPt p) = σ → a₀ ≫ U.ι = gPt p ≫ a → gPt p ≫ b = a₀ ≫ φ → b ≫ t = a ≫ s → b (cPt p) ∈ F) → ∃! Φ : X ⟶ G.toScheme, U.ι ≫ Φ ≫ G.ι = φ ∧ Φ ≫ G.ι ≫ t = s := by
  intro X _ π _ _ _ hX Z P s t _ G U φ hU hφ H
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : Nonempty U.toScheme := hU.to_subtype
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : QuasiCompact U.ι := inferInstance
  have : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]; exact U.isOpen.dense hU⟩
  let Γ := graphClosure s t U.ι φ hφ.symm
  let f : Γ ⟶ X := graphClosure.fst s t U.ι φ hφ.symm
  let g : Γ ⟶ P := graphClosure.snd s t U.ι φ hφ.symm
  let j : U.toScheme ⟶ Γ := graphClosure.incl s t U.ι φ hφ.symm
  have hjf : j ≫ f = U.ι := graphClosure.incl_fst ..
  have hjg : j ≫ g = φ := graphClosure.incl_snd ..
  have hfg : f ≫ s = g ≫ t := graphClosure.condition ..
  have : Flat (j ≫ f ≫ π) := by rw [reassoc_of% hjf]; infer_instance
  have : Flat (f ≫ π) := flat_of_schemeDominant_of_isDedekindDomain j _
  have : JacobsonSpace Γ := jacobsonSpace_of_locallyOfFiniteType_int (f ≫ π)
  choose F hF hFG hFH using H
  have hcl (z : Γ) (hz : IsClosed ({z} : Set Γ)) : IsClosed ({f z} : Set X) := by
    simpa using f.isClosedMap _ hz
  have key (z : Γ) (hz : IsClosed ({z} : Set Γ)) : g z ∈ F (f z) (hcl z hz) := by
    obtain ⟨p, hp, y, hy, hyU⟩ := padicAlgCl_integral_points.1 Γ (f ≫ π) z hz j.opensRange
      (Set.range_nonempty _)
    obtain ⟨l, e⟩ : ∃ l, l ≫ j = gPt p ≫ y := ⟨_, IsOpenImmersion.lift_fac j (gPt p ≫ y) hyU⟩
    have := hFH (f z) (hcl z hz) p (y ≫ f) l (y ≫ g)
      ((Scheme.Hom.comp_apply _ _ _).trans (congrArg f hy))
      (by rw [← reassoc_of% e, hjf]) (by rw [← reassoc_of% e, hjg]) (by simp [hfg])
    exact ((Scheme.Hom.comp_apply y g _).trans (congrArg g hy)) ▸ this
  have : LocallyQuasiFinite f := by
    refine locallyQuasiFinite_of_finite_fibres_closedPoints f fun y hy ↦ ?_
    refine finite_of_isClosed_of_finite_inter_closedPoints
      ((hcl y hy).preimage f.continuous) ?_
    refine ((finite_pullback_over_closedPoint π s t (f y) (hcl y hy) (hF _ (hcl y hy))).preimage
      (graphClosure.ι s t U.ι φ hφ.symm).isClosedEmbedding.injective.injOn).subset ?_
    rintro z ⟨hz, hz'⟩
    have hz₁ : f z = f y := hz
    have h₂ := key z hz'
    refine ⟨?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply]; exact hz₁
    · rw [← Scheme.Hom.comp_apply]
      have : ∀ (x : X) (hx : IsClosed ({x} : Set X)), f z = x → g z ∈ F x hx := by
        rintro _ _ rfl; exact h₂
      exact this _ _ hz₁
  have : IsIso f := isIso_of_isProper_of_quasiFinite_of_birational f (fun x ↦ (hX x).2) U ‹_›
  have hG : Set.range (inv f ≫ g) ⊆ Set.range G.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact subset_of_isOpen_of_closedPoints isOpen_univ (g ⁻¹ᵁ G).isOpen
      (fun z hz _ ↦ hFG _ _ (key z hz)) (Set.mem_univ _)
  have e := IsOpenImmersion.lift_fac G.ι (inv f ≫ g) hG
  have e' : U.ι ≫ inv f = j := by simp [hjf]
  refine ⟨IsOpenImmersion.lift G.ι (inv f ≫ g) hG, ⟨?_, ?_⟩, fun Φ hΦ ↦ ?_⟩
  · rw [e, reassoc_of% e', hjg]
  · rw [reassoc_of% e, ← hfg, IsIso.inv_hom_id_assoc]
  · rw [← cancel_mono G.ι, e]
    refine ext_of_isDominant_of_isSeparated t ?_ U.ι ?_
    · rw [Category.assoc, hΦ.2, Category.assoc, ← hfg, IsIso.inv_hom_id_assoc]
    · rw [hΦ.1, reassoc_of% e', hjg]

end GlobalTheory
