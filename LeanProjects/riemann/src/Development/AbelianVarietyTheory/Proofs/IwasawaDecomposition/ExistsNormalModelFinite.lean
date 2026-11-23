import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalFiniteModelOfFiniteOverOpen
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory

namespace GlobalTheory

theorem exists_normal_finite_model_of_finite_over_open_baseChange : ∀ (A R K : Type) [CommRing A] [CommRing R] [Field K] (κ : A →+* R) (ω : R →+* K) (S Z U : Scheme.{0}) (s : S ⟶ Sp A) (j : Z ⟶ S) [IsOpenImmersion j] (sZ : Z ⟶ Sp A) (cU : U ⟶ Sp K) (y : U ⟶ Z) (h : y ≫ sZ = cU ≫ spMap (ω.comp κ)), IsDedFrac ω → κ.Finite → IsProjOver s → j ≫ s = sZ → Geo.Tor.IsNormalScheme U → IsFinite (pullback.lift y cU h) → ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (sY : Y ⟶ Sp R) (jQ : U ⟶ pullback sY (spMap ω)), IsFinite π ∧ π ≫ s = sY ≫ spMap κ ∧ Geo.Tor.IsNormalScheme Y ∧ IsProjOver sY ∧ Flat sY ∧ jQ ≫ pullback.snd _ _ = cU ∧ jQ ≫ pullback.fst _ _ ≫ π = y ≫ j ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ x, x ∈ Set.range jQ ↔ π (pullback.fst sY (spMap ω) x) ∈ Set.range j := by
  intro A R K _ _ _ κ ω S Z U s j _ sZ cU y h hω hκ hs hjs hU hfin
  obtain ⟨⟨hD, hDed⟩, hchar, hfrac⟩ := hω
  letI : Algebra R K := ω.toAlgebra
  have hκf : IsFinite (spMap κ) := (IsFinite.SpecMap_iff _).2 hκ
  have hcomp : spMap (ω.comp κ) = spMap ω ≫ spMap κ := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hsR : IsProjOver (pullback.snd s (spMap κ)) := GlobalTheory.ProjSpace.isProjOver_pullback_snd κ hs
  have hbS : IsPullback (pullback.fst s (spMap κ)) (pullback.snd s (spMap κ)) s (spMap κ) := .of_hasPullback _ _
  have hbP : IsPullback (pullback.fst (pullback.snd s (spMap κ)) (spMap ω)) (pullback.snd _ _)
      (pullback.snd s (spMap κ)) (spMap ω) := .of_hasPullback _ _
  have hbig := hbP.paste_horiz hbS
  have hQ : IsPullback (pullback.fst sZ (spMap (ω.comp κ))) (pullback.snd sZ (spMap (ω.comp κ)))
      (j ≫ s) (spMap ω ≫ spMap κ) := by
    rw [hjs, ← hcomp]; exact .of_hasPullback _ _
  let e' := hbig.lift (pullback.fst sZ (spMap (ω.comp κ)) ≫ j) (pullback.snd sZ (spMap (ω.comp κ)))
    (by rw [Category.assoc]; exact hQ.w)
  have he₁ : e' ≫ pullback.fst _ _ ≫ pullback.fst s (spMap κ) = pullback.fst sZ (spMap (ω.comp κ)) ≫ j := by
    rw [← Category.assoc]; exact hbig.lift_fst _ _ _
  have he₂ : e' ≫ pullback.snd _ _ = pullback.snd sZ (spMap (ω.comp κ)) := hbig.lift_snd _ _ _
  have hsq : IsPullback (pullback.fst sZ (spMap (ω.comp κ))) e' j
      (pullback.fst _ _ ≫ pullback.fst s (spMap κ)) :=
    IsPullback.of_bot (by rw [he₂]; exact hQ) (by rw [he₁]) hbig
  have he' : IsOpenImmersion e' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq inferInstance
  let P := pullback (pullback.snd s (spMap κ)) (spMap ω)
  let W : P.Opens := e'.opensRange
  let φ := pullback.lift y cU h
  let fW : U ⟶ W.toScheme := φ ≫ e'.isoOpensRange.hom
  have hW : fW ≫ W.ι = φ ≫ e' := by simp [fW, W]
  have hf0 : (y ≫ j) ≫ s = (cU ≫ spMap ω) ≫ spMap κ := by
    rw [Category.assoc, hjs, h, Category.assoc, hcomp]
  let f : U ⟶ pullback s (spMap κ) := pullback.lift (y ≫ j) (cU ≫ spMap ω) hf0
  have hf : fW ≫ W.ι ≫ pullback.fst _ _ = f := by
    rw [← Category.assoc, hW]
    apply pullback.hom_ext
    · simp only [Category.assoc, f, pullback.lift_fst]
      rw [he₁, pullback.lift_fst_assoc]
    · simp only [Category.assoc, f, pullback.lift_snd]
      rw [pullback.condition, reassoc_of% he₂, pullback.lift_snd_assoc]
  have hc : fW ≫ W.ι ≫ pullback.snd _ _ = cU := by
    rw [← Category.assoc, hW, Category.assoc, he₂, pullback.lift_snd]
  have hfW : IsFinite fW := inferInstance
  obtain ⟨Y, π', jQ, hπ', hY, hproj, hflat, hjQ2, hjQ1, hopen, hdense, hlast⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open R K (pullback s (spMap κ)) U
      (pullback.snd s (spMap κ)) cU f W fW hsR hU hfW hf hc
  have hπ : IsFinite (π' ≫ pullback.fst s (spMap κ)) := inferInstance
  refine ⟨Y, π' ≫ pullback.fst s (spMap κ), π' ≫ pullback.snd s (spMap κ), jQ, hπ, ?_, hY, hproj, hflat,
    hjQ2, ?_, hopen, hdense, fun x ↦ ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition]
  · rw [reassoc_of% hjQ1, pullback.lift_fst]
  · rw [hlast x]
    let p : pullback (π' ≫ pullback.snd s (spMap κ)) (spMap ω) ⟶ P :=
      pullback.lift (pullback.fst _ _ ≫ π') (pullback.snd _ _) (by simpa using pullback.condition)
    have hp : p ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π' := pullback.lift_fst ..
    have hx : π' (pullback.fst (π' ≫ pullback.snd s (spMap κ)) (spMap ω) x) =
        pullback.fst (pullback.snd s (spMap κ)) (spMap ω) (p x) := by
      rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply]
    rw [Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply (pullback.fst _ _) (pullback.fst s (spMap κ))]
    constructor
    · rintro ⟨w, hw⟩
      have hinv : e'.isoOpensRange.inv ≫ e' = W.ι := (Iso.inv_comp_eq _).2 e'.isoOpensRange_hom_ι.symm
      have key : e'.isoOpensRange.inv ≫ pullback.fst sZ (spMap (ω.comp κ)) ≫ j =
          W.ι ≫ pullback.fst _ _ ≫ pullback.fst s (spMap κ) := by
        rw [← he₁, reassoc_of% hinv]
      refine ⟨(e'.isoOpensRange.inv ≫ pullback.fst sZ (spMap (ω.comp κ))) w, ?_⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, key, Scheme.Hom.comp_apply (pullback.fst _ _) (pullback.fst s (spMap κ)), ← hw]
      simp only [Scheme.Hom.comp_apply]
    · rintro ⟨v, hv⟩
      obtain ⟨q, hq1, hq2⟩ := Scheme.exists_preimage_of_isPullback hsq v (p x) hv
      refine ⟨e'.isoOpensRange.hom q, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.Hom.comp_apply, hq2]

end GlobalTheory
