import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverFieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightedProjectiveChartsSplitGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDenseClosedPointsChartSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.AbelianLocus

theorem isProper_of_eq {S G G₁ G₂ : Scheme.{0}} (f : G ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    {K₁ K₂ : Type} [Field K₁] [Field K₂] {t₁ : Sp K₁ ⟶ S} {t₂ : Sp K₂ ⟶ S}
    {φ₁ : G₁ ⟶ G} {f₁ : G₁ ⟶ Sp K₁} {φ₂ : G₂ ⟶ G} {f₂ : G₂ ⟶ Sp K₂}
    (h₁ : IsPullback φ₁ f₁ f t₁) (h₂ : IsPullback φ₂ f₂ f t₂) (p₁ : Sp K₁) (p₂ : Sp K₂) (hp : t₁ p₁ = t₂ p₂)
    [IsProper f₁] : IsProper f₂ := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t₁) (g := t₂) p₁ p₂ hp
  let j := (pullback t₁ t₂).fromSpecResidueField z
  let u := j ≫ pullback.fst t₁ t₂
  let u' := j ≫ pullback.snd t₁ t₂
  have e : u ≫ t₁ = u' ≫ t₂ := by simp only [u, u', Category.assoc, pullback.condition]
  have P₁ := (IsPullback.of_hasPullback f₁ u).paste_horiz h₁
  have P₂ := (IsPullback.of_hasPullback f₂ u').paste_horiz h₂
  rw [← e] at P₂
  have h₃ : UniversallyClosed (pullback.snd f₂ u') := by
    rw [← (P₂.isoIsPullback _ _ P₁).hom_inv_id_assoc (pullback.snd f₂ u'), P₂.isoIsPullback_inv_snd]
    infer_instance
  have : Subsingleton (Sp K₂) := inferInstanceAs (Subsingleton (PrimeSpectrum K₂))
  have hu' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u' :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed f₂ :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu' h₃
  have : IsSeparated f₂ := MorphismProperty.of_isPullback h₂ inferInstance
  have : LocallyOfFiniteType f₂ := MorphismProperty.of_isPullback h₂ inferInstance
  exact ⟨⟩

theorem mem_abLocus_iff {S G₁ : Scheme.{0}} (G : Over S) [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    {K : Type} [Field K] {t : Sp K ⟶ S} {φ : G₁ ⟶ G.left} {f : G₁ ⟶ Sp K} (h : IsPullback φ f G.hom t)
    (p : Sp K) : t p ∈ abLocus G ↔ IsProper f := by
  constructor
  · intro hp
    let K' := AlgebraicClosure K
    let u : Sp K' ⟶ Sp K := spMap (algebraMap K K')
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have q : Sp K' := (default : PrimeSpectrum K')
    have e : (u ≫ t) q = t p := congrArg (fun z => t z) (Subsingleton.elim (u q) p)
    have := hp K' (u ≫ t) ⟨q, e⟩
    exact isProper_of_eq G.hom (IsPullback.of_hasPullback G.hom (u ≫ t)) h q p e
  · rintro hf K' _ _ t' ⟨q, hq⟩
    exact isProper_of_eq G.hom h (IsPullback.of_hasPullback G.hom t') p q hq.symm

theorem isProper_iff_of_split (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom]
    [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) (hs : C.Split c) :
    IsProper H.hom ↔ d = 0 := by
  obtain ⟨hc, i, hi⟩ := hs
  obtain ⟨B, _, q, hB, hq, hf, hsu, ha, hp, -⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hi
  have := hi.hom
  constructor
  · intro hH
    have : Mono (η[B]) := ⟨fun a b _ => toUnit_unique _ _⟩
    have : Mono i := MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms _) hp.flip this
    have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mono K (Fin d → ℤ) H i hi.hom
    rcases d with _ | d
    · rfl
    · exact absurd (congrFun (Subsingleton.elim (0 : Fin (d + 1) → ℤ) 1) 0) zero_ne_one
  · rintro rfl
    have : Mono q := ⟨fun {Y} x y hxy => by
      have h1 : (x * y⁻¹) ≫ q = toUnit _ ≫ η[B] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
        rfl
      have h2 : hp.lift _ _ h1 = 1 := by
        apply (splitTorusPointsEquiv (Sp K) (Fin 0 → ℤ) Y).injective
        refine MonoidHom.ext fun a => ?_
        rw [Subsingleton.elim a 1, map_one, map_one]
      have h3 := hp.lift_fst _ _ h1
      rw [h2, MonObj.one_comp] at h3
      exact mul_inv_eq_one.1 h3.symm⟩
    have : Mono q.left := inferInstanceAs (Mono ((Over.forget _).map q))
    have := hB.proper
    have := hB.smooth
    have : LocallyOfFinitePresentation (q.left ≫ B.hom) := by rw [Over.w q]; infer_instance
    have : LocallyOfFiniteType (q.left ≫ B.hom) := inferInstance
    have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp _ B.hom
    have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
    have : LocallyOfFinitePresentation q.left := inferInstance
    have : IsOpenImmersion q.left := IsOpenImmersion.of_flat_of_mono _
    have : IsIso q.left := isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext q.left.surjective.range_eq)
    rw [← Over.w q]
    infer_instance

theorem isProper_snd {P Z : Scheme.{0}} (f : P ⟶ Z) [IsProper f] (G : P.Opens) (U : Z.Opens) (h : f ⁻¹ᵁ U ≤ G) :
    IsProper (pullback.snd (G.ι ≫ f) U.ι) := by
  have h₁ := IsPullback.of_hasPullback f U.ι
  have h₂ := IsPullback.of_hasPullback G.ι (pullback.fst f U.ι)
  have h₃ := h₂.paste_vert h₁
  have : IsIso (pullback.snd G.ι (pullback.fst f U.ι)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    refine Set.eq_univ_of_forall fun x => h ?_
    have : pullback.fst f U.ι x ∈ Set.range (pullback.fst f U.ι) := ⟨x, rfl⟩
    rwa [Scheme.Pullback.range_fst, Scheme.Opens.range_ι] at this
  rw [← h₃.isoPullback_inv_snd]
  infer_instance

theorem abLocus_eq : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → ∀ Zab : C.Z.Opens, (∀ w : C.P.left, IsClosed ({w} : Set C.P.left) → C.P.hom w ∈ Zab → w ∈ C.G) → (∀ z : C.Z, IsClosed ({z} : Set C.Z) → z ∉ Zab → z ∉ abLocus C.GG) → abLocus C.GG = Zab ∧ IsProper (pullback.snd C.GG.hom Zab.ι) := by
  intro C L hT hC Zab h₁ h₂
  let := L.grp
  have := L.comm
  obtain ⟨hsep, hlft, hqc, -⟩ := GlobalTheory.ZJ.core_basic C
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have := C.proper
  have := C.lft
  have hle : C.P.hom ⁻¹ᵁ Zab ≤ C.G := by
    have := (GlobalTheory.jacobson_closedPoints_tools_int C.P.left (C.P.hom ≫ C.π)).2.2.1 (C.P.hom ⁻¹ᵁ Zab)
      (C.P.hom ⁻¹ᵁ Zab ⊓ C.G) fun w hw => ⟨fun h => ⟨h, h₁ w hw h⟩, fun h => h.1⟩
    exact inf_eq_left.1 this.symm
  have hpr : IsProper (pullback.snd C.GG.hom Zab.ι) := isProper_snd C.P.hom C.G Zab hle
  refine ⟨Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_), hpr⟩
  · by_contra hzn
    obtain ⟨R, _, _, _, t, _, ht, Ch, d, c, Sg, hd, hs, hcl⟩ := GlobalTheory.T.exists_dense_closedPoints_chartSplitting C L hT hC z
    have : Smooth ((Over.pullback t).obj C.GG).hom := inferInstanceAs (Smooth (pullback.snd _ _))
    have : IsSeparated ((Over.pullback t).obj C.GG).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
    have : QuasiCompact ((Over.pullback t).obj C.GG).hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
    have key : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R)
        [IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom s)],
        Charts.Split (H := (Over.pullback s).obj ((Over.pullback t).obj C.GG))
          (Ch.pull (pullback.fst ((Over.pullback t).obj C.GG).hom s)) c → ∀ p, (t (s p) ∈ abLocus C.GG ↔ d = 0) := by
      intro K _ s _ hsp p
      have : Smooth ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (Smooth (pullback.snd _ _))
      have : IsSeparated ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (IsSeparated (pullback.snd _ _))
      have : QuasiCompact ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (QuasiCompact (pullback.snd _ _))
      rw [← isProper_iff_of_split K ((Over.pullback s).obj ((Over.pullback t).obj C.GG))
        (Ch.pull (pullback.fst ((Over.pullback t).obj C.GG).hom s)) c hsp]
      exact mem_abLocus_iff C.GG ((IsPullback.of_hasPullback (pullback.snd C.GG.hom t) s).paste_horiz
        (IsPullback.of_hasPullback C.GG.hom t)) p
    have : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom (Out.jK R)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    have hgen := GlobalTheory.T.weightedProjectiveCharts_split_generic_point R ((Over.pullback t).obj C.GG) Ch d c Sg hd hs
    have p₀ : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
    have hp₀ : Out.jK R p₀ = (⊥ : PrimeSpectrum R) := by
      have : p₀ = (⊥ : PrimeSpectrum (FractionRing R)) := Subsingleton.elim (α := PrimeSpectrum _) _ _
      subst this
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))
    have hd0 : d = 0 := (key _ _ hgen p₀).1 (by rw [hp₀, ht]; exact hz)
    have : Nonempty (Sp R) := ⟨(⊥ : PrimeSpectrum R)⟩
    obtain ⟨x, hx⟩ := hd.nonempty
    obtain ⟨K, _, s, _, hr, hsp⟩ := hs x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range s := hr ▸ rfl
    refine h₂ _ (hcl _ hx) (fun hm => hzn ?_) ((key K s hsp p).2 hd0)
    have hsz : (⊥ : PrimeSpectrum R) ⤳ s p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have := (hsz.map t.continuous).mem_open Zab.2 hm
    rwa [← ht]
  · rintro K _ _ t ⟨p, rfl⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have hr : Set.range t ⊆ Set.range Zab.ι := by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim q p]
      exact hz
    have P := (IsPullback.of_hasPullback (pullback.snd C.GG.hom Zab.ι) (IsOpenImmersion.lift Zab.ι t hr)).paste_horiz
      (IsPullback.of_hasPullback C.GG.hom Zab.ι)
    rw [IsOpenImmersion.lift_fac] at P
    rw [← P.isoPullback_inv_snd]
    infer_instance

end GlobalTheory.ZJ.AbelianLocus
