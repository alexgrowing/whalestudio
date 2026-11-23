import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFrames
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocalModelSystemTransitionSiegelClausesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelAmpleModelOfSemistableReductionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.N3OfN2OneModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FourthClauseHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDedFracLocalizationAwayStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInclusionLocalizationReflexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelInclusionLevelChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseModelLevelChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

open GlobalTheory.ZM
open GlobalTheory.Toroidal GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef IsLocalRing

namespace GlobalTheory.CoverFin

open GlobalTheory.RaisedAmple

theorem ampAt_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.TorRef.AmpAt Y (n ^ k) := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N k T hN l₀ l B c O _ β Y hn hodd ⟨e, he⟩ hu hd hβ hR ⟨A⟩
  have hNpos : 0 < N := he ▸ pow_pos hn.pos e
  let l' : Level H := { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos hNpos }
  have d : l.Dvd l' := ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩
  have hNA : N ∣ l'.A := Nat.dvd_lcm_right _ _
  obtain ⟨c', hc⟩ := exists_coeff c l'
  have hkfin : (IntermediateField.inclusion hc).toRingHom.Finite := by
    have := c'.fin
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℚ c.F) ?_
    rw [Subsingleton.elim (RingHom.comp _ _) (algebraMap ℚ c'.F)]
    exact RingHom.finite_algebraMap.2 this
  obtain ⟨O', _, β', b, hβ', hb, hfin, hint⟩ := exists_closure β _ hβ hkfin
  obtain ⟨Y', r, ν, a, hl, hf, hs⟩ := exists_cover L₁ L₂ L₃ hN Y b d hc hβ hβ' hb hfin
  obtain ⟨b₁, r₁, ν₁, hb₁, hl₁, ⟨a₁⟩⟩ := hR
  have hbb : ∀ x, (c'.F.val.toRingHom.comp β') (b x) = (c.F.val.toRingHom.comp β) x := fun x =>
    congrArg Subtype.val (RingHom.congr_fun hb x)
  obtain ⟨ν₂, hν₂⟩ := LevelCover.sab_comp ν ν₁ rfl
  have hR' : Raises B Y' := ⟨b.comp b₁, r ≫ r₁, ν₂, fun x => (hbb _).trans (hb₁ x), levComp_comp hd d hl hl₁ ν₂ hν₂,
    ⟨(GlobalTheory.Models.above_comp E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C (ofModel Y) (ofModel Y') b₁ b r₁ ν₁ r ν ν₂
      a₁ a hν₂).choose⟩⟩
  have hi : Function.Injective (c'.F.val.toRingHom.comp β') := by
    letI := β'.toAlgebra
    have := hβ'.2.2
    exact Subtype.val_injective.comp (IsFractionRing.injective O' c'.F)
  obtain ⟨z, hz⟩ : ∃ z : RZ H n N →+* O', IsInc (RZ H n N).subtype (c'.F.val.toRingHom.comp β') z := by
    refine exists_isInc_of_mem _ hi
      ⟨b (b₁ ⟨(1 + H.rt0) / 2, Subring.subset_closure (by simp)⟩), (hbb _).trans (hb₁ _)⟩ ?_ ?_
    · obtain ⟨u, hu⟩ := hu.exists_right_inv
      refine ⟨b u, eq_inv_of_mul_eq_one_right ?_⟩
      rw [← map_natCast ((c'.F.val.toRingHom.comp β').comp b)]
      exact (map_mul ((c'.F.val.toRingHom.comp β').comp b) _ _).symm.trans (by rw [hu, map_one])
    · have hz : zeta N ∈ c'.F := by
        obtain ⟨m, hm⟩ := hNA
        have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => l'.A_pos.ne' (by rw [hm, h, mul_zero])
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
        have : zeta N = zeta l'.A ^ m := by
          rw [zeta, zeta, ← Complex.exp_nat_mul, hm]
          congr 1
          push_cast
          field_simp
        rw [this]
        exact pow_mem (c'.le (baseKA l').ζ.2) m
      obtain ⟨y, hy⟩ := hint ⟨zeta N, hz⟩
        ((isIntegral_algHom_iff c'.F.val.toRingHom.toIntAlgHom Subtype.val_injective).1 (isIntegral_zeta hNpos))
      exact ⟨y, congrArg Subtype.val hy⟩
  obtain ⟨g, hg, mu, -, hgf, -⟩ := GlobalTheory.AbelianLocusMap.exists_map_top L₁ L₂ L₃ hN B Y' z
    ⟨hd.1, hd.2.1, hd.2.2.trans d.2.2⟩ hNA hβ' hz hR'
  have haff : IsAffineHom g := by
    have : IsAffineHom (spMap z) := inferInstance
    have : IsAffineHom (pullback.fst T.s (spMap z)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
    rw [← pullback.lift_fst g Y'.s hg]
    infer_instance
  obtain ⟨A', -⟩ := GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom E H _ _ T.t Y'.t g mu _ A haff
  exact ⟨Y'.X, a.π, Y'.t, a.mu, hf, hs, ⟨A'⟩⟩

theorem coverSt_fin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ (s : Sys Xo) (M : Finset ℕ), (∀ m ∈ M, 1 ≤ m) ∧
      ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p),
        ∃ (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F) (b : ∀ i, 𝓞 c.F →+* R i)
          (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model (Xo l) c (ω i)),
          IsCover (algebraMap (𝓞 c.F) c.F) R a b ω ∧ (∀ i, ∃ m ∈ M, AmpAt (C i) m) ∧
          ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b₀ : 𝓞 c.F →+* c.V W),
            (∀ x, ((b₀ x : c.V W) : c.F) = (x : c.F)) →
            ∃ (i : I) (b' : R i →+* c.V W), b'.comp (b i) = b₀ ∧ (c.V W).subtype.comp b' = ω i ∧
              Dominates (C i) (s.Y p W hp hW ⟨l, c, hg p hp⟩) b' := by
  intro E _ _ _ H D hD Xo
  obtain ⟨L₁, L₂, L₃, -, -, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  have hH : GlobalTheory.LN.HomExtSt := GlobalTheory.homExtension_semiAbelian_dvr
  have hlev : ToroidalLevelCompatibility (H := H) (D := D) := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H D hD).1
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel hH L₁ L₂ L₃ (GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField) E H D Xo hD hlev
  choose kx hkx using hS
  have hAmp : ∀ p W hp hW (i : Idx H p), GlobalTheory.LN.Amp (S.Y p W hp hW i) := by
    intro p W hp hW i
    obtain ⟨l₀, hl, hR⟩ := S.raises p W hp hW i
    have haux := S.aux (S.ch p)
    obtain ⟨hded, hunit, -⟩ := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
    exact GlobalTheory.T.raised_model_finite_cover_ample_frames L₁ L₂ L₃ E H D Xo _ _ (kx (S.ch p)) (S.T (S.ch p)) hlev l₀ i.l _ _ _ _ _ haux.1 haux.2.1 ⟨_, rfl⟩
      (hunit _ ((Nat.coprime_primes haux.1 hp).2 (S.ch_ne p)))
      ((GlobalTheory.Models.primeToPart_spec E H p hp).2.1 _ _ hl).1 hded hR (hkx (S.ch p))
  refine ⟨⟨S.Y, fun p W hp hW => ⟨GlobalTheory.T.localModelSystem_transition_siegel_clauses hH L₁ L₂ L₃ E H D Xo hD hlev S p W hp hW, fun i => ?_⟩⟩,
    Finset.univ.image (fun i : Bool => S.n i ^ kx i), ?_, ?_⟩
  · have h2 := GlobalTheory.T.localModel_oneModel_and_splitFibres hH L₁ L₂ L₃ E H D Xo hD hlev S p W hp hW i
    exact ⟨h2.2, GlobalTheory.model_uniformisation_unconditional E H D _ _ _ _ _ p h2.1,
      GlobalTheory.LN.fourth_clause_holds E H D _ _ _ _ _ p h2.1 (hAmp p W hp hW i)⟩
  · intro m hm
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (S.aux i).1.ne_zero)
  intro l c hg
  let P := {l₀ : Level H // ∃ p : ℕ, p.Prime ∧ IsPrimeToPart l₀ l p}
  have : Finite P := GlobalTheory.GlobalModel.finite_parts l
  have hP : ∀ x : P, x.1.A = 1 ∧ x.1.Dvd l := fun x => by
    obtain ⟨p, hp, h⟩ := x.2
    exact ⟨h.1, ((GlobalTheory.Models.primeToPart_spec E H p hp).2.1 l x.1 h).1⟩
  let a : Bool × P → ℕ := fun i => S.n i.1 * i.2.1.M
  have ha : ∀ i, 0 < a i := fun i => Nat.mul_pos (S.aux _).1.pos (lt_of_lt_of_le (by norm_num) i.2.1.three_le)
  obtain ⟨hdO, -, -, hV⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  have hne : ∀ i, algebraMap (𝓞 c.F) c.F (a i : 𝓞 c.F) ≠ 0 := fun i => by
    rw [map_natCast]; exact Nat.cast_ne_zero.mpr (ha i).ne'
  let R : Bool × P → Type := fun i => Localization.Away (a i : 𝓞 c.F)
  let ω : ∀ i, R i →+* c.F := fun i => IsLocalization.Away.lift (a i : 𝓞 c.F) (isUnit_iff_ne_zero.mpr (hne i))
  have hωc : ∀ i, (ω i).comp (algebraMap (𝓞 c.F) (R i)) = algebraMap (𝓞 c.F) c.F := fun i =>
    IsLocalization.Away.lift_comp _ _
  have hωd : ∀ i, IsDedFrac (ω i) := fun i => GlobalTheory.T.isDedFrac_localization_away _ _ _ _ (hne i) hdO _ (hωc i)
  choose bR hbR using fun i => GlobalTheory.T.exists_inclusion_localization_reflex E H l c (a i) (ha i) (ω i) (hωc i)
  let B : ∀ i : Bool × P, BaseModel (S.T i.1) i.2.1 := fun i => S.B i.1 i.2.1 (hP i.2).1
  choose C k r ν hr hk hlv hA using fun i : Bool × P => GlobalTheory.T.model_inclusion_level_change L₁ L₂ L₃ E H D Xo _ _ (S.T i.1) hlev
    i.2.1 l (B i) c (R i) (ω i) (bR i) (S.aux i.1).1.pos (hP i.2).2 (hωd i) (hbR i)
  refine ⟨Bool × P, inferInstance, R, fun _ => inferInstance, fun i => (a i : 𝓞 c.F), fun i => algebraMap _ _, ω, C,
    ⟨hdO, fun i => ⟨hωd i, hωc i, ?_⟩, ?_⟩, fun i => ?_, ?_⟩
  · convert (Localization.isLocalization : IsLocalization.Away (a i : 𝓞 c.F) (Localization.Away (a i : 𝓞 c.F)))
    all_goals first | rfl | exact Algebra.algebra_ext (R := 𝓞 c.F) (A := Localization.Away (a i : 𝓞 c.F)) _ _ fun _ => rfl
  · exact GlobalTheory.GlobalModel.span_natCast_eq_top a fun p hp => by
      obtain ⟨l₀, h⟩ := (GlobalTheory.Models.primeToPart_spec E H p hp).1 l (hg p hp)
      refine ⟨(S.ch p, ⟨l₀, p, hp, h⟩), ?_⟩
      have hc : (S.n (S.ch p) * l₀.M).Coprime p := Nat.Coprime.mul_left
        ((Nat.coprime_primes (S.aux _).1 hp).mpr (S.ch_ne p)) ((GlobalTheory.Models.primeToPart_spec E H p hp).2.1 l l₀ h).2.1
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hc.symm
  · have hu : IsUnit ((S.n i.1 : ℕ) : R i) := by
      have h₁ : IsUnit (algebraMap (𝓞 c.F) (R i) (a i : 𝓞 c.F)) := IsLocalization.Away.algebraMap_isUnit _
      rw [map_natCast] at h₁
      simp only [a, Nat.cast_mul] at h₁
      exact isUnit_of_mul_isUnit_left h₁
    exact ⟨S.n i.1 ^ kx i.1, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ampAt_of_raises L₁ L₂ L₃ E H D Xo _ _ (kx i.1) (S.T i.1) hlev i.2.1 l (B i) c _ _ (C i) (S.aux i.1).1
      (S.aux i.1).2.1 ⟨_, rfl⟩ hu (hP i.2).2 (hωd i) ⟨bR i, r i, ν i, hbR i, hlv i, hA i⟩ (hkx i.1)⟩
  · intro p W hp hW b₀ hb₀
    obtain ⟨l₀, h, hR⟩ := S.raises p W hp hW ⟨l, c, hg p hp⟩
    let i : Bool × P := (S.ch p, ⟨l₀, p, hp, h⟩)
    obtain ⟨hdV, hunitV, -⟩ := hV p W hp hW
    have hc : (a i).Coprime p := Nat.Coprime.mul_left
      ((Nat.coprime_primes (S.aux _).1 hp).mpr (S.ch_ne p)) ((GlobalTheory.Models.primeToPart_spec E H p hp).2.1 l l₀ h).2.1
    have hu : IsUnit (b₀ (a i : 𝓞 c.F)) := by rw [map_natCast]; exact hunitV _ hc
    let b' : R i →+* c.V W := IsLocalization.Away.lift (a i : 𝓞 c.F) hu
    have hb' : (c.V W).subtype.comp b' = ω i := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (a i : 𝓞 c.F)) ?_
      rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, hωc]
      exact RingHom.ext hb₀
    refine ⟨i, b', IsLocalization.Away.lift_comp _ _, hb', ?_⟩
    obtain ⟨A⟩ := hA i
    exact GlobalTheory.T.base_model_level_change L₁ L₂ L₃ E H D Xo _ _ (S.T i.1) i.2.1 l (B i) c (R i) (c.V W) (ω i) (c.V W).subtype
      (bR i) (C i) _ b' (k i) (r i) (ν i) (hr i) (hk i) (hlv i) A (hωd i) hdV hb' hR

end GlobalTheory.CoverFin
