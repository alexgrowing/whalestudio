import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGoodReductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitAlmostEverywhereFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConditionsOfEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitConditionsOfEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerIndexNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedDoubleCosetsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartInProdStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonsplitPlacePairEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalElementIntegralAlmostAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyOfSectionPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionMeetsAbovePlaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCharpolySeparableOfEllipticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceLocalElementStatement

noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypProof

theorem transport_loc : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := @GlobalTheory.T.local_conditions_of_equiv

theorem transport_unit : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → UnitConds θ' K' (e d) f' → UnitConds θ K d f := @GlobalTheory.T.unit_conditions_of_equiv

theorem split_index : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G) (d : G) (f : G → ℂ),
  Continuous θ → IsCompact (K : Set G) → IsOpen (K' : Set G) → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) →
  ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0 := @GlobalTheory.T.stabilizer_index_ne_zero

theorem split_fin : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H) (K : Subgroup H) (d d' : H) (f : H × H → ℂ)
  (C₁ C₂ : Set H), Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  IsCompact C₁ → IsCompact C₂ → (∀ y, f y ≠ 0 → y.1 ∈ C₁ ∧ y.2 ∈ C₂) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  {q : DoubleCoset.Quotient (twCent (swTw σ) (d, d') : Set (H × H)) (K.prod K : Set (H × H)) |
    ∃ k ∈ K.prod K, f ((Quotient.out q * k)⁻¹ * (d, d') * swTw σ (Quotient.out q * k)) ≠ 0}.Finite := @GlobalTheory.T.finite_twisted_double_cosets

theorem split_cpt : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d') → ∀ y : H × H,
  twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (swTw σ) (d, d')) ∧
    (twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (swTw σ) (d, d'))) ≠ 0 := @GlobalTheory.T.swap_twist_compact_part_le

theorem split_unit : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → d ∈ K → d' ∈ K →
  cptPart (twCent (MonoidHom.id H) (d * σ d')) ≤ K →
  (∀ g : H, g⁻¹ * (d * σ d') * MonoidHom.id H g ∈ K → ∃ t ∈ twCent (MonoidHom.id H) (d * σ d'), t⁻¹ * g ∈ K) →
  cptPart (twCent (swTw σ) (d, d')) ≤ K.prod K ∧
    ∀ y : H × H, y⁻¹ * (d, d') * swTw σ y ∈ K.prod K → ∃ t ∈ twCent (swTw σ) (d, d'), ∃ k ∈ K.prod K, y = t * k := @GlobalTheory.T.swap_twist_compact_part_in_prod

theorem inert_iso : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), ¬ IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* (GLw a w.1 × GLw b w.1), (∀ y, e y = evw w y) ∧
    (∀ y, e (thv a b v y) = ((thL a w.1).prodMap (thL b w.1)) (e y)) ∧ ∀ y, y ∈ Kv a b v ↔ e y ∈ K2 a b w.1 := @GlobalTheory.T.nonsplit_place_pair_equiv

theorem split_iso : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* ((GLw a w.1 × GLw b w.1) × (GLw a w.1 × GLw b w.1)), (∀ y, (e y).1 = evw w y) ∧
    (∀ y, e (thv a b v y) = swTw (sgP a b w.1) (e y)) ∧ (∀ y, y ∈ Kv a b v ↔ e y ∈ (K2 a b w.1).prod (K2 a b w.1)) ∧
    ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), e (pv a b v (ratF E a δ₁, ratF E b δ₂)) =
      ((ratW a w.1 δ₁, ratW b w.1 δ₂),
        (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
         ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂))) := @GlobalTheory.T.aux_statement_22

theorem sg_facts : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
  Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧ ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := @GlobalTheory.T.pair_involution_continuous

theorem rat_mem : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E), ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w n := @GlobalTheory.T.rational_element_integral_almost_all

theorem cofinite_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ P : PlF E → Prop,
  (∀ᶠ w : {w : Pl E // w ∈ S} in cofinite, P (w.1.under (𝓞 (maximalRealSubfield E)))) → ∀ᶠ v in cofinite, P v := @GlobalTheory.T.eventually_of_section_places

theorem exists_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ v : PlF E, ∃ w : Above v, w.1 ∈ S := @GlobalTheory.T.section_meets_above_place

theorem sep_locEl : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
  (nrmL n w (locEl n w δ)).val.charpoly.Separable := @GlobalTheory.T.norm_charpoly_separable_of_elliptic

theorem norm_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), IsSplitAt w →
  ratW n w δ * thetaGL n (RingHom.id _) (ratW n w (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ)) = locEl n w δ := @GlobalTheory.T.split_place_local_element

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem fv_eq {S : Set (Pl E)} (hS : IsSection S) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (v : PlF E) (w : Above v)
    (hw : w.1 ∈ S) (y : Yv a b v) :
    fv S φ₁ φ₂ v y = φ₁ w.1 (evw w y) * if IsSplitAt w.1 then φ₂ w.1 (evw w (thv a b v y)) else 1 := by
  unfold fv
  rw [finprod_eq_single _ w, finprod_eq_if, if_pos hw]
  intro u hu
  have hn : u.1 ∉ S := by
    intro h
    apply hu
    apply Subtype.ext
    obtain ⟨z, -, hz⟩ := hS w.1
    have e : u.1.under (𝓞 (maximalRealSubfield E)) = w.1.under (𝓞 (maximalRealSubfield E)) := u.2.trans w.2.symm
    exact (hz _ ⟨h, e⟩).trans (hz _ ⟨hw, rfl⟩).symm
  rw [finprod_eq_if, if_neg hn]

theorem evw_pv_rat (v : PlF E) (w : Above v) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    evw w (pv a b v (ratF E a δ₁, ratF E b δ₂)) = (ratW a w.1 δ₁, ratW b w.1 δ₂) := by
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_)) <;> rfl

theorem test_facts {φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h : IsTestP φ) :
    ∃ K' : ∀ w : Pl E, Subgroup (GLw a w × GLw b w), (∀ w, IsOpen (K' w : Set (GLw a w × GLw b w))) ∧ (∀ w, K' w ≤ K2 a b w) ∧
      (∀ w, IsHecke (K' w) (φ w)) ∧ ∀ᶠ w in cofinite, φ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  refine ⟨fun w => (K₁ w).prod (K₂ w), fun w => ?_, fun w => ?_, h₃.1, h₃.2⟩
  · rw [Subgroup.coe_prod]
    exact ((h₁.1 w).1).prod ((h₂.1 w).1)
  · exact Subgroup.prod_mono (h₁.1 w).2.1 (h₂.1 w).2.1

theorem locConds_inert (hC : CjEx) (hU : Unr E) {S : Set (Pl E)} (hS : IsSection S)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h₁ : IsTestP φ₁) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (he₁ : polE δ₁ ∈ Ell E a) (he₂ : polE δ₂ ∈ Ell E b) (v : PlF E) (w : Above v) (hw : w.1 ∈ S) (hns : ¬ IsSplitAt w.1) :
    LocConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
  obtain ⟨e, he, hθ, hK⟩ := inert_iso hC E a b v w hns
  refine transport_loc e _ ((thL a w.1).prodMap (thL b w.1)) _ (K2 a b w.1) _ _ (φ₁ w.1) hθ hK (fun x => ?_) ?_
  · rw [fv_eq hS φ₁ φ₂ v w hw, if_neg hns, mul_one, he]
  obtain ⟨K', hKo, hKle, hH, -⟩ := test_facts h₁
  have hloc : e (pv a b v (ratF E a δ₁, ratF E b δ₂)) = (locEl a w.1 δ₁, locEl b w.1 δ₂) := by
    rw [he, evw_pv_rat]
    simp only [locEl, if_neg hns, ratW]
  rw [hloc]
  have s₁ := sep_locEl hC E a w.1 δ₁ he₁
  have s₂ := sep_locEl hC E b w.1 δ₂ he₂
  have hG := GlobalTheory.T.local_good_reduction E hU a b w.1 (locEl a w.1 δ₁, locEl b w.1 δ₂) s₁ s₂
  have hL := GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w.1 (locEl a w.1 δ₁, locEl b w.1 δ₂) s₁ s₂
  obtain ⟨-, hKc⟩ := GlobalTheory.CompanionTheory.TwistOrbit.isOpen_isCompact_pair_integral_points (E := E) a b w.1
  refine ⟨hG.1, fun y => split_index _ _ (K' w.1) _ (φ₁ w.1) (GlobalTheory.CompanionTheory.TwistOrbit.continuous_thPair hU a b w.1) hKc (hKo _)
    (hH w.1).2 y, ?_, hG.2⟩
  refine (hL.1 _ (hH w.1).1).subset ?_
  rintro q ⟨k, hk, hq⟩
  exact ⟨k, hk, subset_tsupport _ hq⟩

theorem split_all {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K K₁ K₂ : Subgroup H)
    (d d' : H) (f₁ f₂ : H → ℂ) (hσc : Continuous σ) (hσ : ∀ g, σ (σ g) = g) (hσK : ∀ k ∈ K, σ k ∈ K)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) (hKo₁ : IsOpen (K₁ : Set H)) (hKo₂ : IsOpen (K₂ : Set H))
    (hH₁ : IsHecke K₁ f₁) (hH₂ : IsHecke K₂ f₂) (hG : PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d'))
    (hL : ∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
      ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) :
    LocConds (swTw σ) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) := by
  have hcomm : ∀ x ∈ twCent (swTw σ) (d, d'), ∀ y ∈ twCent (swTw σ) (d, d'), x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₁, e₁⟩ := (mem_twCent_swTw σ hσ d d' x).1 hx
    obtain ⟨y₁, e₂⟩ := (mem_twCent_swTw σ hσ d d' y).1 hy
    have c := hG.1 _ x₁ _ y₁
    refine Prod.ext c ?_
    show x.2 * y.2 = y.2 * x.2
    rw [e₁, e₂]
    have c' : σ x.1 * σ y.1 = σ y.1 * σ x.1 := by rw [← map_mul, c, map_mul]
    calc d' * σ x.1 * d'⁻¹ * (d' * σ y.1 * d'⁻¹) = d' * (σ x.1 * σ y.1) * d'⁻¹ := by group
      _ = d' * (σ y.1 * σ x.1) * d'⁻¹ := by rw [c']
      _ = _ := by group
  have hσc' : Continuous (swTw σ) := (hσc.comp continuous_snd).prodMk (hσc.comp continuous_fst)
  refine ⟨hcomm, ?_, ?_, split_cpt σ _ d d' hσc hσ hKo hKc hσK hG⟩
  · have hc2 : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
      rw [Subgroup.coe_prod]; exact hKc.prod hKc
    have ho2 : IsOpen ((K₁.prod (K₂.comap σ) : Subgroup (H × H)) : Set (H × H)) := by
      rw [Subgroup.coe_prod]; exact hKo₁.prod (hKo₂.preimage hσc)
    refine split_index (swTw σ) (K.prod K) (K₁.prod (K₂.comap σ)) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) hσc' hc2 ho2 ?_
    rintro ⟨k₁, k₂⟩ ⟨hk₁, hk₂⟩ ⟨x₁, x₂⟩
    have hk₂' : σ k₂ ∈ K₂ := hk₂
    constructor
    · show f₁ (k₁ * x₁) * f₂ (σ (k₂ * x₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(hH₁.2 k₁ hk₁ x₁).1, map_mul, (hH₂.2 _ hk₂' _).1]
    · show f₁ (x₁ * k₁) * f₂ (σ (x₂ * k₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(hH₁.2 k₁ hk₁ x₁).2, map_mul, (hH₂.2 _ hk₂' _).2]
  · refine split_fin σ K d d' (fun y => f₁ y.1 * f₂ (σ y.2)) (tsupport f₁) (σ '' tsupport f₂) hσc hσ hKo hKc hσK hH₁.1 (hH₂.1.image hσc) ?_ hL
    intro y hy
    have h1 : f₁ y.1 ≠ 0 := left_ne_zero_of_mul hy
    have h2 : f₂ (σ y.2) ≠ 0 := right_ne_zero_of_mul hy
    exact ⟨subset_tsupport _ h1, σ y.2, subset_tsupport _ h2, hσ _⟩

theorem locConds_split (hC : CjEx) (hU : Unr E) {S : Set (Pl E)} (hS : IsSection S)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (he₁ : polE δ₁ ∈ Ell E a) (he₂ : polE δ₂ ∈ Ell E b) (v : PlF E) (w : Above v) (hw : w.1 ∈ S) (hs : IsSplitAt w.1) :
    LocConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
  obtain ⟨e, he, hθ, hK, hr⟩ := split_iso hC E a b v w hs
  obtain ⟨hσc, hσ, hσK⟩ := sg_facts E a b w.1
  refine transport_loc e _ (swTw (sgP a b w.1)) _ ((K2 a b w.1).prod (K2 a b w.1)) _ _
    (fun y => φ₁ w.1 y.1 * φ₂ w.1 (sgP a b w.1 y.2)) hθ hK (fun x => ?_) ?_
  · rw [fv_eq hS φ₁ φ₂ v w hw, if_pos hs, ← he, ← he, hθ]
    rfl
  obtain ⟨K₁, hKo₁, -, hH₁, -⟩ := test_facts h₁
  obtain ⟨K₂, hKo₂, -, hH₂, -⟩ := test_facts h₂
  obtain ⟨hKo, hKc⟩ := GlobalTheory.CompanionTheory.TwistOrbit.isOpen_isCompact_pair_integral_points (E := E) a b w.1
  rw [hr]
  have hN : (ratW a w.1 δ₁, ratW b w.1 δ₂) * sgP a b w.1 (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
    ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂)) = (locEl a w.1 δ₁, locEl b w.1 δ₂) :=
    Prod.ext (norm_split E a w.1 δ₁ hs) (norm_split E b w.1 δ₂ hs)
  have s₁ := sep_locEl hC E a w.1 δ₁ he₁
  have s₂ := sep_locEl hC E b w.1 δ₂ he₂
  have hG := GlobalTheory.T.local_good_reduction E hU a b w.1 (locEl a w.1 δ₁, locEl b w.1 δ₂) s₁ s₂
  have hL := (GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w.1 (locEl a w.1 δ₁, locEl b w.1 δ₂) s₁ s₂).1
  have hid : (thL a w.1).prodMap (thL b w.1) = MonoidHom.id _ := by
    have e₁ : thL a w.1 = MonoidHom.id _ := by rw [thL, if_pos hs]
    have e₂ : thL b w.1 = MonoidHom.id _ := by rw [thL, if_pos hs]
    rw [e₁, e₂]
    rfl
  rw [hid, ← hN] at hG hL
  exact split_all _ _ (K₁ w.1) (K₂ w.1) _ _ _ _ hσc hσ hσK hKo hKc (hKo₁ _) (hKo₂ _) (hH₁ _) (hH₂ _) hG hL

theorem unitConds_inert (hC : CjEx) {S : Set (Pl E)} (hS : IsSection S)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (v : PlF E) (w : Above v)
    (hw : w.1 ∈ S) (hns : ¬ IsSplitAt w.1) (hφ : φ₁ w.1 = (K2 a b w.1 : Set (GLw a w.1 × GLw b w.1)).indicator 1)
    (hy : (locEl a w.1 δ₁, locEl b w.1 δ₂) ∈ K2 (E := E) a b w.1 ∧
      (∀ g : GLw a w.1 × GLw b w.1, g⁻¹ * (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) g ∈ K2 (E := E) a b w.1 →
        ∃ t ∈ twCent ((thL a w.1).prodMap (thL b w.1)) (locEl a w.1 δ₁, locEl b w.1 δ₂), t⁻¹ * g ∈ K2 (E := E) a b w.1) ∧
      cptPart (twCent ((thL a w.1).prodMap (thL b w.1)) (locEl a w.1 δ₁, locEl b w.1 δ₂)) ≤ K2 (E := E) a b w.1) :
    UnitConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
  obtain ⟨e, he, hθ, hK⟩ := inert_iso hC E a b v w hns
  refine transport_unit e _ ((thL a w.1).prodMap (thL b w.1)) _ (K2 a b w.1) _ _ (φ₁ w.1) hθ hK (fun x => ?_) ?_
  · rw [fv_eq hS φ₁ φ₂ v w hw, if_neg hns, mul_one, he]
  have hloc : e (pv a b v (ratF E a δ₁, ratF E b δ₂)) = (locEl a w.1 δ₁, locEl b w.1 δ₂) := by
    rw [he, evw_pv_rat]
    simp only [locEl, if_neg hns, ratW]
  rw [hloc]
  refine ⟨hφ, hy.1, hy.2.2, fun g hg => ?_⟩
  obtain ⟨t, ht, hk⟩ := hy.2.1 g hg
  exact ⟨t, ht, t⁻¹ * g, hk, by group⟩

theorem split_ind {H : Type} [Group H] (σ : H →* H) (K : Subgroup H) (hσ : ∀ g, σ (σ g) = g) (hσK : ∀ k ∈ K, σ k ∈ K)
    (f₁ f₂ : H → ℂ) (h₁ : f₁ = (K : Set H).indicator 1) (h₂ : f₂ = (K : Set H).indicator 1) :
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) = ((K.prod K : Subgroup (H × H)) : Set (H × H)).indicator 1 := by
  subst h₁ h₂
  funext y
  have e : σ y.2 ∈ K ↔ y.2 ∈ K := ⟨fun h => hσ y.2 ▸ hσK _ h, hσK _⟩
  by_cases c₁ : y.1 ∈ K <;> by_cases c₂ : y.2 ∈ K <;>
    simp [Set.indicator, Subgroup.mem_prod, c₁, c₂, e]

theorem unitConds_split (hC : CjEx) {S : Set (Pl E)} (hS : IsSection S)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (v : PlF E) (w : Above v)
    (hw : w.1 ∈ S) (hs : IsSplitAt w.1) (hφ₁ : φ₁ w.1 = (K2 a b w.1 : Set (GLw a w.1 × GLw b w.1)).indicator 1)
    (hφ₂ : φ₂ w.1 = (K2 a b w.1 : Set (GLw a w.1 × GLw b w.1)).indicator 1)
    (hd : (ratW a w.1 δ₁, ratW b w.1 δ₂) ∈ K2 (E := E) a b w.1)
    (hd' : (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
      ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂)) ∈ K2 (E := E) a b w.1)
    (hy : (∀ g : GLw a w.1 × GLw b w.1, g⁻¹ * (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) g ∈ K2 (E := E) a b w.1 →
        ∃ t ∈ twCent ((thL a w.1).prodMap (thL b w.1)) (locEl a w.1 δ₁, locEl b w.1 δ₂), t⁻¹ * g ∈ K2 (E := E) a b w.1) ∧
      cptPart (twCent ((thL a w.1).prodMap (thL b w.1)) (locEl a w.1 δ₁, locEl b w.1 δ₂)) ≤ K2 (E := E) a b w.1) :
    UnitConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
  obtain ⟨e, he, hθ, hK, hr⟩ := split_iso hC E a b v w hs
  obtain ⟨hσc, hσ, hσK⟩ := sg_facts E a b w.1
  refine transport_unit e _ (swTw (sgP a b w.1)) _ ((K2 a b w.1).prod (K2 a b w.1)) _ _
    (fun y => φ₁ w.1 y.1 * φ₂ w.1 (sgP a b w.1 y.2)) hθ hK (fun x => ?_) ?_
  · rw [fv_eq hS φ₁ φ₂ v w hw, if_pos hs, ← he, ← he, hθ]
    rfl
  rw [hr]
  have hN : (ratW a w.1 δ₁, ratW b w.1 δ₂) * sgP a b w.1 (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
    ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂)) = (locEl a w.1 δ₁, locEl b w.1 δ₂) :=
    Prod.ext (norm_split E a w.1 δ₁ hs) (norm_split E b w.1 δ₂ hs)
  have hid : (thL a w.1).prodMap (thL b w.1) = MonoidHom.id _ := by
    have e₁ : thL a w.1 = MonoidHom.id _ := by rw [thL, if_pos hs]
    have e₂ : thL b w.1 = MonoidHom.id _ := by rw [thL, if_pos hs]
    rw [e₁, e₂]
    rfl
  rw [hid, ← hN] at hy
  obtain ⟨hc, hp⟩ := split_unit (sgP a b w.1) (K2 a b w.1) _ _ hσc hσ hσK hd hd' hy.2 hy.1
  exact ⟨split_ind _ _ hσ hσK _ _ hφ₁ hφ₂, ⟨hd, hd'⟩, hc, hp⟩

theorem locHyp : PositivityTheory.Rg.BcB.G8.Fin.LocHyp := by
  intro hC E _ _ _ hU a b S hS φ₁ φ₂ h₁ h₂ δ₁ δ₂ he₁ he₂
  have hloc : ∀ v : PlF E, LocConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
    intro v
    obtain ⟨w, hw⟩ := exists_above E S hS v
    by_cases hs : IsSplitAt w.1
    · exact locConds_split hC hU hS h₁ h₂ δ₁ δ₂ he₁ he₂ v w hw hs
    · exact locConds_inert hC hU hS h₁ δ₁ δ₂ he₁ he₂ v w hw hs
  have hunit : ∀ᶠ v : PlF E in cofinite,
      UnitConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
    refine cofinite_sec E S hS _ ?_
    have hinj : Tendsto (Subtype.val : {w : Pl E // w ∈ S} → Pl E) cofinite cofinite :=
      Function.Injective.tendsto_cofinite Subtype.val_injective
    obtain ⟨-, -, -, -, t₁⟩ := test_facts h₁
    obtain ⟨-, -, -, -, t₂⟩ := test_facts h₂
    have c₁ := rat_mem E a δ₁
    have c₂ := rat_mem E b δ₂
    have c₃ := rat_mem E a (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁)
    have c₄ := rat_mem E b (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂)
    filter_upwards [hinj.eventually t₁, hinj.eventually t₂, hinj.eventually c₁, hinj.eventually c₂, hinj.eventually c₃,
      hinj.eventually c₄, GlobalTheory.T.unit_almost_everywhere_facts E hU a b S hS δ₁ δ₂ he₁ he₂] with w r₁ r₂ m₁ m₂ m₃ m₄ hy
    have hy' := hy _ rfl
    by_cases hs : IsSplitAt w.1
    · exact unitConds_split hC hS δ₁ δ₂ _ ⟨w.1, rfl⟩ w.2 hs r₁ r₂ ⟨m₁, m₂⟩ ⟨m₃, m₄⟩ hy'.2
    · exact unitConds_inert hC hS δ₁ δ₂ _ ⟨w.1, rfl⟩ w.2 hs r₁ hy'
  exact ⟨fun v => (hloc v).1, fun v y => (hloc v).2.1 y, fun v => (hloc v).2.2.1, fun v y => (hloc v).2.2.2 y, hunit⟩

end GlobalTheory.CompanionTheory.LocHypProof

end
