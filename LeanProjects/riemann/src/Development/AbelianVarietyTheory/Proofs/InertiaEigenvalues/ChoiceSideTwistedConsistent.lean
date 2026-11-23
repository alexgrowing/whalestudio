import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTopStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentComplexOfSubfieldCoeffLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientLatticeEqSmallCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenFieldFormsProportionalOfReadings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsTwistedDefiniteFormsRationalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteComplexFormsEqTwistComplexFormsFockModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelTwistCharacterMemCoefficientIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFormAtEvaluationVectorEqRealisationLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftTwistLevelFormEqUnitMulClassSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormsCentralTranslateIffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugationScaledCoordsIntegralFormsTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingCompatAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateFunctionAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixBaseOfFixingFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScaleTwistedPlaceCoefficientMapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsConjugateTwistsConjugateExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistViaEmbeddingGoodConjugateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitPrimeProductOfTwistedPlaceTupleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtensionComplexDataEmbeddingRestrictCoeffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralUnitOfIsUnitAwayFromLevelEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalRowSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingOkClassAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesCharacterInverseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralFormsEqSpanDedekindCoefRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeFockPolysSpanIntegralForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteFormReadingInjectiveLatticeIntegralFormsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem image_span {R V A : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup A] [Module ℂ A] (φ : R →+* ℂ)
    (O : Subring ℂ) (hO : O = φ.range) (f : V →+ A) (hf : ∀ r v, f (r • v) = φ r • f v) (s : Set V) :
    f '' (Submodule.span R s : Set V) = (Submodule.span O (f '' s) : Set A) := by
  subst hO
  refine Set.Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [hf]; exact Submodule.smul_mem _ (⟨φ r, r, rfl⟩ : φ.range) hx
  · induction hy using Submodule.span_induction with
    | mem x hx => exact Set.image_mono Submodule.subset_span hx
    | zero => exact ⟨0, zero_mem _, map_zero f⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, add_mem hx hy, map_add f x y⟩
    | smul r x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨_, r, rfl⟩ := r
      exact ⟨r • x, Submodule.smul_mem _ r hx, hf r x⟩

theorem span_span_sub {A : Type} [AddCommGroup A] [Module ℂ A] {O₁ O₂ : Subring ℂ} (h : O₁ ≤ O₂) (s : Set A) :
    Submodule.span O₂ (Submodule.span O₁ s : Set A) = Submodule.span O₂ s := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => ?_) (Submodule.span_mono Submodule.subset_span)
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_mem _ (⟨r.1, h r.2⟩ : O₂) hx

theorem isIntegral_of_root {ζ : ℂ} (h : IsRoot1 ζ) : IsIntegral ℤ ζ ∧ IsIntegral ℤ ζ⁻¹ ∧ ζ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one), IsIntegral.of_pow hn (by rw [inv_pow, h, inv_one]; exact isIntegral_one), ?_⟩
  rintro rfl
  rw [zero_pow hn.ne'] at h
  exact zero_ne_one h

theorem unitOff_conj {N : ℕ} {a ζ ξ : ℂ} (τ : ℂ ≃+* ℂ) (ha : UnitOff N a) (hζ : IsRoot1 ζ) (hξ : IsRoot1 ξ) :
    UnitOff N (ξ * ζ * (τ a)⁻¹) := by
  obtain ⟨h0, n, h1, h2⟩ := ha
  obtain ⟨z1, z2, z0⟩ := isIntegral_of_root hζ
  obtain ⟨x1, x2, x0⟩ := isIntegral_of_root hξ
  have k1 := h1.map (τ : ℂ →+* ℂ).toIntAlgHom
  have k2 := h2.map (τ : ℂ →+* ℂ).toIntAlgHom
  simp only [map_mul, map_pow, map_natCast, map_inv₀] at k1 k2
  have t0 : τ a ≠ 0 := by simpa using h0
  refine ⟨mul_ne_zero (mul_ne_zero x0 z0) (inv_ne_zero t0), n, ?_, ?_⟩
  · have e : (N : ℂ) ^ n * (ξ * ζ * (τ a)⁻¹) = ξ * ζ * ((N : ℂ) ^ n * (τ a)⁻¹) := by ring
    rw [e]
    exact (x1.mul z1).mul k2
  · have e : (N : ℂ) ^ n * (ξ * ζ * (τ a)⁻¹)⁻¹ = ξ⁻¹ * ζ⁻¹ * ((N : ℂ) ^ n * τ a) := by rw [mul_inv, mul_inv, inv_inv]; ring
    rw [e]
    exact (x2.mul z2).mul k1

variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}

theorem mem_ringOf (ι : KE c w →+* ℂ) {y : D.what₂.LL} (hy : IsIntegral ℤ y) : ι (c.embW w y) ∈ ringOf ι := by
  obtain ⟨p, pm, hp⟩ := hy
  have h := congrArg (c.embW w) hp
  rw [Polynomial.hom_eval₂, map_zero] at h
  have hi : IsIntegral (c.Oe w) (c.embW w y) := ⟨p.map (Int.castRingHom _), pm.map _, by
    rw [Polynomial.eval₂_map, ← h]
    congr 1
    exact RingHom.ext_int _ _⟩
  obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨o, congrArg ι ho⟩

theorem intLL_le {ι : KE c w →+* ℂ} (hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x) : intLL D ≤ ringOf ι := by
  rintro _ ⟨a, rfl⟩
  change D.what₂.embLL (a : D.what₂.LL) ∈ _
  rw [← hι]
  exact mem_ringOf ι a.isIntegral_coe

theorem coefRing_LL {O : Subring ℂ} (h : intLL D ≤ O) : IsCoefRing D.what₂.embLL (labLL D) O :=
  ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => h ⟨a, rfl⟩⟩

theorem coefficient_ring_of_integral_le {O : Subring ℂ} (h : intLL D ≤ O) : IsCoefRing (embLL0 D) (labLL0 D) O :=
  ⟨embLL0_labLL0, fun a => h ⟨⟨((a : D.LL0) : D.what₂.LL), a.isIntegral_coe.map D.LL0.val.toRingHom.toIntAlgHom⟩, rfl⟩⟩

theorem span_latT (j : ℕ) : Submodule.span (KE c w) (latT c w j : Set (Tgt c w j)) = ⊤ := by
  refine top_unique fun y _ => ?_
  induction y using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem (hx trivial) (hy trivial)
  | tmul a f =>
    have hf : f ∈ Submodule.span (FractionRing (D.ntw.Ok (c.twI w) (c.k' w)))
        (D.nexp.MtLat (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) : Set _) := by
      rw [D.nexp.MtLat_span]; trivial
    induction hf using Submodule.span_induction generalizing a with
    | mem f hf =>
      have e : (a ⊗ₜ f : Tgt c w j) = a • ((1 : KE c w) ⊗ₜ f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e]
      exact Submodule.smul_mem _ a (Submodule.subset_span (Submodule.subset_span ⟨f, hf, rfl⟩))
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [TensorProduct.tmul_add]; exact add_mem (hf a trivial) (hg a trivial)
    | smul r f _ hf =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := D.ntw.Ok (c.twI w) (c.k' w)) r
      have hq0 := nonZeroDivisors.ne_zero hq
      have hq1 : algebraMap _ (KE c w) q ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply _ (c.Oe w) (KE c w)]
        exact fun h => hq0 (c.Oe_inj w ((IsFractionRing.injective (c.Oe w) (KE c w) (h.trans (map_zero _).symm)).trans (map_zero _).symm))
      have e : (a ⊗ₜ ((algebraMap _ (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) p / algebraMap _ _ q) • f) : Tgt c w j) =
          (p • (a / algebraMap _ (KE c w) q)) ⊗ₜ f := by
        conv_lhs => rw [← div_mul_cancel₀ a hq1, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
        rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) q,
          ← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) p f, smul_smul,
          mul_div_cancel₀ _ (by simpa using hq0)]
      rw [e]
      exact hf _ trivial

theorem span_smul_latT (j : ℕ) (o : (c.Oe w)ˣ) :
    Submodule.span (c.Oe w) ((fun y => algebraMap (c.Oe w) (KE c w) o • y) '' (latT c w j : Set (Tgt c w j))) = latT c w j := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun y hy => Submodule.subset_span ⟨((o⁻¹ : (c.Oe w)ˣ) : c.Oe w) • y, Submodule.smul_mem _ _ hy, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    beta_reduce
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ hy
  · beta_reduce
    rw [algebraMap_smul, smul_smul, Units.mul_inv, one_smul]

variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}

theorem rdF_thPe (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (hok : TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w))
    (hr : ∀ f, ρ.sum (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (T.rdV (c.k' w) (c.Q w) (chr c w) f) ∈ Set.range (rdK rd hρ (c.k' w)))
    (y : Tgt c w (j.1 + 1)) :
    rdF rd hρ hε (NChoice.thPe D c w (j.1 + 1) y) = ρ.sum (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (rdE T hε y) := by
  have key : ∀ m, rdF rd hρ hε (((Algebra.linearMap (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w)).restrictScalars (D.ntw.O (c.twI w))).rTensor
      (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w)) m) = rdK rd hρ (c.k' w) m := fun m => by
    induction m using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul a f =>
      rw [LinearMap.rTensor_tmul, rdF_tmul, rdK_tmul, ← hε.apply]
      rfl
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a f =>
    have e : (a ⊗ₜ f : Tgt c w (j.1 + 1)) = a • ((1 : KE c w) ⊗ₜ f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [rdE_tmul, map_smul, e, map_smul, LinearMap.map_smulₛₗ, NChoice.thPe_one, key, T.thP_eq _ _ _ hok f (hr f)]

end GlobalTheory.PlaceRead

namespace GlobalTheory.PlaceRead

variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} {Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0} {S : NX.RatDat D.ntw}
  {YS : NX.NExpRealS X.R X.cG S} {Z : ExportTie YS X.geo.v₀} {c : NChoice D} {w : D.what₂.places.Pl} {j : Fin D.R.m}

theorem levJ_congr {S T : HSp D} (B : Base S T) {ψ ψ' : Twist D Circle} (h : ψ'.Q = ψ.Q) : B.levJ ψ' = B.levJ ψ := by
  obtain ⟨Q, a, b⟩ := ψ
  obtain ⟨Q', a', b'⟩ := ψ'
  dsimp only at h
  subst h
  rfl

theorem span_translate (H : AtPlace Y Z c w j) {ι : KE c w →+* ℂ} (hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x)
    {u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ} (hu : IsLow X j u) {κ : ℂ} (hκ : κ ≠ 0) (hs : IsScale X.R X.geo.v₀ (baseOf Z c w j) κ)
    {z : GA D (Vc D j)} (hz : IsCentAt j (X.R.Q (Y.tupT (D.what₂.muTw w))) z) :
    ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) : Set (Amb D j)) =
      Submodule.span (ringOf ι) ((fun x h => (κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))
        (h * finPt (Vc D j) z)) '' latS w (j.1 + 1)) := by
  have hB := Z.good.base (c.twI w) j (c.sd w)
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ι
  have hle := intLL_le hι
  obtain ⟨hN0, hNP, o, ho⟩ := GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple D X X0 Y S YS Z c w j H ι hι
  have hNi : ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : ℂ)⁻¹ ∈ ringOf ι := by
    refine ⟨((o⁻¹ : (c.Oe w)ˣ) : c.Oe w), ?_⟩
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← map_natCast (ι.comp (algebraMap (c.Oe w) (KE c w))), ← ho, ← map_mul, Units.inv_mul, map_one]
  have h1 : (baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) =
      Submodule.span (ringOf ι) ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) ''
        latS w (j.1 + 1)) := by
    have e1 : (baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) =
        (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (ringOf ι) (twVia Z.ρ ι) := by
      unfold Base.mtLat
      rw [funext (GlobalTheory.T.coefficient_lattice_eq_small_coefficient_field D _ _ _ hB _ hle)]
    have e2 := GlobalTheory.T.thetaSeriesIntegralForms_eq_span_dedekindCoefRing D _ _ _ hB _ hg ha _ D.what₂.embLL (labLL D) (𝓞 D.what₂.LL) (D.what₂.embLL.comp (algebraMap _ _))
      (D.what₂.embLL.injective.comp RingOfIntegers.coe_injective) (coefRing_LL le_rfl) (GlobalTheory.T.level_twist_character_mem_coefficientIntegers D X X0 Y S YS Z c w j H ι hι) _ hle
    have e3 := GlobalTheory.T.rational_lattice_fock_polys_span_integral_forms D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
    rw [e1, e2]
    exact (congrArg (fun M : Submodule (intLL D) (Amb D j) => Submodule.span (ringOf ι) (M : Set (Amb D j))) e3).trans
      (span_span_sub hle _)
  have hc := GlobalTheory.T.integral_forms_central_translate_iff D j _ hB (twVia Z.ρ ι) _ (embLL0 D) (labLL0 D) _ (coefficient_ring_of_integral_le hle) _ z hz _ hN0 hNP hNi
  let Tz : Amb D j →ₗ[ℂ] Amb D j := LinearMap.funLeft ℂ _ fun h => h * finPt (Vc D j) z
  have h2 := image_span (ringOf ι).subtype (ringOf ι) (Subring.range_subtype _).symm Tz.toAddMonoidHom
    (fun r v => Tz.map_smul (r : ℂ) v)
    ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1))
  rw [Set.image_image, ← h1] at h2
  refine Eq.trans (Set.Subset.antisymm (fun F hF => ?_) ?_) h2
  · have e : (fun h => (fun h => F (h * (finPt (Vc D j) z)⁻¹)) (h * finPt (Vc D j) z)) = F :=
      funext fun h => by beta_reduce; rw [mul_inv_cancel_right]
    exact ⟨fun h => F (h * (finPt (Vc D j) z)⁻¹), (hc _).2 (by rw [e]; exact hF), e⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact (hc F).1 hF

noncomputable def trOf (H : AtPlace Y Z c w j) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (κ : ℂ) (z : GA D (Vc D j)) :
    D.what₂.Mt (D.what₂.muTw w) (j.1 + 1) →ₗ[ℂ] Amb D j :=
  LinearMap.funLeft ℂ _ (fun h => h * finPt (Vc D j) z) ∘ₗ (κ⁻¹ • fockOf Y (used_of_tw H.tw) j u)

theorem trOf_apply (H : AtPlace Y Z c w j) (u κ z y h) :
    trOf H u κ z y h = κ⁻¹ • fockOf Y (used_of_tw H.tw) j u y (h * finPt (Vc D j) z) := rfl

theorem trOf_eq_zero (H : AtPlace Y Z c w j) {u κ z} (hκ : κ ≠ 0) (hinj : Function.Injective (fockOf Y (used_of_tw H.tw) j u)) (y)
    (hy : trOf H u κ z y = 0) : y = 0 := by
  refine hinj (Eq.trans (funext fun h => ?_) (map_zero _).symm)
  have := congrFun hy (h * (finPt (Vc D j) z)⁻¹)
  rw [trOf_apply, inv_mul_cancel_right] at this
  exact (smul_eq_zero.1 this).resolve_left (inv_ne_zero hκ)

theorem indep_conj {M A I : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A] (τ : ℂ ≃+* ℂ) (Φ : M →ₗ[ℂ] A)
    (C : A →ₛₗ[(τ : ℂ →+* ℂ)] A) (h : ∀ y, C (Φ y) = 0 → y = 0) {b : I → M} (hb : LinearIndependent ℂ b) :
    LinearIndependent ℂ fun k => C (Φ (b k)) := by
  refine linearIndependent_iff'.2 fun s g hg k hk => ?_
  have h1 : C (Φ (∑ i ∈ s, τ.symm (g i) • b i)) = 0 := by
    rw [map_sum, map_sum, ← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ]
    exact congrArg (· • _) (τ.apply_symm_apply _)
  simpa using linearIndependent_iff'.1 hb s _ (h _ h1) k hk

noncomputable def semiComp {L V M A : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
    [Module ℂ A] (τ : ℂ ≃+* ℂ) {σ : L →+* ℂ} (J : V →ₛₗ[σ] M) (Φ : M →ₗ[ℂ] A) (C : A →ₛₗ[(τ : ℂ →+* ℂ)] A) (σ' : L →+* ℂ)
    (h : ∀ r, τ (σ r) = σ' r) : V →ₛₗ[σ'] A where
  toFun x := C (Φ (J x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' r x := by
    rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ]
    exact congrArg (· • _) (h r)

theorem rescale_conj {A : Type} [AddCommGroup A] [Module ℂ A] (τ : ℂ ≃+* ℂ) {n : ℕ} {κ ν ζ a₀ : ℂ} (hκ : κ ≠ 0) (hν : ν ≠ 0)
    {g : Fin n → A} {a a' : Fin n → ℂ} (ha : ∀ k, τ (a k) = a' k) {s : A} (h : κ • s = ζ • ∑ k, τ (a₀⁻¹ * a k) • g k) :
    s = (ν / κ * ζ * (τ a₀)⁻¹) • ν⁻¹ • ∑ k, a' k • g k := by
  rw [← inv_smul_smul₀ hκ s, h]
  simp only [map_mul, map_inv₀, ha, mul_smul]
  rw [← Finset.smul_sum]
  simp only [smul_smul]
  congr 1
  field_simp

theorem expansion_eq (H : AtPlace Y Z c w j) {u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ} (hu : IsLow X j u) {κ : ℂ} (hκ : κ ≠ 0)
    {z : GA D (Vc D j)} {a₀ : ℂ} (ha₀ : a₀ ≠ 0) (L : Amb D j →ₗ[ℂ] (GA D (Wc D j) → ℂ)) {x} (hx : x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1))
    (hth : X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))
        (fun τ => (u τ : ↥((X.R.MW j (sg0 D X.A3.A)).sm τ))) =
      a₀ • L (fun h => fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x) (h * finPt (Vc D j) z)))
    {n : ℕ} {a : Fin n → D.what₂.LL} {f : Fin n → NX.FmK S (j.1 + 1)}
    (hf : (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
      Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) :
    κ • L (trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) =
      ∑ k, (a₀⁻¹ * D.what₂.embLL (a k)) • evW YS X.geo.v₀ j (f k).val := by
  have k1 := GlobalTheory.T.liftForm_at_evaluationVector_eq_realisationLift D X X0 Y S YS Z c w j H x hx
  have k0 : (fun τ => (u τ : ↥((X.R.MW j (sg0 D X.A3.A)).sm τ))) = X.geo.v₀ j (sg0 D X.A3.A) := funext hu
  have k3 : evW YS X.geo.v₀ j (∑ k, a k • (f k).val) = ∑ k, D.what₂.embLL (a k) • evW YS X.geo.v₀ j (f k).val := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => evW_smul YS X.geo.v₀ j _ _
  have k4 : evW YS X.geo.v₀ j (∑ k, a k • (f k).val) = _ :=
    (congrArg (fun y => (X.R.HW j (sg0 D X.A3.A)).e y (X.geo.v₀ j (sg0 D X.A3.A))) hf).trans (k1.trans (k0 ▸ hth))
  have k5 : κ • trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x) =
      fun h => fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x) (h * finPt (Vc D j) z) :=
    funext fun h => by rw [Pi.smul_apply, trOf_apply, smul_inv_smul₀ hκ]
  rw [← map_smul, k5]
  simp only [mul_smul]
  rw [← Finset.smul_sum, ← k3, k4, inv_smul_smul₀ ha₀]

theorem span_conj (H : AtPlace Y Z c w j) {ι ε : KE c w →+* ℂ} (hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x) {τ : ℂ ≃+* ℂ}
    (hιε : (τ : ℂ →+* ℂ).comp ι = ε) {u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ} (hu : IsLow X j u) {κ : ℂ} (hκ : κ ≠ 0)
    (hs : IsScale X.R X.geo.v₀ (baseOf Z c w j) κ) {z : GA D (Vc D j)} (hz : IsCentAt j (X.R.Q (Y.tupT (D.what₂.muTw w))) z)
    (C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j) (M : Set (Amb D j))
    (hC : C '' ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) : Set (Amb D j)) = M) :
    M = Submodule.span (ringOf ε) ((fun x => C (trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) '' latS w (j.1 + 1)) := by
  have e1 : (ringOf ι).map (τ : ℂ →+* ℂ) = ringOf ε := by
    rw [← hιε, ringOf, ringOf, RingHom.map_range, RingHom.comp_assoc]
  have e3 := image_span ((τ : ℂ →+* ℂ).comp (ringOf ι).subtype) (ringOf ε)
    (by rw [← RingHom.map_range, Subring.range_subtype, e1]) C.toAddMonoidHom (fun r v => C.map_smulₛₗ (r : ℂ) v)
    ((fun x => trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1))
  rw [Set.image_image] at e3
  rw [← hC, span_translate H hι hu hκ hs hz]
  exact e3

theorem exists_read (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : PrN) (H : AtPlace Y Z c w j) {ε : KE c w →+* ℂ} (hε : Extends Z.ρ ε) :
    ∃ (Ψ : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[ε.comp (c.embW w)] Amb D j) (N : ℕ) (z₁ : ℂ),
      (∀ (I : Type) (b : I → D.what₂.MtL (D.what₂.muTw w) (j.1 + 1)),
        LinearIndependent ℂ (fun k => D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (b k)) → LinearIndependent ℂ fun k => Ψ (b k)) ∧
      ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia Z.ρ ε) : Set (Amb D j)) =
        Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)) ∧
      IsUnit (N : c.Oe w) ∧ UnitOff N z₁ ∧
      ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
        (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
          Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
        (baseOf Z c w j).classSum (Z.ρ.om (c.twI w) j (c.sd w) (twVia Z.ρ ε).chi) (twVia Z.ρ ε)
          (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) (Ψ x) =
          z₁ • (Z.ν (c.twI w) j (c.sd w))⁻¹ • ∑ k, ε (c.embW w (a k)) • evW YS X.geo.v₀ j (f k).val := by
  obtain ⟨τ, hτ0⟩ := GlobalTheory.BigOn.Exp.TwConj.exists_aut_on D.what₂.embLL (ε.comp (c.embW w))
    (GlobalTheory.BigOn.Exp.TwConj.countable_alg D.what₂.embLL)
  have hτ : ∀ x, τ (D.what₂.embLL x) = ε (c.embW w x) := fun x =>
    hτ0 x ((Algebra.IsAlgebraic.isAlgebraic x).algHom D.what₂.embLL.toRatAlgHom)
  have hfix : ∀ a, τ (embLL0 D a) = embLL0 D a := fun a => (hτ a).trans (H.emb ε hε a)
  obtain ⟨ι, hιε⟩ : ∃ ι : KE c w →+* ℂ, (τ : ℂ →+* ℂ).comp ι = ε :=
    ⟨(τ.symm : ℂ →+* ℂ).comp ε, RingHom.ext fun y => τ.apply_symm_apply _⟩
  have hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x := fun x => τ.injective ((RingHom.congr_fun hιε _).trans (hτ x).symm)
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo : BaseOf X.R.toRealDat j (baseOf Z c w j) :=
    GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  obtain ⟨hg, ha, hcc⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ι
  obtain ⟨hg', ha', -⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ε
  have hcj : ConjChar τ (twVia Z.ρ ι) (twVia Z.ρ ε) := hιε ▸ hcc τ
  obtain ⟨u, cc, κ, hu, hc, hκ, hval, hfn, hs, hν⟩ := GlobalTheory.T.exists_scale_twisted_place_coefficient_map D X X0 Y S YS Z c w j H
  obtain ⟨hfb, hfd⟩ := GlobalTheory.T.fix_base_of_fixing_field hP D X X0 Y S YS Z c w j H τ hfix
  obtain ⟨C, hC1, hC2⟩ := GlobalTheory.T.conjugation_scaled_coords_integral_forms_twist D j _ hB hBo.lam (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ hκ hval hfn τ hfix _ _ hg hg' hcj hfd
  have hω := Z.good.weil (c.twI w) j (c.sd w) _ hg
  have hω' := Z.good.weil (c.twI w) j (c.sd w) _ hg'
  have hcl' := Z.good.classes (c.twI w) j (c.sd w) _ hg' ha'
  have hcl : IsClassSystem (Vc D j) ((baseOf Z c w j).levJ (twVia Z.ρ ι)) (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) := by
    rw [← levJ_congr (baseOf Z c w j) hcj.1]
    exact hcl'
  refine (GlobalTheory.T.thetaLift_twistLevelForm_eq_unit_mul_classSum D X j _ hB hBo _ _ hg ha (H.tup ι hι) _ hω _ _ hcl u).elim fun z hz => hz.elim fun a₀ hz => ?_
  obtain ⟨hz, ha₀, hth⟩ := hz
  refine (GlobalTheory.T.classSums_conjugate_twists_conjugate_expansions D X j _ hB _ _ hg hg' ha (GlobalTheory.T.embedding_compat_at_place hCo hCW hHM hP D X X0 Y S YS Z c w j H ι hι τ hfix _ hg' hcj) u cc κ hu hc hκ τ hfb hfd
    hcj _ _ hω hω').elim fun ζ hζ => ?_
  obtain ⟨hζ, hcs⟩ := hζ
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u hu
  have hmem : ∀ y, fockOf Y (used_of_tw H.tw) j u y ∈ (baseOf Z c w j).formsC (twVia Z.ρ ι) := fun y =>
    hrange.le (LinearMap.mem_range_self _ y)
  have hΦv : ∀ y h, trOf H u κ z y h ∈ (baseOf Z c w j).valSpace := fun y h =>
    Submodule.smul_mem _ κ⁻¹ (((baseOf Z c w j).mem_formsC.1 (hmem y)).1 _)
  have hN := (GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple D X X0 Y S YS Z c w j H ι hι).2.2
  refine ⟨semiComp τ (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1)) (trOf H u κ z) C (ε.comp (c.embW w)) hτ, _, _, fun I b hb => ?_, ?_, hN, unitOff_conj τ ha₀ hζ hν, fun x hx n a f hf => ?_⟩
  · exact indep_conj τ (trOf H u κ z) C (fun y hy => trOf_eq_zero H hκ hinj y ((hC1 _ (hΦv y)).2 hy)) hb
  · have e1 : (ringOf ι).map (τ : ℂ →+* ℂ) = ringOf ε := by
      rw [← hιε, ringOf, ringOf, RingHom.map_range, RingHom.comp_assoc]
    have e2 := hC2 _ (coefficient_ring_of_integral_le (intLL_le hι))
    rw [e1] at e2
    exact span_conj H hι hιε hu hκ hs hz C _ e2
  · have h1 := expansion_eq H hu hκ ha₀.1 _ hx (hth _ (hmem (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) hf
    have h2 := GlobalTheory.T.conjugate_function_at_place hP D X X0 Y S YS Z c w j H τ hfix ζ _ _
      (hcs _ _ hcl'.fin _ _ (hC1 _ (hΦv (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))).1) n _ f h1
    exact rescale_conj τ hκ (Z.scalar (c.twI w) j (c.sd w)).ne (fun k => hτ (a k)) h2

theorem exists_lift {L K V W A : Type} [Field L] [Field K] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module K W] [AddCommGroup A]
    [Module ℂ A] (φ : L →+* K) (ε : K →+* ℂ) (r : W →ₛₗ[ε] A) (hr : Function.Injective r) (Ψ : V →ₛₗ[ε.comp φ] A) {s : Set V}
    (hs : Submodule.span L s = ⊤) (h : ∀ x ∈ s, ∃ y, r y = Ψ x) : ∃ e : V →ₛₗ[φ] W, ∀ x, r (e x) = Ψ x := by
  have key : ∀ x, ∃ y, r y = Ψ x := fun x => by
    have hx : x ∈ Submodule.span L s := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx⟩ := hx
      obtain ⟨y', hy⟩ := hy
      exact ⟨x' + y', by rw [map_add, map_add, hx, hy]⟩
    | smul a x _ hx =>
      obtain ⟨x', hx⟩ := hx
      exact ⟨φ a • x', by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hx]; rfl⟩
  choose e he using key
  exact ⟨⟨⟨e, fun x y => hr (by rw [map_add, he, he, he, map_add])⟩,
    fun a x => hr (by
      change r (e (a • x)) = r (φ a • e x)
      rw [LinearMap.map_smulₛₗ, he, he, LinearMap.map_smulₛₗ]; rfl)⟩, he⟩

theorem indep_of_read {K W A I : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup A] [Module ℂ A] (ε : K →+* ℂ)
    (r : W →ₛₗ[ε] A) {b : I → W} (h : LinearIndependent ℂ fun k => r (b k)) : LinearIndependent K b := by
  refine linearIndependent_iff'.2 fun s g hg k hk => ?_
  have h1 : ∑ i ∈ s, ε (g i) • r (b i) = 0 := by
    rw [← map_zero r, ← hg, map_sum]
    exact Finset.sum_congr rfl fun i _ => (r.map_smulₛₗ _ _).symm
  simpa using linearIndependent_iff'.1 h s _ h1 k hk

theorem mem_span_basis {L K V W I : Type} [Field L] [Field K] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module K W]
    {φ : L →+* K} (e : V →ₛₗ[φ] W) (b : Module.Basis I L V) (x : V) : e x ∈ Submodule.span K (Set.range fun i => e (b i)) := by
  have hx : x ∈ Submodule.span L (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem place_of_at (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : PrN) (H : AtPlace Y Z c w j) :
    ∃ (e : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[c.embW w] Tgt c w (j.1 + 1)) (u : (FractionRing (c.Oe w))ˣ),
      BasisAt c w (j.1 + 1) e ∧ LatAt c w (j.1 + 1) e (u : FractionRing (c.Oe w)) ∧ ThetaAt Y YS c w j e (u : FractionRing (c.Oe w)) := by
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField D c w Z.ρ Z.good).1
  refine (exists_read hCo hCW hHM hP H hε).elim fun Ψ h => h.elim fun N h => h.elim fun z₁ h => ?_
  obtain ⟨hind, hlat, hN, hz, hth⟩ := h
  obtain ⟨hinj, hmt⟩ := GlobalTheory.T.definiteFormReading_injective_lattice_integralForms D c w Z.ρ Z.good j _ (Z.tie (c.twI w) j (c.sd w)) ε hε H.ok H.field.roots
  have hsub : ∀ F ∈ Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)), ∃ y ∈ latT c w (j.1 + 1),
      rdE (Z.tie (c.twI w) j (c.sd w)) hε y = F := fun F hF => (hmt F).1 (hlat.ge hF)
  obtain ⟨e, he⟩ := exists_lift (c.embW w) ε _ hinj Ψ (GlobalTheory.T.rationalLatticeTwistedTuple_span_top D w (j.1 + 1)) fun x hx =>
    (hsub _ (Submodule.subset_span ⟨x, hx, rfl⟩)).imp fun _ h => h.2
  have hL : Submodule.span (c.Oe w) (e '' latS w (j.1 + 1)) = latT c w (j.1 + 1) := by
    have h1 := image_span (ε.comp (algebraMap (c.Oe w) (KE c w))) (ringOf ε) rfl
      (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom
      (fun r v => (congrArg _ (algebraMap_smul (KE c w) r v).symm).trans ((rdE (Z.tie (c.twI w) j (c.sd w)) hε).map_smulₛₗ _ v)) (e '' latS w (j.1 + 1))
    have h2 : (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom '' (e '' latS w (j.1 + 1)) = Ψ '' latS w (j.1 + 1) := by
      rw [Set.image_image]
      exact Set.image_congr fun x _ => he x
    rw [h2] at h1
    refine le_antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨y', hy', e1⟩ := hsub _ (h1.le ⟨y, hy, rfl⟩)
      exact hinj e1 ▸ hy'
    · obtain ⟨y', hy', e1⟩ := h1.ge (hlat.le ((hmt _).2 ⟨y, hy, rfl⟩))
      exact hinj e1 ▸ hy'
  have hb : BasisAt c w (j.1 + 1) e := fun b => by
    refine ⟨indep_of_read ε (rdE (Z.tie (c.twI w) j (c.sd w)) hε) ?_, top_unique ?_⟩
    · simp only [he]
      exact hind _ b (D.what₂.jMt_basis _ _ b).1
    · rw [← span_latT, ← hL]
      refine Submodule.span_le.2 fun y hy => ?_
      refine (Submodule.span_le (p := (Submodule.span (KE c w) (Set.range fun i => e (b i))).restrictScalars (c.Oe w))).2 ?_ hy
      rintro _ ⟨x, -, rfl⟩
      exact mem_span_basis e b x
  have hfa : Faithful (Z.rd (c.twI w) j (c.sd w)) :=
    GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ X.R X.cG S YS X.geo.v₀ Z.ρ Z.good _ j _ _ (Z.scalar _ j _).ne X.unif
      X.char.models.HW (Z.vec j) H.ks
  have hrat := GlobalTheory.T.class_sums_twisted_definite_forms_rational D Z.ρ Z.good _ j _ _ (Z.tie (c.twI w) j (c.sd w)) (Z.rat H.rat).2.1 H.field.roots _ _ _ H.ok H.cls
  have key : ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
      (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
        Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
      rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (NChoice.thPe D c w (j.1 + 1) (e x)) =
        z₁ • rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
          (YS.eF (c.twI w) (j.1 + 1) (c.sd w) (Nat.le_add_left _ _) j.2).symm ((1 : NX.KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)) := by
    intro x hx n a f hf
    have h1 := hth x hx n a f hf
    rw [hε.twVia_eq] at h1
    refine (rdF_thPe _ hε H.ok hrat _).trans ((congrArg _ (he x)).trans (h1.trans (congrArg (z₁ • ·) ?_)))
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rdF_tmul, smul_comm]
    refine congrArg (ε (c.embW w (a k)) • ·) ?_
    refine Eq.trans ?_ (realRd_tmul YS X.geo.v₀ Z.good (c.twI w) j (c.sd w) _ 1 (f k)).symm
    rw [show Z.ρ.e (c.twI w) (c.sd w) (1 : NX.KB S (c.twI w) (c.sd w)) = 1 from map_one _, mul_one]
  have hco := fun x hx n a f hf => GlobalTheory.T.chosenField_forms_proportional_of_readings D c w Z.ρ Z.good j _ hfa ε hε _ _ z₁ (key x hx n a f hf)
  obtain ⟨o, ho⟩ : ∃ o : (c.Oe w)ˣ, ThetaAt Y YS c w j e (algebraMap (c.Oe w) (KE c w) o) := by
    by_cases hex : ∃ t : KE c w, ε t = z₁
    · obtain ⟨t, ht⟩ := hex
      obtain ⟨o, rfl⟩ := GlobalTheory.T.exists_integral_unit_of_isUnitAwayFromLevel_embedding (c.Oe w) ε N t hN (ht ▸ hz)
      refine ⟨o, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', e1⟩ := h1 hB
      exact e1.trans (congrArg (· • _) (ε.injective (ht'.trans ht.symm)))
    · refine ⟨1, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', -⟩ := h1 hB
      exact absurd ⟨t', ht'⟩ hex
  exact ⟨e, Units.map (algebraMap (c.Oe w) (KE c w)).toMonoidHom o, hb, hL.trans (span_smul_latT _ o).symm, ho⟩

end GlobalTheory.PlaceRead

namespace GlobalTheory.PlaceRead

open Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem exists_map_at_place : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∀ v, TwistedAt (Dof x) v → ∀ i : Fin (Dof x).R.m, ∃ (e : (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1)) (u : (FractionRing (ch.Oe v))ˣ), GlobalTheory.ChoiceRead.BasisAt ch v (i.1 + 1) e ∧ GlobalTheory.ChoiceRead.LatAt ch v (i.1 + 1) e (u : FractionRing (ch.Oe v)) ∧ GlobalTheory.ChoiceRead.ThetaAt x.r.Y l.b.YS ch v i e (u : FractionRing (ch.Oe v)) := by
  intro hCo hCW hHM hP hS hL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hF : StepW Start fun _ _ _ _ w => ∀ (Z : w.Lt) (X : RealSide (w.st Z).toD7), X.R.C = TC.cf w.I w.l Z → FieldOk X :=
    EvG.imp (GlobalTheory.TwInputs.SmallField.evLgG_fieldOk hP) fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp _ _ w _ Z => (H kp T w Z).1
  refine (((((GlobalTheory.T.rational_row_series hP hS hL).and (GlobalTheory.T.twisting_ok_class_at_place hP hL)).and (GlobalTheory.T.series_character_inverse hL)).and hF).and
    ((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev))).trans
    (StepW.of_all fun K B f T w hO _ H P x => ?_)
  intro l ch tp hxi hpsi hQ hk hside hok v hv i
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := H
  obtain ⟨hHo, -⟩ := h5 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := h6 (w.st x.o.Z) hO
  let X := RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo (Finite.of_injective _ (ixOf_injective w.I _)) hHo hStd hSize
  have hf : FieldOk X := h4 x.o.Z X x.m.z.lev.C
  obtain ⟨k1, k2⟩ := h2 P x l ch tp hxi hpsi hQ hk hside v hv (hok v hv)
  obtain ⟨k3, k4⟩ := h3 P x l
  obtain ⟨ψ0, -, k5, -⟩ := hside.nct.psi_eq
  exact place_of_at (X := X) (Y := x.r.Y) (YS := l.b.YS) (Z := l.b.ser.ex) hCo hCW hHM hP
    { pins := x.m.z.pins, intersectionNumber_baseChange := x.m.intersectionNumber_baseChange, field := hf, tw := hv, ok := hok v hv, cls := k1
      emb := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField _ ch v _ l.b.ser.ex.good).2 hside.nct
      val := fun σ => ⟨_, (k5 v σ).trans (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
      U_eq := k3, psi_eq := k4, ks := l.rat.In.ks _ (Nat.le_add_left _ _) i.2
      rat := h1 P x l _ (GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ ch hside.nct hf.galois v hv) i _
      tup := k2 i }

end GlobalTheory.PlaceRead
