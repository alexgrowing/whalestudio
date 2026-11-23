import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLettersHarmMemHHa
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTorsionFreeIntOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjLatUnimodBd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowestWeightVectorsAtRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonnegStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumerator
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumPairUniformLevelBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipThetaTranslateHalfLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelSeriesTranslateBoundedDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealRationalPointActsHarmonicSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelPointsTranslateMeanOfIntegralCombinatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFormsThetaShortSeriesIdentityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSupportedClassScalarMemValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleSecondSplittingCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverIsDictionaryFrameCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoreConstantsEqVacuumIdentityUpToPhaseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumIdentityConstantsCoverOfDominantPinsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicMapExtremalVectorEqPhaseSmulLettersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntegralFormsOfRationalAndLocalSpansStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDeterminantMulIntegralFormsRayClassCoverStatement

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

section Ring

variable {k : Type} [Field k] [NumberField k] {σ : k →+* ℂ} {la : HeightOneSpectrum (𝓞 k)} {O : Subring ℂ} {l : ℕ}

theorem val_le_of_integral (hl : ((l : ℕ) : 𝓞 k) ∈ la.asIdeal) {m : ℕ} (hm : Nat.Coprime m l) {x : k}
    (hx : IsIntegral ℤ ((m : k) * x)) : la.valuation k x ≤ 1 := by
  have h1 : la.valuation k ((m : k) * x) ≤ 1 := la.valuation_le_one (K := k) (⟨_, hx⟩ : 𝓞 k)
  rwa [map_mul, GlobalTheory.ScalarUnit.val_natCast la hl hm, one_mul] at h1

theorem mem_of_integral (hl : ((l : ℕ) : 𝓞 k) ∈ la.asIdeal) (hO : ValRing σ la O) {m : ℕ} (hm : Nat.Coprime m l) {z : ℂ}
    (hz : ∃ x, σ x = z) (hi : IsIntegral ℤ ((m : ℂ) * z)) : z ∈ O := by
  obtain ⟨x, rfl⟩ := hz
  refine hO x (val_le_of_integral hl hm ?_)
  rw [← isIntegral_algHom_iff σ.toIntAlgHom σ.injective]
  simpa using hi

theorem inv_mem_of_coprime (hl : ((l : ℕ) : 𝓞 k) ∈ la.asIdeal) (hO : ValRing σ la O) {m : ℕ} (hm : Nat.Coprime m l) :
    (m : ℂ)⁻¹ ∈ O := by
  have := hO (m : k)⁻¹ (by rw [map_inv₀, GlobalTheory.ScalarUnit.val_natCast la hl hm, inv_one])
  simpa using this

end Ring

theorem zeta_mem_range {k : IntermediateField ℚ ℂ} {M : ℕ} (hM : M ≠ 0) (h : zeta M ∈ k) (σ : k →+* ℂ) :
    ∃ x, σ x = zeta M := by
  have h0 : IsPrimitiveRoot (zeta M) M := Complex.isPrimitiveRoot_exp M hM
  have h1 : IsPrimitiveRoot (⟨zeta M, h⟩ : k) M :=
    IsPrimitiveRoot.of_map_of_injective (f := k.val.toRingHom) h0 Subtype.val_injective
  have h2 := h1.map_of_injective σ.injective
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨j, -, hj⟩ := h2.eq_pow_of_pow_eq_one h0.pow_eq_one
  exact ⟨⟨zeta M, h⟩ ^ j, by rw [map_pow, hj]⟩

theorem bddAll_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {la : HeightOneSpectrum (𝓞 c.F)} {κ n : ℤ} {f : Rul Xo c}
    (h : GlobalTheory.GoodPts.BddAll Xo c la (κ : c.F) f) (hd : κ ∣ n) : GlobalTheory.GoodPts.BddAll Xo c la 1 ((n : c.F) • f) := by
  obtain ⟨j, rfl⟩ := hd
  intro T io e ho y hy
  have := mul_mem (intCast_mem (algebraMap T.V T.Fr).range j) (h T io e ho y hy)
  rw [map_one, one_mul, evI_smul, Int.cast_mul, map_mul, map_intCast io j, mul_comm (io _), mul_assoc]
  exact this

theorem exists_denom {X ι : Type} [AddCommGroup X] [Module ℂ X] (J : X →ₗ[ℂ] MvPolynomial ι ℂ) (Lat : Submodule ℤ X)
    (hL : Lat.FG) (l : ℕ) (hl : l.Prime) : ∃ c : ℕ, ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ)
      (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O →
      (∀ v ∈ Lat, ∀ mo, ∃ x, σ x = (J v).coeff mo) → ∀ v ∈ Lat, ∀ mo, ((l : ℂ) ^ c • J v).coeff mo ∈ O := by
  have one : ∀ z : ℂ, ∃ c : ℕ, IsAlgebraic ℤ z → ∃ m : ℕ, Nat.Coprime m l ∧ IsIntegral ℤ ((m : ℂ) * ((l : ℂ) ^ c * z)) := by
    intro z
    by_cases hz : IsAlgebraic ℤ z
    · obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
      obtain ⟨c, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hy0) l hl.ne_one
      refine ⟨c, fun _ => ⟨m, ((Nat.Prime.coprime_iff_not_dvd hl).2 hm).symm, ?_⟩⟩
      have e2 : (m : ℂ) * ((l : ℂ) ^ c * z) = ((y.natAbs : ℕ) : ℂ) * z := by rw [e]; push_cast; ring
      rw [e2]
      rw [zsmul_eq_mul] at hy
      have e3 : ((y.natAbs : ℕ) : ℂ) = ((y.sign : ℤ) : ℂ) * (y : ℂ) := by
        rw [← Int.cast_mul, Int.sign_mul_self_eq_natAbs, Int.cast_natCast]
      rw [e3, mul_assoc]
      exact (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := y.sign)).mul hy
    · exact ⟨0, fun h => absurd h hz⟩
  choose cz hcz using one
  obtain ⟨S, rfl⟩ := hL
  refine ⟨S.sup fun v => (J v).support.sup fun mo => cz ((J v).coeff mo), fun k _ _ σ la O hla hO hσ v hv => ?_⟩
  generalize hc : (S.sup fun v => (J v).support.sup fun mo => cz ((J v).coeff mo)) = c
  induction hv using Submodule.span_induction with
  | mem v hv =>
    intro mo
    by_cases hmo : mo ∈ (J v).support
    · have hle : cz ((J v).coeff mo) ≤ c := hc ▸ (Finset.le_sup (f := fun mo => cz ((J v).coeff mo)) hmo).trans
        (Finset.le_sup (f := fun v => (J v).support.sup fun mo => cz ((J v).coeff mo)) hv)
      obtain ⟨x, hx⟩ := hσ v (Submodule.subset_span hv) mo
      have halg : IsAlgebraic ℤ ((J v).coeff mo) := by
        rw [← hx]
        exact ((IsFractionRing.isAlgebraic_iff ℤ ℚ k).2 (Algebra.IsAlgebraic.isAlgebraic x)).algHom σ.toIntAlgHom
      obtain ⟨m, hm, hi⟩ := hcz _ halg
      have h1 := mem_of_integral hla hO hm ⟨(l : k) ^ cz ((J v).coeff mo) * x, by rw [map_mul, map_pow, map_natCast, hx]⟩ hi
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
      rw [MvPolynomial.coeff_smul, smul_eq_mul, pow_add, mul_assoc]
      exact mul_mem (pow_mem (natCast_mem O l) _) h1
    · rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 hmo, smul_zero]; exact zero_mem _
  | zero => intro mo; simp
  | add x y _ _ hx hy => intro mo; rw [map_add, smul_add, MvPolynomial.coeff_add]; exact add_mem (hx mo) (hy mo)
  | smul n x _ hx =>
    intro mo
    rw [map_zsmul, smul_comm, MvPolynomial.coeff_smul]
    exact zsmul_mem (hx mo) n

set_option maxHeartbeats 2000000 in

theorem series_bound {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} {sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {f₀ : WO V W → ℂ} (hP : VacPair ψ θ V W χV χW om ΛV ΛW sW f₀) {r : ℕ} (hr : W.rank = r) (hodd : Odd r)
    {χ : Formalism.L2.Host.HChar D.host.E} {M₀ : ℕ} (hχ : ChiData χW χ M₀) (hM₀ : M₀ ≠ 0)
    {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {lt : LtN Dw V.rank ≃ FVar D W.rank V.rank} {wa : (D.host.E →+* ℂ) × ℕ → ℕ} (hpq : W.rank = Dw.p + Dw.q)
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hB : ∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) Dw.p)
    (hlt : IsLetters Dw lt) (hDom : Dom wa V.rank) (hLast : LastPos Dw wa) {l : ℕ} (hl : l.Prime) {s : GA D V} (hs : s ∈ GfC V) :
    ∃ c : ℕ, ∀ (l₂ : Geo.Tor.Level H) (pd : ℕ) (Xo : Moduli Dw l₂) (c₂ : Coeff l₂) (σ : c₂.F →+* ℂ) (U : Unf Xo c₂ σ r)
      (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
      (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (mu : GA D W → ℂ) (cc : U.Comp → ℂ),
      l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → l₂.A = 1 → l₂.GoodAt l →
      (∀ τ, relab c₂ σ τ = τ) → GoodEmb c₂ σ → IsDict U W hr dict ι x₀ → FrameTie U W hr x₀ sW BW →
      CcIs θ V W hr U dict mu x₀ om f₀ cc → χ.ValuesIn (-1 / 2) σ →
      ∀ (la : HeightOneSpectrum (𝓞 c₂.F)) (O : Subring ℂ), ((l : ℕ) : 𝓞 c₂.F) ∈ la.asIdeal → ValRing σ la O →
      ∀ (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (Φ φ : WO V W → ℂ), IsIdemSum e P →
        (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) →
        GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e) (latO V W ΛV ΛW fun _ => True) l₂.M Φ → (∀ x, Φ x ∈ O) →
        IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ φ →
      ∀ Q ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q.coeff mo ∈ O) →
        ∃ (m : ℕ) (β : Fin m → ℂ) (f : Fin m → Rul Xo c₂), (∀ k, β k ∈ O ∧ f k ∈ sec Xo c₂ wa V.rank ∧
          rdU U (f k) ∈ Formalism.L2.Pj.holSub0 U.X (laU U wa V.rank) ∧ GlobalTheory.GoodPts.BddAll Xo c₂ la 1 (f k)) ∧
          ∀ g : GA D W, (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW φ (MvPolynomial.rename lt Q)) =
            ∑ k, β k * ((lieFac Dw (xiR D) wa : ℂ) * (cc (dict g).1 * mu g * rdU U (f k) (dict g).1 (dict g).2)) := by
  subst hr
  obtain ⟨K, hK⟩ := GlobalTheory.T.vacuum_pair_uniform_level_bound D ψ θ V W χV χW om ΛV ΛW sW f₀ hP
  obtain ⟨Z, cf, hZ, hflip⟩ := GlobalTheory.T.exists_centralFlip_thetaTranslate_halfLevel D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀
  choose cm hcm using fun z : Z => GlobalTheory.T.exists_levelSeries_translate_boundedDenominator D ψ θ V W χV χW om ΛV ΛW sW f₀ hP l hl (s * z) (mul_mem hs (hZ z z.2))
  obtain ⟨ca, hca⟩ := GlobalTheory.T.real_rational_point_acts_harmonic_substitution D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H Dw BW lt wa hpq hΨ hB hlt l (Finset.univ.sup cm)
  obtain ⟨c₃, hc₃⟩ := GlobalTheory.ConstBound.const_dvd _ H Dw V.rank (degA Dw wa) M₀ l hl hM₀
  obtain ⟨v, M₁, hM₁, eM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM₀ l hl.ne_one
  refine ⟨v * K + cf + ca + c₃, fun l₂ pd Xo c₂ σ U dict ι x₀ mu cc hM hc1 hc2 hbadN hA hgood hrel hσ hD hF hcc hval la O hla hO
    e P Φ φ he hPM hΦ hΦO hth Q hQ hQO => ?_⟩
  have hM0 : l₂.M ≠ 0 := by have := l₂.three_le; omega
  have hconj : ConjIn D σ := fun τ a => ⟨embF c₂ τ a, RingHom.congr_fun (hrel τ) a⟩
  have hz : zeta l₂.M ∈ O := by
    have h1 := c₂.zeta_mem
    rw [Geo.Tor.Level.M', hA, Nat.lcm_one_right] at h1
    refine mem_of_integral hla hO (Nat.coprime_one_left l) (zeta_mem_range hM0 h1 σ) ?_
    rw [Nat.cast_one, one_mul]
    exact (Complex.isPrimitiveRoot_exp _ hM0).isIntegral (Nat.pos_of_ne_zero hM0)
  have hn : Nat.Coprime (M₁ * pd) l := Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hl).2 hM₁).symm hc2
  have hn0 : ((M₁ * pd : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hl.one_lt.ne' (by simpa [h] using hn)
  have h4 : ((l : ℂ) ^ (v * K)) • φ ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O := by
    have h1 := Submodule.smul_mem _ (⟨_, pow_mem (inv_mem_of_coprime hla hO hn) K⟩ : O)
      (hK l₂.M e P O Φ φ hM0 hbadN he hPM hz hΦ hΦO hth)
    convert h1 using 1
    change _ = (((M₁ * pd : ℕ) : ℂ)⁻¹ ^ K) • ((l₂.M : ℂ) ^ K • φ)
    rw [smul_smul, hM, eM, mul_assoc, Nat.cast_mul (l ^ v), mul_pow, inv_pow, mul_left_comm, inv_mul_cancel₀ (pow_ne_zero _ hn0),
      mul_one, Nat.cast_pow, pow_mul]
  obtain ⟨e₂, he₂⟩ := GlobalTheory.SingleDatum.exists_isHalfIdem D H l₂
  obtain ⟨z₂, hz₂, z₁, hz₁, hone, hfl⟩ := hflip H l₂ pd hM hc1 hc2 hbadN c₂.F σ la O hla hO hconj hval hz e e₂ P he hPM he₂
  obtain ⟨f', hf', hser₁⟩ := hfl _ h4
  have hbad0 : 2 * l * l₂.M ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hl.ne_zero) hM0
  have b1 : l ∣ 2 * l * l₂.M := (dvd_mul_left l 2).mul_right _
  have b2 : l₂.M ∣ 2 * l * l₂.M := dvd_mul_left _ _
  obtain ⟨γ, h, a, γ', hγ, hrat, ha, hγa, hh, ⟨m, hm, hden⟩, hser₂⟩ := hcm ⟨z₂, hz₂⟩ z₁ hz₁ hone l₂.M _ hM0 hbad0 b1
  have hent : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), IsIntegral ℤ (((m * l ^ cm ⟨z₂, hz₂⟩ : ℕ) : D.host.E) * x) →
      (l : ℂ) ^ Finset.univ.sup cm * τ x ∈ O := fun τ x hx => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := cm) (Finset.mem_univ ⟨z₂, hz₂⟩))
    rw [hd, pow_add, mul_assoc]
    refine mul_mem (pow_mem (natCast_mem O l) _) (mem_of_integral hla hO hm ?_ ?_)
    · obtain ⟨y, hy⟩ := hconj τ x
      exact ⟨(l : c₂.F) ^ cm ⟨z₂, hz₂⟩ * y, by rw [map_mul, map_pow, map_natCast, hy]⟩
    · have := hx.map τ.toIntAlgHom
      simpa [mul_assoc] using this
  obtain ⟨Q', hQ', hQ'O, harch⟩ := hca γ a γ' O hγ hrat ha hγa (fun τ x y => ⟨hent τ _ (hden x y).1, hent τ _ (hden x y).2⟩) Q hQ hQO
  obtain ⟨u, hu, rfl⟩ := GlobalTheory.T.exists_levelPointsTranslateMean_of_integral_combination D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H Dw ι hD.2.1 l₂ e₂ he₂ hbadN O f' hf'
  obtain ⟨Λ, n, hΛ, hun, hT, hnl, hN⟩ := GlobalTheory.SingleDatum.exists_conjLat_levOK D V hP.1.std (hP.2.2.1.symm.trans hP.2.2.2.2.2.2.1)
    (2 * l * l₂.M) l₂.M l l₂.odd ((dvd_mul_right 2 l).mul_right _) b2 b1 h hh
  obtain ⟨hhf, e', Ps, he', hPs, hsupp⟩ := hh
  obtain ⟨y, hy⟩ := GlobalTheory.PtId.exists_isDetAt he' V h
  have hep := GlobalTheory.T.splitSupportedClassScalar_mem_valuationRing D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l _ hχ hl ((hM ▸ dvd_mul_right _ _ : M₀ ∣ l₂.M).trans b2) b1
    c₂.F σ la O hla hO hval h Λ e' Ps y hbad0 he' hPs hhf hsupp hy hΛ
  obtain ⟨m', β, f, hf, hsum⟩ := GlobalTheory.T.exists_forms_theta_short_series_identity D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H Dw l₂ Xo c₂ _ σ hrel hσ U hA hodd rfl dict ι x₀ BW mu cc
    hD hF hcc e₂ he₂ _ _ h Λ e' Ps y b2 he' hPs hhf hsupp hy hΛ hun hT hN lt wa hlt hDom hLast la l hl hla hgood O hO u hu Q' hQ' hQ'O
  obtain ⟨u', hu', hdvd⟩ := hc₃ l₂ pd n Λ hM ((Nat.Prime.coprime_iff_not_dvd hl).1 hc2.symm) hnl hN
  have hu0 : (u' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hl.one_lt.ne' (by simpa [h] using hu')
  refine ⟨m', fun k => (-1) ^ degA Dw wa * clsScal χW y Λ W.rank * β k * (u' : ℂ)⁻¹,
    fun k => (((l ^ c₃ * u' : ℕ) : ℤ) : c₂.F) • f k, fun k => ⟨?_, Submodule.smul_mem _ _ (hf k).2.1, ?_, ?_⟩, fun g => ?_⟩
  · exact mul_mem (mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) hep) (hf k).1) (inv_mem_of_coprime hla hO hu')
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (hf k).2.2.1
  · exact bddAll_scale (by have := (hf k).2.2.2; push_cast at this ⊢; exact this) hdvd
  · have e1 := hser₁ BW (MvPolynomial.rename lt Q) s g
    have e2 := hser₂ e₂ O _ hf' BW (MvPolynomial.rename lt Q) g
    have e3 := harch l₂.M e₂ O hM0 _ hf'
    have e4 := hsum g
    rw [← e3] at e4
    rw [GlobalTheory.FiniteFock.pureTensorO_smul] at e1
    replace e2 := e1.trans e2
    simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul] at e2 e4 ⊢
    have e5 : ∀ k, (-1) ^ degA Dw wa * clsScal χW y Λ W.rank * β k * (u' : ℂ)⁻¹ * ((lieFac Dw (xiR D) wa : ℂ) *
        (cc (dict g).1 * mu g * rdU U ((((l ^ c₃ * u' : ℕ) : ℤ) : c₂.F) • f k) (dict g).1 (dict g).2)) =
        (l : ℂ) ^ c₃ * ((-1) ^ degA Dw wa * clsScal χW y Λ W.rank) * (β k * ((lieFac Dw (xiR D) wa : ℂ) *
        (cc (dict g).1 * mu g * rdU U (f k) (dict g).1 (dict g).2))) := fun k => by
      rw [map_smulₛₗ, map_intCast]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl fun k _ => e5 k, ← Finset.mul_sum, mul_assoc, ← e4, ← e2]
    ring

theorem exists_place_over (k : Type) [Field k] [NumberField k] {l : ℕ} (hl : l.Prime) :
    ∃ la : HeightOneSpectrum (𝓞 k), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal := by
  have h1 : Ideal.span {((l : ℕ) : 𝓞 k)} ≠ ⊤ := fun h => by
    have h2 := Ideal.absNorm_span_natCast (S := 𝓞 k) l
    rw [h, Ideal.absNorm_top] at h2
    exact hl.one_lt.ne' ((pow_eq_one_iff_of_nonneg (Nat.zero_le _) Module.finrank_pos.ne').1 h2.symm)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h1
  have h3 : ((l : ℕ) : 𝓞 k) ∈ m := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨m, hm.isPrime, fun h => by rw [h, Ideal.mem_bot] at h3; exact Nat.cast_ne_zero.2 hl.ne_zero h3⟩, h3⟩

theorem goodAt_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {l₁ l₂ : Geo.Tor.Level H}
    {pd p : ℕ} (hp : p.Prime) (hM : l₂.M = l₁.M * pd) (hc : Nat.Coprime pd p) (h : l₁.GoodAt p) : l₂.GoodAt p := by
  have h1 : l₁.M ≠ 0 := by have := l₁.three_le; omega
  have h2 : pd ≠ 0 := by rintro rfl; have := l₂.three_le; omega
  unfold Geo.Tor.Level.GoodAt at h ⊢
  rw [hM, Nat.factorization_mul h1 h2, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hc.symm), add_zero]
  exact h.trans (Nat.div_le_div_right (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h2)))

theorem castDict_symm {D : D7} {Y : Type} {V W : HSp D} (h : V = W) (F : GA D W → Y) : castDict h (castDict h.symm F) = F := by
  subst h; rfl

theorem castDict_twist {D : D7} {V W : HSp D} (h : V = W) (xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ) (F : GA D V → ℂ) (g : GA D W) :
    castDict h (fun g => ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) * F g) g =
      ((xi (Matrix.GeneralLinearGroup.det (finHom W g)) : ℂˣ) : ℂ) * castDict h F g := by
  subst h; rfl

theorem eq_of_castDict {D : D7} {Y : Type} {V W : HSp D} (h : V = W) {F F' : GA D V → Y}
    (e : ∀ g, castDict h F g = castDict h F' g) : F = F' := by
  subst h; exact funext e

set_option maxHeartbeats 2000000 in

theorem serIntAt_record : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerIntAt T R i (κ i) hV u c0 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV hFP u hu c0 hc0
  have hj : Formalism.L2.Pj.InR D ((i : ℕ) + 1) := inR i
  have h5 : GlobalTheory.Core5 R F := ⟨hLev, hG, hFam, hMod, hTh⟩
  obtain ⟨hPr, q1, q2, q3, q4, q5, q6⟩ := GlobalTheory.AdTh.RecPair.isPair_record_ofFive D G Pl0 T0 A _ R F h5 i A.μ0 hstd
  obtain ⟨-, -, f3, -, f5⟩ := GlobalTheory.AdTh.PhaseMapFree.vec_fock_of_clauses D G Pl0 T0 A _ R hMod hTh i A.μ0 hstd
  have hvac := (hTh.vP i A.μ0).1
  have hP : VacPair R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i A.μ0) (R.ΛV i) (R.ΛW i) (cart (R.MW i (sg0 D A))) (R.vacP i) :=
    ⟨hPr, q1, q2, q3, q4, q5, q6, f3, hvac⟩
  obtain ⟨-, -, -, -, hrpq, -, -, -, -, -, hDom, hn, hLast⟩ := GlobalTheory.AdTh.models_at_record_ofFive D G Pl0 T0 A T R F κ v₀ h5 hTie i
    T.σ₀ rfl (T.dict _ T.σ₀ 1).1
  obtain ⟨-, -, hΨ, -, -⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hL.pins _ hj (κ i)
  have hodd : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hpq := (rank_Wc i).trans hrpq
  have hB : ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ)
      (T.Q.Dw ((i : ℕ) + 1)).p := fun τ => by
    rw [(hL.pins.2.2.2 _ hj).1, ← show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    exact f5 τ
  have hlt := GlobalTheory.FockLetters.isLetters_letterEquiv (n := (Vc D i).rank) (T.Q.Dw ((i : ℕ) + 1)) hΨ hpq
  generalize GlobalTheory.FockLetters.letterEquiv (n := (Vc D i).rank) (T.Q.Dw ((i : ℕ) + 1)) hΨ hpq = lt at hlt
  have hχ := GlobalTheory.T.referenceTuple_secondSplittingCharacter D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hL.pins.2.1.1
  rw [← hMg] at hχ
  have hM₀ : T.Q.l.M ≠ 0 := by have := T.Q.l.three_le; omega
  have hMb : Nat.Coprime T.Q.l.M (GlobalTheory.Tow.badN D) := by
    have : ∀ k, Nat.Coprime (D.host.g k) (GlobalTheory.Tow.badN D) := fun k =>
      ((D.host.level_coprimeS _ (D.host.g_level k)).mul_right (ReciprocityTheory.ChartRestriction.G.PullbackSections.g_coprime_ram D k _ (by simp))).mul_right
        (D.host.ccK_coprime _ (by simp [D.host.g_level k])).symm
    rw [hMg]
    exact (this 0).mul_left (this 1)
  obtain ⟨ph, hph, hbase⟩ := GlobalTheory.T.coreConstants_eq_vacuumIdentity_up_to_phase D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV hFP
  obtain ⟨ka, hka, J, hJH, hJk, hJ⟩ := GlobalTheory.T.harmonicMap_extremalVector_eq_phase_smul_letters D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd u hu c0 hc0 lt hlt
  have hph0 : ph ≠ 0 := fun h => by simp [h] at hph
  have hka0 : ka ≠ 0 := fun h => by simp [h] at hka
  refine ⟨(ka * ph)⁻¹, by rw [norm_inv, norm_mul, hka, hph]; norm_num, fun l hl s hs Lat hLat => ?_⟩
  obtain ⟨c₁, hc₁⟩ := exists_denom J Lat hLat l hl
  obtain ⟨c₂, hc₂⟩ := series_bound hP (rank_Wc i) hodd hχ hM₀ hpq hΨ hB hlt hDom hLast hl hs
  refine ⟨c₂ + c₁, fun C hC hpin hbig S hS xi hxi Φ f hf hΦ v hv => ?_⟩
  obtain ⟨hU, -, hcl, hcb⟩ := hC
  obtain ⟨hval, hcoef, hray⟩ := hbig
  obtain ⟨P, e, he, hPM, hfn, hth⟩ := hf
  obtain ⟨hD, hF, hrel, hσ⟩ := GlobalTheory.T.uniformisedCover_isDictionary_frameCompatible D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV C hU
  have hcc := GlobalTheory.T.vacuumIdentityConstants_cover_of_dominantPins D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV ph hph hbase C hU hpin
  have hM₂ : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hgood : C.d.l₂.GoodAt l := goodAt_of_dvd hl hM₂ hcl
    (Formalism.L2.Pj.goodAt_of_two_primes hMg (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl)
  have hθf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f :=
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hPr.weil.std hPr.inf hth hvac.2.theta
  have hfld : ∀ x ∈ T.Q.c.F, x ∈ C.σ₂.fieldRange := fun x hx => ⟨C.inc ⟨x, hx⟩, RingHom.congr_fun hU.2.2.1 ⟨x, hx⟩⟩
  have hJσ : ∀ w ∈ Lat, ∀ mo, ∃ x, C.σ₂ x = (J w).coeff mo := fun w hw mo =>
    hJk C.σ₂.fieldRange hfld w (fun m => hcoef w hw m) mo
  let Fn : GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ := castDict hV.symm fun g =>
    (l : ℂ) ^ (c₂ + c₁) * ((ka * ph)⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series R i u s f (c0 v) g)
  have key : ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (O : Subring ℂ), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal →
      ValRing C.σ₂ la O → (∀ x, Φ x ∈ O) → Fn ∈ Submodule.span O (C.intForms (wtA (κ i)) (κ i).n {la}) := by
    intro la O hla hO hΦO
    obtain ⟨m, β, fs, hfs, hsum⟩ := hc₂ C.d.l₂ C.d.pd C.d.Xo₂ C.d.c₂ C.σ₂ C.U₂ _ _ _ _ _ hM₂ hU.1.2.2.1 hcl
      (hM₂ ▸ hMb.mul_left hcb) hU.2.1 hgood hrel hσ hD hF hcc hval la O hla hO e P Φ f he hPM hfn hΦO hth
      ((l : ℂ) ^ c₁ • J v) (GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (hJH v))))
      (hc₁ _ C.σ₂ la O hla hO hJσ v hv)
    have e1 : Fn = ∑ k, β k • C.rd (wtA (κ i)) (fs k) := by
      refine eq_of_castDict hV fun g => ?_
      rw [castDict_symm]
      have e2 := hsum g
      have e3 : castDict hV (∑ k, β k • C.rd (wtA (κ i)) (fs k)) g = ∑ k, β k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
          (C.cc₂ (castDict hV C.dict₂ g).1 * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) g *
            rdU C.U₂ (fs k) (castDict hV C.dict₂ g).1 (castDict hV C.dict₂ g).2)) := by
        unfold castDict
        rw [Finset.sum_apply]
        rfl
      rw [e3, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series, hJ f hθf v]
      simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul] at e2 ⊢
      have e4 : ∑ k, β k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
          (ph * C.cc₂ (castDict hV C.dict₂ g).1 * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) g *
            rdU C.U₂ (fs k) (castDict hV C.dict₂ g).1 (castDict hV C.dict₂ g).2)) = ph *
          ∑ k, β k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
          (C.cc₂ (castDict hV C.dict₂ g).1 * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) g *
            rdU C.U₂ (fs k) (castDict hV C.dict₂ g).1 (castDict hV C.dict₂ g).2)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e4] at e2
      refine mul_left_cancel₀ hph0 ?_
      rw [← e2]
      field_simp
      ring
    rw [e1]
    refine sum_mem fun k _ => Submodule.smul_mem _ (⟨β k, (hfs k).1⟩ : O) (Submodule.subset_span ⟨fs k, ⟨?_, ?_⟩, rfl⟩)
    · rw [hn]; exact ⟨(hfs k).2.1, (hfs k).2.2.1⟩
    · rintro _ rfl
      exact (GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg _ _ _ _ _ _ _ _).1 (hfs k).2.2.2
  have hint : Fn ∈ C.intForms (wtA (κ i)) (κ i).n S := by
    refine GlobalTheory.T.mem_integralForms_of_rational_and_local_spans D T hL _ hj T.σ₀ T.toCore.good_σ₀ C hU (hpin _ (dom_wtA (κ i))).1 _ _ (dom_wtA (κ i)) S Fn ?_ fun la hla => ?_
    · obtain ⟨la, hla⟩ := exists_place_over C.d.c₂.F hl
      exact Submodule.span_mono (C.intForms_subset _ _ _)
        (key la _ hla (valRing_range _ _) fun x => let ⟨a, ha, _⟩ := hΦ x; ⟨a, ha⟩)
    · exact key la _ (hS la hla) (valRing_locRing _ _) fun x => let ⟨a, ha, hb⟩ := hΦ x; ⟨a, hb la hla, ha⟩
  refine ⟨_, GlobalTheory.T.twistDeterminant_mul_integralForms_rayClassCover D T hL _ hj C hU hray xi hxi _ _ S Fn hint, fun g => ?_⟩
  rw [castDict_twist, castDict_symm]
  ring

end GlobalTheory.LevelSeries

end
