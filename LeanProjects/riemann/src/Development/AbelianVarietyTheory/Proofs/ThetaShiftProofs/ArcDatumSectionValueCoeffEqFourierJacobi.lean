import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLetterRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangularStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScalingStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFrameChangeByConstantsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnfStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangentStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LaurentCoeffSectionValueArcEqFourierJacobiStatement
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfPowEqInt
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.FirstMinimumRankZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcId

section Freq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X X' : Type} [AddCommGroup X] [Module (𝓞 E) X]
  [AddCommGroup X'] [Module (𝓞 E) X']

omit [IsCMField E] in
theorem pairE_comp (f : X' ≃ₗ[𝓞 E] X) (ξ : Module.Dual ℤ X) (y : X') :
    pairE (E := E) (ξ.comp (f.toLinearMap.restrictScalars ℤ)) y = pairE ξ (f y) := by
  simp [pairE]

theorem betaAt_comp (f : X' ≃ₗ[𝓞 E] X) (ξ : Module.Dual ℤ X) {N : ℕ} {be : LinearMap.BilinForm ℤ X}
    {be' : LinearMap.BilinForm ℤ X'} (hbe : ∀ y z, be' y z = be (f y) (f z)) {ν₀ : E} {jj : ℤ}
    (h : BetaAt ξ N be ν₀ jj) : BetaAt (ξ.comp (f.toLinearMap.restrictScalars ℤ)) N be' ν₀ jj := by
  refine ⟨h.1, fun s hs => ?_⟩
  have hs' : IsBePar ξ be s := ⟨hs.1, fun x y => by
    obtain ⟨x, rfl⟩ := f.surjective x
    obtain ⟨y, rfl⟩ := f.surjective y
    rw [← hbe, ← hs.2, pairE_comp, pairE_comp]⟩
  refine ⟨(h.2 s hs').1, fun ν h1 h2 h3 => (h.2 s hs').2 ν h1 h2 fun s' hl => h3 s' ⟨hl.1, fun x y => ?_⟩⟩
  rw [pairE_comp, pairE_comp]
  exact hl.2 _ _

end Freq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

theorem gtTanR_of_isArcFr (hG : Out.GlobalFnsSt) {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] {b : O →+* A} {a : ArcIn Dw l β A b}
    {χ : Sp (PowerSeries A) ⟶ Y.X} {W : Wit Y a χ}
    {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)} {th : a.D₀.P.L.Sec}
    {S : Type} [CommRing S] [Algebra c.F S] {ι : PowerSeries A →+* S} (hι : Function.Injective ι)
    {y : FrPt Xo c S} (h : IsArcFr W e th ι y) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) : GtTanR (e τ k) := by
  obtain ⟨z, t', m1, m2, φ, -, -, -, -, -, hu, -⟩ := h
  obtain ⟨v, u', hv, h1, h2, h3⟩ := hu τ k
  refine ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W (e τ k)).2 v hv).2 ?_
  have e1 : eSec t'.G ≫ m1.φ = y.x ≫ eSec Xo.univ.t.G := m1.cm.e_comm.trans (congrArg (· ≫ _) m1.base)
  have e2 : eSec t'.G ≫ m2.φ = spMap ι ≫ eSec W.t.G := m2.cm.e_comm.trans (congrArg (· ≫ _) m2.base)
  have h0 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ u' = eSec t'.G := by
    refine m1.cart.1.hom_ext ?_ ?_
    · exact ((Category.assoc _ _ _).trans ((congrArg _ h1).trans (y.tan τ k).2)).trans e1.symm
    · refine ((Category.assoc _ _ _).trans (congrArg _ h3)).trans ((sp_comp _ _).trans ?_)
      rw [TanPart.fst_alg]
      exact (Spec.map_id _).trans (Over.w (MonObj.one (X := t'.G))).symm
  have := W.t.semi.separated
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ι) hι
  refine ExtUnique.hom_ext_of_dominant W.t.G.hom ?_ (spMap ι) ?_
  · refine ((Category.assoc _ _ _).trans (congrArg _ (Over.w v))).trans ((sp_comp _ _).trans ?_)
    rw [TanPart.fst_alg]
    exact (Spec.map_id _).trans (Over.w (MonObj.one (X := W.t.G))).symm
  · refine Eq.trans ?_ e2
    rw [← h0, Category.assoc, h2, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
    congr 2
    exact RingHom.ext fun x => by simp [dualMap]

section Ev

variable {K : Type} [Field K]

def cstL : ℂ →+* ℂ⸨X⸩ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.C (R := ℂ))

theorem cstL_eq (z : ℂ) : cstL z = HahnSeries.C z := HahnSeries.ofPowerSeries_C z

def evP (ι : K →+* ℂ) (x : ArcLt Dw → ℂ) : MvPolynomial (ArcLt Dw) K⸨X⸩ →+* ℂ⸨X⸩ :=
  MvPolynomial.eval₂Hom (LetterMap.coeffMap ι) fun v => cstL (x v)

theorem isUnit_evalLaurent_det (ι : K →+* ℂ) {x : ArcLt Dw → ℂ} (hx : InvBl x) : IsUnit (evP ι x (arcDet Dw K)) := by
  rw [isUnit_iff_ne_zero, arcDet, map_prod, Finset.prod_ne_zero_iff]
  intro τ _
  have : (evP ι x).mapMatrix (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) K⸨X⸩)) =
      cstL.mapMatrix (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩) := by
    ext i k : 2
    simp [evP]
  rw [RingHom.map_det, this, ← RingHom.map_det]
  exact (map_ne_zero cstL).2 (hx τ)

def evS (ι : K →+* ℂ) {x : ArcLt Dw → ℂ} (hx : InvBl x) : ArcS Dw K →+* ℂ⸨X⸩ :=
  IsLocalization.Away.lift (arcDet Dw K) (g := evP ι x) (isUnit_evalLaurent_det ι hx)

theorem evS_algebraMap (ι : K →+* ℂ) {x : ArcLt Dw → ℂ} (hx : InvBl x) (P : MvPolynomial (ArcLt Dw) K⸨X⸩) :
    evS ι hx (algebraMap _ _ P) = evP ι x P := IsLocalization.Away.lift_eq _ _ _

theorem evS_arcι (ι : K →+* ℂ) {x : ArcLt Dw → ℂ} (hx : InvBl x) (g : PowerSeries K) :
    evS ι hx (arcι Dw K g) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map ι g) :=
  (evS_algebraMap ι hx _).trans ((MvPolynomial.eval₂Hom_C _ _ _).trans (LetterMap.coeffMap_ofPowerSeries ι g))

theorem evS_arcX (ι : K →+* ℂ) {x : ArcLt Dw → ℂ} (hx : InvBl x) (τ : E →+* ℂ) (i k : Fin (Dw.mult τ)) :
    evS ι hx (arcX Dw K τ i k) = cstL (x ⟨τ, (i, k)⟩) :=
  (evS_algebraMap ι hx _).trans (MvPolynomial.eval₂Hom_X' _ _ _)

theorem coeff_evalLaurent (ι : K →+* ℂ) (x : ArcLt Dw → ℂ) (P : MvPolynomial (ArcLt Dw) K⸨X⸩) (j : ℤ) :
    (evP ι x P).coeff j = ∑ μ ∈ P.support, ι ((P.coeff μ).coeff j) * ∏ v ∈ μ.support, x v ^ μ v := by
  rw [evP, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [← map_pow, ← map_prod]
  rw [mul_comm, cstL_eq, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]
  rfl

end Ev

theorem exists_frPt_at (h1 : Out.Laws) (h2 : Out.Laws2) (hev : GlobalTheory.Reg.EvLaws Xo c)
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) [Algebra c.F ℂ⸨X⸩]
    (halg : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = cstL (ι (algebraMap c.F K₁ x)))
    {ζ : K₁} {e₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt (d.a.restrict (c.V d.Wp).subtype).D₀ (epsR K₁)}
    {y₀ : FrPt Xo c (ArcS Dw K₁)} (hy₀ : IsArcFr d.W e₀ d.th (arcι Dw K₁) y₀)
    (hc : FrChg (letM Dw K₁) (cst Dw ζ) y₀ d.yF) (hth : ThNZ d.th)
    {b' : c.V d.Wp →+* ℂ} {a₁ : ArcIn Dw l (c.V d.Wp).subtype ℂ b'}
    {p : Out.IsPullDeg ι (d.a.restrict (c.V d.Wp).subtype).D₀ a₁.D₀}
    {W₁ : Wit d.Y a₁ (spMap (PowerSeries.map ι) ≫ d.χ)} (hp : InBC ι (d.a.restrict (c.V d.Wp).subtype) a₁ p)
    (hW : WitBC ι p d.W W₁) {e₁ e₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a₁.D₀ (epsR ℂ)} {th₁ : a₁.D₀.P.L.Sec}
    (he : ∀ τ k, LetBC p (e₀ τ k) (e₁ τ k)) (ht : ThBC p d.th th₁) (hth₁ : ThNZ th₁)
    {x : ArcLt Dw → ℂ} (hx : InvBl x) (he₂ : ∀ τ i, GtComb (fun k => x ⟨τ, (i, k)⟩) (e₁ τ) (e₂ τ i))
    (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ι ζ ≠ 0 ∧ ∃ y : FrPt Xo c ℂ⸨X⸩, IsArcFr W₁ e₂ th₁ (HahnSeries.ofPowerSeries ℤ ℂ) y ∧
      ∀ F ∈ sec Xo c a' n, ajAt d ι F x = ι ζ ^ n * (evR Xo c F y).coeff d.jj := by
  have hY : Mono d.Y.j := GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  have hdom := (GlobalTheory.ArcConst.algebraic_const E H Dw K₁).1
  let φ : ArcS Dw K₁ →ₐ[c.F] ℂ⸨X⸩ :=
    { evS ι hx with
      commutes' := fun r => by
        change evS ι hx _ = _
        rw [arcS_pin, evS_arcι, PowerSeries.map_C, halg]
        rfl }
  obtain ⟨y₁, hy₁⟩ := hev.bc _ _ φ y₀
  obtain ⟨z₁, hz₁⟩ := hev.bc _ _ φ d.yF
  have a₀ := (GlobalTheory.T.arcFramedPoint_unique_and_baseChange h1 h2 E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W e₀ d.th hth _ _ y₀ hy₀).2 hY _ φ y₁ hy₁
  have hι : φ.toRingHom.comp (arcι Dw K₁) = (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map ι) :=
    RingHom.ext fun g => evS_arcι ι hx g
  rw [hι] at a₀
  have b₁ := GlobalTheory.T.isFramedPoint_of_arc_baseChange h1 h2 E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W ℂ b' a₁ ι p W₁ hY hp hW e₀ e₁ d.th th₁ he ht
    _ _ y₁ a₀
  have c₁ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c (ArcS Dw K₁)).2.2.1 _ φ _ _ _ _ _ _ hc hy₁).1 hz₁
  let g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := fun τ => Matrix.of fun i k => x ⟨τ, (i, k)⟩
  have hM : ∀ τ, (letM Dw K₁ τ).map φ = 1 * (g τ).map cstL := fun τ => by
    rw [one_mul]
    exact Matrix.ext fun i k => evS_arcX ι hx τ i k
  have hζ : φ (cst Dw ζ) = cstL (ι ζ) * 1 := by
    rw [mul_one]
    refine (evS_arcι ι hx _).trans ?_
    rw [PowerSeries.map_C]
    rfl
  rw [funext hM, hζ] at c₁
  have hu := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c ℂ⸨X⸩ _ _ y₁).2.2.1 z₁ c₁
  obtain ⟨y₂, hy₂⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c ℂ⸨X⸩ (fun τ => (g τ).map cstL) 1 y₁).1
    (fun τ => by simpa only [one_mul] using hu.1 τ) isUnit_one
  have c₂ : FrChg (fun _ => 1) (cstL (ι ζ)) y₂ z₁ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c ℂ⸨X⸩).1 _ _ _ _ _ _ _ hy₂).2 c₁
  refine ⟨fun h0 => hu.2.ne_zero (by rw [h0, map_zero, zero_mul]), y₂, ?_, fun F hF => ?_⟩
  · refine GlobalTheory.T.arcFrame_change_by_constants h1 h2 E H Dw l Xo c _ _ d.Y ℂ b' a₁ _ W₁ e₁ e₂ th₁ th₁ g 1 hth₁ he₂ (ThMul.refl _) _ _ y₁ y₂
      hY b₁ ?_
    rw [map_one, map_one]
    exact hy₂
  · obtain ⟨P, hP, -⟩ := evR_arc_isHomogeneous h1 h2 E H Dw l Xo c hev K₁ d a' n F hF
    have eS := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a' n F hF (ArcS Dw K₁)).1 _ φ _ _ hz₁
    have eT := ((GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a' n F hF ℂ⸨X⸩).2 inferInstance).2 _ _ _ c₂
    have e3 : evP ι x P = cstL (ι ζ ^ n) * evR Xo c F y₂ := by
      rw [map_pow, ← eT, eS, ← hP]
      exact (evS_algebraMap ι hx P).symm
    rw [ajAt, ← hP, LetterMap.num_algebraMap, ← coeff_evalLaurent, e3, cstL_eq, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]

theorem generic_mem {K₁ : Type} [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ)
    (q : Sp (PowerSeries ℂ)) (hq : PowerSeries.X ∉ q.asIdeal) :
    (spMap (PowerSeries.map ι) ≫ d.χ) q ∈ Set.range d.Y.j := by
  obtain ⟨z, hz, -⟩ := d.arcDatum_isArc_point_basis.2.1
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  obtain ⟨hdom, hinj, -⟩ := GlobalTheory.ArcConst.algebraic_const E H Dw K₁
  have hq0 : q.asIdeal = ⊥ := by
    by_contra h
    apply hq
    have hm := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime (PowerSeries ℂ)).1 inferInstance
    rw [hm.2.unique ⟨h, q.isPrime⟩ ⟨IsDiscreteValuationRing.not_a_field _, inferInstance⟩,
      PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  have hι : Function.Injective (arcι Dw K₁) :=
    hinj.comp ((MvPolynomial.C_injective _ _).comp HahnSeries.ofPowerSeries_injective)
  let η : Sp (ArcS Dw K₁) := (⊥ : PrimeSpectrum (ArcS Dw K₁))
  have hη : spMap (arcι Dw K₁) η = spMap (PowerSeries.map ι) q := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (arcι Dw K₁) ⊥ = Ideal.comap (PowerSeries.map ι) q.asIdeal
    rw [hq0, Ideal.comap_bot_of_injective _ hι, Ideal.comap_bot_of_injective _ (PowerSeries.map_injective ι ι.injective)]
  refine ⟨z η, ?_⟩
  rw [← Scheme.Hom.comp_apply, hz, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hη]

theorem ajAt_eq_fj_of_overBase : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ToroidalArchimedeanCondition → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (ι.comp (algebraMap c.F K₁)) r) (ξ : Module.Dual ℤ d.a.D₀.X) (ν₀ : E) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c (ι.comp (algebraMap c.F K₁)) → IsUnf U → d.OverBase → PushInvertible d.Y.t.G d.Y.t.PP.L → Module.finrank (𝓞 E) d.a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' d.a.be ν₀ d.jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∃ (k : U.Comp) (ξ' : Fin r → E) (fr : (ArcLt Dw → ℂ) → Frame (U.X k).Ψ r) (u₁ : ℂ) (κ : (ArcLt Dw → ℂ) → ℂ), u₁ ≠ 0 ∧ (U.X k).IsIso ξ' ∧ (∀ x, InvBl x → κ x ≠ 0) ∧ (∀ x, InvBl x → fr x ∈ (U.X k).dom) ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → ∀ x, InvBl x → ajAt d ι F x * u₁ ^ d.jj = κ x * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) (fr x) := by
  intro h1 h2 hU h5 hN E _ _ _ H Dw l Xo c K₁ _ _ d ι r U ξ ν₀ a' n hev hgood hunf hover hpush hrk hξ hbeta hdom htv
  letI : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  haveI : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  letI : Algebra c.F ℂ⸨X⸩ := (cstL.comp (ι.comp (algebraMap c.F K₁))).toAlgebra
  obtain ⟨Uw⟩ := GlobalTheory.T.nonempty_unifWitnessData_of_isUnf E H Dw l Xo c _ r U hunf
  obtain ⟨ζ, e₀, y₀, hy₀, hc⟩ := d.exists_normal_tangent h1 h2
  have hth : ThNZ d.th := by
    obtain ⟨_, _, _, _, hne, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.nonzero_generates h1 h2 K₁ _ d.th).1.1 hne
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  have hι : Function.Injective (arcι Dw K₁) := (GlobalTheory.ArcConst.algebraic_const E H Dw K₁).2.1.comp
    ((MvPolynomial.C_injective _ _).comp HahnSeries.ofPowerSeries_injective)
  obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hU h5 E H Dw l Xo c _ _ d.Y K₁ ℂ _
    (d.a.restrict (c.V d.Wp).subtype) ι ι.injective ((ι.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) rfl
  obtain ⟨hW, hlet, htan, hthx, hnz⟩ := hbc a₁ p hp
  obtain ⟨W₁, hW₁⟩ := hW d.χ d.W
  choose e₁ he₁ using fun τ k => (hlet (e₀ τ k)).exists
  obtain ⟨th₁, hth₁⟩ := (hthx d.th).exists
  have hover₁ : (spMap (PowerSeries.map ι) ≫ d.χ) ≫ d.Y.s = spMap (PowerSeries.C (R := ℂ)) ≫
      spMap ((ι.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) := by
    rw [Category.assoc, hover, sp_comp, sp_comp, sp_comp]
    congr 1
    exact RingHom.ext fun x => PowerSeries.map_C _ _
  obtain ⟨Ha⟩ := hN E H Dw l Xo c _ _ d.Y (ι.comp (algebraMap c.F K₁)) a₁ _ W₁ Uw.g _ Uw.F hgood
    ((GlobalTheory.Relab.relab_good E H l c _ hgood).2.2.2 Dw Uw.g Uw.e) (GlobalTheory.ArcInTest.exists_values c d.Wp) hover₁
    (generic_mem d ι)
  let f : a₁.D₀.X ≃ₗ[𝓞 E] d.a.D₀.X := { p.xe with map_smul' := hp.2.1 }
  obtain ⟨k, ξ', sE, C, hiso, -, -, -, hC, -, hmain⟩ := GlobalTheory.T.laurentCoeff_sectionValue_arc_eq_fourierJacobi h1 h2 E H Dw l Xo c _ r U Uw _ _ d.Y a₁ _ W₁ Ha
    th₁ (ξ.comp (f.toLinearMap.restrictScalars ℤ)) ν₀ d.jj a' n hev hgood hunf (fun _ => rfl) hover₁
    (mono_spMap_subtype _) hpush (hnz _ _ hth₁ hth) (f.finrank_eq.trans hrk)
    (fun h => hξ (LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := f.surjective y
      exact LinearMap.congr_fun h y))
    (betaAt_comp f ξ hp.2.2.1 hbeta) hdom htv (((Ha.T + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  obtain ⟨v₁, v₂, -, v₄⟩ := GlobalTheory.T.torusExt_exponential_derivative_bijective_tangent h1.globalFns E H Dw l Xo c _ _ _ d.Y a₁ _ W₁ _ _ Uw.F Ha
  choose z₁ hz₁ using fun τ i =>
    (v₁ (e₁ τ i) (htan _ _ (he₁ τ i) (gtTanR_of_isArcFr h1.globalFns hι hy₀ τ i))).exists
  have key : ∀ x, InvBl x → ∃ (fr : (U.X k).dom) (κ : ℂ), κ ≠ 0 ∧
      ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) →
        ajAt d ι F x * eTwoPi (((Ha.T + 1 : ℝ) : ℂ) * Complex.I) ^ d.jj =
          κ * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) fr.1 := fun x hx => by
    choose e₂ he₂ using fun (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) => (v₂ (∑ j, x ⟨τ, (i, j)⟩ • z₁ τ j)).exists
    obtain ⟨hζ, y, hy, hval⟩ := exists_frPt_at h1 h2 hev d ι (fun _ => rfl) hy₀ hc hth hp hW₁ he₁ hth₁
      (hnz _ _ hth₁ hth) hx (fun τ i => (v₄ _ _ _ _ _ (hz₁ τ)).2 (he₂ τ i)) a' n
    obtain ⟨fr, κ, -, -, -, -, -, -, hκ, hF⟩ := hmain e₂ _ y hy he₂
    refine ⟨fr, ι ζ ^ n * κ, mul_ne_zero (pow_ne_zero _ hζ) (norm_pos_iff.1 ?_), fun F h hb => ?_⟩
    · rw [hκ]
      exact mul_pos (Real.rpow_pos_of_pos (mul_pos hC (Finset.prod_pos fun τ _ =>
        inv_pos.2 (GlobalTheory.FlagFlowCheck.tt_pos _ fr.2 hiso.2.2 τ))) _) (BoundedSectionAlgebra.nfac_pos _ fr.2 _)
    · rw [hval F h, mul_assoc, hF F h hb, mul_assoc]
  have hone : InvBl (Dw := Dw) fun v => (1 : Matrix (Fin (Dw.mult v.1)) (Fin (Dw.mult v.1)) ℂ) v.2.1 v.2.2 :=
    fun τ => (Matrix.det_one (n := Fin (Dw.mult τ)) (R := ℂ)).trans_ne one_ne_zero
  classical
  choose fr κ hκ hF using key
  refine ⟨k, ξ', fun x => if hx : InvBl x then (fr x hx).1 else (fr _ hone).1,
    eTwoPi (((Ha.T + 1 : ℝ) : ℂ) * Complex.I),
    fun x => if hx : InvBl x then κ x hx else 1, Complex.exp_ne_zero _, hiso, fun x hx => ?_, fun x hx => ?_,
    fun F h hb x hx => ?_⟩
  · simpa only [dif_pos hx] using hκ x hx
  · simpa only [dif_pos hx] using (fr x hx).2
  · simpa only [dif_pos hx] using hF x hx F h hb

theorem ajAt_eq_fj : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ToroidalArchimedeanCondition → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (ι.comp (algebraMap c.F K₁)) r) (ξ : Module.Dual ℤ d.a.D₀.X) (ν₀ : E) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c (ι.comp (algebraMap c.F K₁)) → IsUnf U → d.OverBase → (∀ τ k, GtTanR (d.e τ k)) → PushInvertible d.Y.t.G d.Y.t.PP.L → Module.finrank (𝓞 E) d.a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' d.a.be ν₀ d.jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∃ (k : U.Comp) (ξ' : Fin r → E) (fr : (ArcLt Dw → ℂ) → Frame (U.X k).Ψ r) (u₁ : ℂ) (κ : (ArcLt Dw → ℂ) → ℂ), u₁ ≠ 0 ∧ (U.X k).IsIso ξ' ∧ (∀ x, InvBl x → κ x ≠ 0) ∧ (∀ x, InvBl x → fr x ∈ (U.X k).dom) ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → ∀ x, InvBl x → ajAt d ι F x * u₁ ^ d.jj = κ x * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) (fr x) :=
  fun h1 h2 hU h5 hN E _ _ _ H Dw l Xo c K₁ _ _ d ι r U ξ ν₀ a' n hev hgood hunf hover _ =>
    ajAt_eq_fj_of_overBase h1 h2 hU h5 hN E H Dw l Xo c K₁ d ι r U ξ ν₀ a' n hev hgood hunf hover

end GlobalTheory.ArcId
