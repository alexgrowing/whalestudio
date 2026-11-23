import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePointMemClosed
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsModelPushInvertibleOverCompleteDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplication
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeSplitIndexPrimeToStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsometryConjPointSplitUpToIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexLinearOfPureTypesFiniteIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedFieldOfInertiaPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixesComplexFibrePureEndomorphismTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmEllipticCurveGaloisTorsionSectionsStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.UnramPoint

section Curve

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_curveOver (hA : GlobalTheory.Published.FormalAlgebraisation) (hG : GlobalTheory.Published.GrothendieckMessing)
    (hR : GlobalTheory.Published.AbelianDeRham) (H : Host E) {n q : ℕ} (hq : q.Prime) (hn : ¬ q ∣ n) (hd : ¬ q ∣ H.d) :
    ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ CurveOver H F' n := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (h ▸ dvd_zero q)
  obtain ⟨N, _, _, ω, C, C₀, ψ, hω, hψ, hy⟩ := GlobalTheory.T.exists_cmEllipticCurve_galois_torsion_sections E H n hn0
  have h1 : wC H (1, 0) = 1 := by simp [wC]
  obtain ⟨F', _, hF, h⟩ := GlobalTheory.T.exists_unramified_field_of_inertia_property N q hq (fun τ => ∃ io, C₀.ActsBy τ io n (1, 0))
    (by
      rintro τ τ' ⟨i, hi, hi'⟩ ⟨j, hj, hj'⟩
      have e : spMap (τ' : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) = spMap ((τ.trans τ' : ℂ ≃+* ℂ) : ℂ →+* ℂ) := by
        rw [← Spec.map_comp]; rfl
      refine ⟨j ≫ i, (hj.comp hi).congr e rfl, fun a => ?_⟩
      have k := hi' a
      have k' := hj' a
      rw [h1, _root_.one_mul] at k k' ⊢
      rw [← Category.assoc, k', Category.assoc, k, ← Category.assoc, e])
    (by
      intro τ 𝔮 h𝔮 hq𝔮 hτ
      haveI := C.act.hom (GlobalTheory.CM.wK H)
      have hu : 1 - ω - ω ∉ 𝔮 := fun hm => by
        have h2 : (H.d : 𝓞 N) ∈ 𝔮 := by
          have : (H.d : 𝓞 N) = -((1 - ω - ω) * (1 - ω - ω)) := by linear_combination hω
          rw [this]; exact neg_mem (𝔮.mul_mem_left _ hm)
        obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hd)
        refine h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
        have h3 : (u : 𝓞 N) * (q : 𝓞 N) + (v : 𝓞 N) * (H.d : 𝓞 N) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 N) huv
        rw [← h3]
        exact add_mem (𝔮.mul_mem_left _ hq𝔮) (𝔮.mul_mem_left _ h2)
      obtain ⟨io, hio, hx⟩ := GlobalTheory.T.inertia_fixes_complex_fibre_pure_endomorphism_torsion hA hG N C.P _ (1 - ω) ω (GlobalTheory.T.cmEllipticCurve_isPureHodgeEndomorphismBaseChange hR E H _ ω C) q hq 𝔮 h𝔮 hq𝔮 hu τ hτ
        C₀.P.A ψ hψ
      refine ⟨io, hio, fun a => ?_⟩
      obtain ⟨y, hy1, hy2⟩ := hy a
      rw [h1, _root_.one_mul]
      exact hx n hn y hy1 _ (Over.w (C₀.u.ex fun _ => C₀.c * (wC H a / n))) hy2)
  exact ⟨F', inferInstance, hF, fun τ hτ => ⟨C₀, h τ hτ⟩⟩

theorem exists_eq_add_nsmul {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) {m : ℕ} (hm : 0 < m) {t w : (F.Di i).La}
    (h : (F.ex i P ((m : ℂ)⁻¹ • P t)).left = (F.ex i P ((m : ℂ)⁻¹ • P w)).left) : ∃ x, w = t + m • x := by
  have h0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have e : F.ex i P ((m : ℂ)⁻¹ • P t) = F.ex i P ((m : ℂ)⁻¹ • P w) := Over.OverMorphism.ext h
  have e' := F.ex_add i P hP ((m : ℂ)⁻¹ • P (w - t)) ((m : ℂ)⁻¹ • P t)
  rw [← smul_add, ← map_add, sub_add_cancel, e] at e'
  obtain ⟨x, hx⟩ := (F.ex_ker i P hP _).1 (mul_eq_right.1 e'.symm)
  refine ⟨x, ?_⟩
  rw [← sub_eq_iff_eq_add']
  apply hP.2.1
  rw [map_nsmul, hx, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem conj_point_eq {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0) (hty : IsTypeFn H D.p D.q ty) (τ : ℂ ≃+* ℂ)
    (hτσ : (τ : ℂ →+* ℂ).comp σ = σ) {N : ℕ} (hN : 0 < N)
    (hfix : FixesCurve H τ (N * l.M')) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hs : ∀ v : (F.Di i).La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) :
    spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
  obtain ⟨C, io, hC⟩ := hfix
  have hτ : τ H.rt0 = H.rt0 := by
    rw [← hσ]
    exact RingHom.congr_fun hτσ _
  obtain ⟨i', P', hP', hu⟩ := F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P)
    (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hA : 0 < l.A := l.A_pos
  have hdiv : ∀ m : ℕ, m ∣ N * l.M' → C.ActsBy τ io m (1, 0) :=
    ((GlobalTheory.CompRat.Acts.main E H C τ hτ io hC.1 _ (Nat.mul_pos hN (Nat.lcm_pos hM hA))).2 _ hC).2
  obtain ⟨Φ, hE, hp, hm, hact⟩ := GlobalTheory.T.exists_lattice_isometry_conj_point_split_up_to_index E H D l Xo σ g ty F hD hσ hty τ hτ C io hC.1 i P hP i' P' hP' N hN hs
    hu.symm (hdiv _ (dvd_mul_right _ _))
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_complexLinear_of_pure_types_finite_index E H _ _ g ty P P' hP hP' Φ N hN hs hp hm
  have tu : ∀ (y : Sp ℂ ⟶ Xo.X) (s : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G), (toUnit (Over.mk y) ≫ s).left = y ≫ s.left := by
    intro y s
    rw [Over.comp_left]
    congr 1
  have hA' : ∀ v, ∃ x, Φ (F.t i v) = F.t i' v + l.A • x := fun v => by
    have key := hact l.A hA (hdiv _ (Nat.mul_dvd_mul_left _ (Nat.dvd_lcm_right _ _))) (F.t i v)
    rw [← F.ex_etaA i P hP v, tu, ← Category.assoc, hu.symm, ← tu, F.ex_etaA i' P' hP' v] at key
    exact exists_eq_add_nsmul F hP' hA key
  refine hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i')
      (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P')
      ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, F.ex_onto i P hP, isHolTo_ex_at_period F i P hP,
        (F.ex_diff i P hP).1, (F.ex_diff i P hP).2⟩, F.ex_ker i P hP, F.ex_lin i P hP, F.ex_weil i P hP,
        F.ex_eta i P hP, F.ex_etaA i P hP⟩
      ⟨F.over_σ i' P' hP', hP', ⟨F.ex_add i' P' hP', F.ex_onto i' P' hP', isHolTo_ex_at_period F i' P' hP',
        (F.ex_diff i' P' hP').1, (F.ex_diff i' P' hP').2⟩, F.ex_ker i' P' hP', F.ex_lin i' P' hP',
        F.ex_weil i' P' hP', F.ex_eta i' P' hP', F.ex_etaA i' P' hP'⟩).2 ⟨Φ, L, hE, fun v hv => ?_, hA', hL⟩).symm
  have key := hact l.M hM (hdiv _ (Nat.mul_dvd_mul_left _ (Nat.dvd_lcm_left _ _))) (F.t i v)
  rw [← F.ex_eta i P hP v hv, tu, ← Category.assoc, hu.symm, ← tu, F.ex_eta i' P' hP' v hv] at key
  exact exists_eq_add_nsmul F hP' hM key

end Curve

section Point

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompRat GlobalTheory.CompRat.FixedConst
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FixedPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_fixed_point (hD : 1 ≤ Dw.p + Dw.q) {q : ℕ} (hq : q.Prime) (hqd : ¬ q ∣ 2 * H.d * (discr E).natAbs)
    (Z : Comp Xo c) :
    ∃ (N : ℕ) (x : Sp ℂ ⟶ Xo.XF c), ¬ q ∣ N ∧ x ≫ strK = spMap (algebraMap c.F ℂ) ∧
      (∀ p, x p ∈ (Z : Set (Xo.XF c))) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ c.F, τ a = a) → FixesCurve H τ (N * l.M') → spMap (τ : ℂ →+* ℂ) ≫ x = x := by
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H Dw.p Dw.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  obtain ⟨L, _, _, j, x₁, hx₁, hZ₁⟩ := exists_numberField_point Z
  letI : Algebra c.F L := j.toAlgebra
  let k : L →ₐ[c.F] ℂ := IsAlgClosed.lift
  obtain ⟨h1, h2⟩ := GlobalTheory.FlatLine.point_ext hx₁ hZ₁ k.toRingHom
  have e : k.toRingHom.comp j = algebraMap c.F ℂ := k.comp_algebraMap
  rw [e] at h1
  generalize spMap k.toRingHom ≫ x₁ = x₂ at h1 h2
  have hsp : spMap (algebraMap (KA l) ℂ) =
      spMap (algebraMap c.F ℂ) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← Spec.map_comp]; rfl
  obtain ⟨i, P, hP, hu⟩ := F.onto (x₂ ≫ prX Xo c) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h1, hsp])
  obtain ⟨Lp, Lm, N, hN, hs, ho, hp, hm⟩ := GlobalTheory.T.exists_lattice_split_index_prime_to E H (F.Di i) q hq hqd
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h => hN (h ▸ dvd_zero q)
  obtain ⟨P₀, hP₀, k₁, k₂⟩ := GlobalTheory.CM.FamCompare.exists_period (F.Di i) Lp Lm (fun z => ⟨N, hN0, hs z⟩) ho hp hm
    (ty := ty) (by rw [(F.sig i).1, (F.sig i).2]; exact hty)
  let x : Sp ℂ ⟶ Xo.XF c := pullback.lift (F.u i P₀) (spMap (algebraMap c.F ℂ)) (by rw [F.over_σ i P₀ hP₀, hsp])
  have hx1 : x ≫ prX Xo c = F.u i P₀ := pullback.lift_fst _ _ _
  have hx2 : x ≫ strK = spMap (algebraMap c.F ℂ) := pullback.lift_snd _ _ _
  refine ⟨N, x, hN, hx2, fun p => ?_, fun τ hτ hC => ?_⟩
  · obtain ⟨f, hf⟩ := exists_indicator (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z)
    have key := valAt_eq_of_finite_values_anyLevel E H Dw l Xo _ g ty F hD rfl hty c (algebraMap c.F ℂ) f {0, 1}
      (Set.toFinite _) (fun y _ => by
        rw [valAt'_top]
        by_cases h : y p ∈ (Z : Set (Xo.XF c))
        exacts [Or.inr ((hf y p).1 h), Or.inl ((hf y p).2 h)]) i P₀ P hP₀ hP x x₂ hx1 hx2 hu.symm h1
    rw [valAt'_top, valAt'_top, (hf x₂ p).1 (h2 p)] at key
    by_contra h
    exact zero_ne_one (((hf x p).2 h).symm.trans key)
  · have h := conj_point_eq F hD rfl hty τ (RingHom.ext fun a => hτ _ (c.le a.2)) hN0 hC i P₀ hP₀
      fun v => sup_le_sup k₁ k₂ (hs v)
    apply pullback.hom_ext
    · rw [Category.assoc, hx1, h]
    · rw [Category.assoc, hx2, ← Spec.map_comp]
      congr 1
      ext a
      exact hτ _ a.2

end Point

section Integral

open AlgebraicGeometry CategoryTheory
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_intFr (hpq : 1 ≤ Dw.p + Dw.q) {q : ℕ} (hq : q.Prime) (hg : l.GoodAt q) (Z : Comp Xo c) {K : Type}
    [Field K] [NumberField K] (j : c.F →+* K) (z : Sp K ⟶ Xo.XF c) (hz : z ≫ strK = spMap j)
    (hZ : ∀ p, z p ∈ (Z : Set (Xo.XF c))) (w : HeightOneSpectrum (𝓞 c.F)) (hw : ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (hv : ∀ a : c.F, vLa 𝔭 (j a) = vLa w a) :
    ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y' : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y' := by
  classical
  obtain ⟨T, k, hk, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K 𝔭
  have ho : OverLa w T.V (k.comp j) 1 := ⟨Nat.one_pos, fun a => by rw [← hv a]; exact hk.2 _⟩
  have hqT : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    rw [← GlobalTheory.PlaceCompletion.valV_algebraMap_lt_one_iff (K' := T.Fr), map_natCast, ← map_natCast (k.comp j),
      GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho, pow_one, ← map_natCast (algebraMap (𝓞 c.F) c.F)]
    exact (w.valuation_lt_one_iff_mem _).2 hw
  obtain ⟨O, _, β, Y, hPI, b, hb⟩ := GlobalTheory.exists_model_pushInvertible_under_cdvr GlobalTheory.partI_closed
    GlobalTheory.Moduli.moduli_scheme_exists E H Dw l Xo c hpq T (k.comp j) q hq hqT hg
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hIF : IntFramesSt Xo c := GlobalTheory.intFrames_of_laws GlobalTheory.abelianSchemeLaws_all.1.secBaseChange hT E H Dw l Xo c
  let _ := (k.comp j).toAlgebra
  have hs : (spMap k ≫ z) ≫ Limits.pullback.snd _ _ = spMap (k.comp j) := by
    rw [Category.assoc, ← GlobalTheory.EtaVal.spMap_comp_spMap]
    exact congrArg _ hz
  have hx : ((spMap k ≫ z) ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, GlobalTheory.EtaVal.spMap_comp_spMap]
    rfl
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) _ hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y', t, hbor⟩ := intFr_of_model hIF T (k.comp j) Y hPI b hb y₀
  refine ⟨T, k.comp j, y', ho, hfin, fun p => ?_⟩
  have h1 : y'.1.x = y₀.x := hbor.1
  have h2 : ptF y'.1 = spMap k ≫ z := by
    apply Limits.pullback.hom_ext
    · exact (Limits.pullback.lift_fst _ _ _).trans (h1.trans h0)
    · exact (Limits.pullback.lift_snd _ _ _).trans hs.symm
  rw [h2]
  exact hZ (spMap k p)

end Integral

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open AlgebraicGeometry CategoryTheory

theorem unramPts : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → UnramPts Xo c (badPrimes H l) := by
  intro hA hG hR E _ _ _ H Dw l Xo c hD
  refine UnramPts.of_index_one fun Z w hw => ?_
  obtain ⟨q, hq, hqw⟩ : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal := by
    have gen : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 c.F) ∈ w.asIdeal → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 c.F) ∈ w.asIdeal := by
      intro n
      induction n using Nat.recOnMul with
      | zero => exact fun h => absurd rfl h
      | one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) w.isPrime.ne_top
      | prime p hp => exact fun _ h => ⟨p, hp, h⟩
      | mul a b ha hb =>
        intro h0 h
        rw [Nat.cast_mul] at h
        exact (w.isPrime.mem_or_mem h).elim (ha (left_ne_zero_of_mul h0)) (hb (right_ne_zero_of_mul h0))
    exact gen _ (fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _)
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hb : ¬ q ∣ 2 * H.d * (discr E).natAbs * l.M' := fun h => hw q (Nat.mem_primeFactors.2 ⟨hq, h,
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero)
      (Int.natAbs_ne_zero.mpr (discr_ne_zero E))) hM⟩) hqw
  have hqM : ¬ q ∣ l.M' := fun h => hb (h.mul_left _)
  have hg : l.GoodAt q := by
    have h0 : l.M.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun h => hqM (h.trans (Nat.dvd_lcm_left _ _))
    rw [Level.GoodAt, h0, pow_zero, Nat.div_one]
    exact l.three_le
  obtain ⟨N, x, hN, hx, hZ, hfix⟩ := exists_fixed_point hD hq (fun h => hb (h.mul_right _)) Z
  obtain ⟨F', _, hF, hC⟩ := exists_curveOver hA hG hR H (n := N * l.M') hq
    (fun h => (hq.dvd_mul.1 h).elim hN hqM) (fun h => hb (((h.mul_left _).mul_right _).mul_right _))
  haveI := c.fin
  haveI : NumberField (c.F ⊔ F' : IntermediateField ℚ ℂ) := ⟨⟩
  have hle : c.F ≤ c.F ⊔ F' := le_sup_left
  obtain ⟨𝔭, h𝔭⟩ := GlobalTheory.UnramCompositum.exists_vLa_eq c.F F' _ hle rfl q hq hF w hqw
  obtain ⟨g, rfl⟩ := GlobalTheory.FixedPoint.exists_descent (c.F ⊔ F') x fun τ hτ =>
    hfix τ (fun a ha => hτ a (hle ha)) (hC τ fun a ha => hτ a (le_sup_right (a := c.F) ha))
  refine exists_intFr hD hq hg Z (IntermediateField.inclusion hle).toRingHom g ?_ (fun s => ?_) w hqw 𝔭 h𝔭
  · rw [Category.assoc, ← Spec.map_preimage (g ≫ strK), ← Spec.map_comp] at hx
    rw [← Spec.map_preimage (g ≫ strK)]
    congr 1
    ext a
    exact congrArg (fun f => f.hom a) (Spec.map_injective hx)
  · obtain ⟨p⟩ : Nonempty (Sp ℂ) := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)⟩
    have h := hZ p
    rw [Scheme.Hom.comp_apply] at h
    have e : s = _ := Subsingleton.elim (α := PrimeSpectrum (c.F ⊔ F' : IntermediateField ℚ ℂ)) s
      (spMap (algebraMap (c.F ⊔ F' : IntermediateField ℚ ℂ) ℂ) p)
    exact e ▸ h

end GlobalTheory.UnramPoint
