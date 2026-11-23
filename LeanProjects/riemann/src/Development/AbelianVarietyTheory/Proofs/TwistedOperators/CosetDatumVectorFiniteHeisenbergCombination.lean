import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPairWeilLatticeIffStandardOfHalfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfCosetRepresentativesCardDvdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLatticeCharSumDetectsNsmulMultipleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx.FourierSelfDualModel

open GlobalTheory.RowTest GlobalTheory.FunObj Formalism.IndefR.Datum

theorem stdSelfDual {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {U : Set T}
    (N : Std G U) {p : Pair T} (hp : DefPair D.R.m p) :
    IsSelfDualC (G.pS p) (N.latS p) ∧ IsSelfDualC (G.pT p) (N.latT p) := by
  obtain ⟨h1, h2⟩ := hp.nodes
  rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
  · exact ⟨isSelfDualC_neg (N.selfDual h2), N.selfDual h1⟩
  · exact hp.elim
  · exact hp.elim
  · exact ⟨N.selfDual h1, N.selfDual h2⟩

theorem pow_psi_eq_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ)
    (hLL : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
    {x y : WO S T} (hx : IsHalf e x) (hkx : k • x ∈ Λ) (hy : IsHalf (cA D e) y) (hky : k • y ∈ Λ) :
    ψ (symplOH S T x y) ^ (2 * k * k) = 1 := by
  have hl : ∀ (m : ℕ) (a b : WO S T), symplOH S T (m • a) b = m • symplOH S T a b := fun m a b => by
    induction m with
    | zero => simp [GlobalTheory.FinTranslate.symplOH_zero_left]
    | succ m ih => rw [succ_nsmul, GlobalTheory.FinTranslate.symplOH_add_left, ih, succ_nsmul]
  have hr : ∀ (m : ℕ) (a b : WO S T), symplOH S T a (m • b) = m • symplOH S T a b := fun m a b => by
    induction m with
    | zero => simp [GlobalTheory.FinTranslate.symplOH_zero_right]
    | succ m ih => rw [succ_nsmul, GlobalTheory.FinTranslate.symplOH_add_right, ih, succ_nsmul]
  have h2 : ∀ a b : WO S T, symplOH S T a b + symplOH S T a b = symplO S T a b := fun a b => by
    unfold symplOH
    rw [← add_mul, ← map_add]
    norm_num
  have e1 : (2 * k * k) • symplOH S T x y = symplO S T (k • x) (k • y) := by
    rw [← h2, hl, hr, ← two_nsmul, ← mul_nsmul, ← mul_nsmul]
    ring_nf
  rw [← AddChar.map_nsmul_eq_pow, e1]
  exact hLL _ hkx (isHalf_nsmul_of k hx) _ hky (isHalf_nsmul_of k hy)

theorem mem_qbar_of_pow {z : ℂ} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  have hi : IsIntegral ℚ z := IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)
  exact mem_algebraicClosure_iff.2 hi.isAlgebraic

set_option maxHeartbeats 1600000 in
open Classical in

theorem model_coset {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (e : AE D) (P : Finset (Pl D.host.E))
    (he : IsIdemSum e P) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm)
    (k : ℕ) (hk : 0 < k) (x₀ : WO S T) (hx₀ : IsHalf e x₀)
    (hkx : k • x₀ ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    ∃ (n : ℕ) (c : Fin n → Formalism.MainNotions.TaylorLogMetric.Qbar) (w : Fin n → WO S T),
      (∀ i, k • w i ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧
      (∀ i, (w i).map (infPart D) = 0) ∧
      (∀ i, IsIntegral ℤ ((k : Formalism.MainNotions.TaylorLogMetric.Qbar) ^ (D.R.f * S.rank * T.rank) * c i)) ∧
      (∀ ρ : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ, ∑ i, ‖ρ (c i)‖ ≤ 1) ∧
      Tm ((halfCoset e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
        k x₀).indicator 1) = ∑ i, (c i : ℂ) • heisO ψ S T (w i) f₀ := by
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hinfc := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hLL : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1 :=
    fun u hu hu' y hy _ => ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1 u (GlobalTheory.PlaceDatum.infPart_of_half hinf hu')).1 hu y hy
  have hdual : ∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ := by
    intro x hx h
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1 x
      (GlobalTheory.PlaceDatum.infPart_of_half hinf hx)).2 fun u hu => ?_
    have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
    have hec : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
    have hcu : IsHalf (cA D e) (cA D e • u) := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hec]
    have := h _ (GlobalTheory.SplitScalar.idem_smul_mem hec u hu) hcu
    rwa [← GlobalTheory.PlaceModel.symplO_smul, show e • x = x from Matrix.ext fun i j => hx i j] at this
  obtain ⟨R, hR1, hR2, hRd⟩ := GlobalTheory.T.exists_halfCosetRepresentatives_card_dvd S T ΛS ΛT hS hT e P he k hk
  have hsum := GlobalTheory.T.halfLattice_charSum_detects_nsmul_multiple ψ S T Λ e k R hk hLL hdual hR1 hR2
  have hcard : R.card ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hRd
    exact pow_ne_zero _ hk.ne' hRd
  have hcardC : (R.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hcard
  set Ψ : WO S T → ℂ := (halfCoset e Λ k 0).indicator 1 with hΨdef
  have hmem0 : ∀ t, t ∈ halfCoset e Λ k 0 ↔ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u := fun t => by
    simp only [halfCoset, Set.mem_setOf_eq, zero_add]
  have hΨ : Ψ = (R.card : ℂ)⁻¹ • ∑ r ∈ R, (fun t => ψ (symplO S T t r) * halfInd e Λ t) := by
    funext t
    rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    by_cases ht : t ∈ Λ ∧ IsHalf e t
    · have h1 : halfInd e Λ t = 1 := if_pos ht
      simp only [h1, mul_one]
      by_cases hm : ∃ u ∈ Λ, IsHalf e u ∧ t = k • u
      · rw [(hsum t ht.1 ht.2).1 hm, inv_mul_cancel₀ hcardC, hΨdef, Set.indicator_of_mem ((hmem0 t).2 hm)]
        rfl
      · rw [(hsum t ht.1 ht.2).2 hm, mul_zero, hΨdef, Set.indicator_of_notMem (fun h => hm ((hmem0 t).1 h))]
    · have h1 : halfInd e Λ t = 0 := if_neg ht
      simp only [h1, mul_zero, Finset.sum_const_zero]
      rw [hΨdef, Set.indicator_of_notMem]
      intro h
      obtain ⟨u, hu, hu', rfl⟩ := (hmem0 t).1 h
      exact ht ⟨nsmul_mem hu k, isHalf_nsmul_of k hu'⟩
  have hΨsb : IsSBHalf e Λ Ψ := isSBHalf_halfCoset_indicator hk (fun i j => mul_zero _) (by simp)
  have hind : (halfCoset e Λ k x₀).indicator (1 : WO S T → ℂ) = fun t => Ψ (t + -x₀) := by
    funext t
    have hiff : t ∈ halfCoset e Λ k x₀ ↔ t + -x₀ ∈ halfCoset e Λ k 0 := by
      rw [hmem0]
      simp only [halfCoset, Set.mem_setOf_eq]
      refine exists_congr fun u => and_congr_right fun _ => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
      · rw [h]; abel
      · rw [← h]; abel
    by_cases h : t ∈ halfCoset e Λ k x₀
    · rw [Set.indicator_of_mem h, hΨdef, Set.indicator_of_mem (hiff.1 h)]
      rfl
    · rw [Set.indicator_of_notMem h, hΨdef, Set.indicator_of_notMem (fun h' => h (hiff.2 h'))]
  have hvac : Tm (halfInd e Λ) = f₀ := by
    have := hTm.vac
    rwa [one_smul] at this
  have hTΨ : Tm Ψ = (R.card : ℂ)⁻¹ • ∑ r ∈ R, heisO ψ S T r f₀ := by
    rw [hΨ, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [hTm.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) r (hR1 r hr).1, hvac]
  have hnx : IsHalf e (-x₀) := fun i j => by rw [Matrix.neg_apply, mul_neg, hx₀ i j]
  have hneg : k • -x₀ = -(k • x₀) := by
    rw [eq_neg_iff_add_eq_zero, ← nsmul_add, neg_add_cancel, nsmul_zero]
  have hmain : Tm ((halfCoset e Λ k x₀).indicator 1) =
      ∑ r ∈ R, ((R.card : ℂ)⁻¹ * ψ (symplOH S T (-x₀) r)) • heisO ψ S T (-x₀ + r) f₀ := by
    rw [hind, hTm.trans Ψ hΨsb (-x₀) hnx, hTΨ]
    have hlin : heisO ψ S T (-x₀) ((R.card : ℂ)⁻¹ • ∑ r ∈ R, heisO ψ S T r f₀) =
        (R.card : ℂ)⁻¹ • ∑ r ∈ R, heisO ψ S T (-x₀) (heisO ψ S T r f₀) := by
      funext t
      simp only [heisO, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    rw [hlin, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [GlobalTheory.FinTranslate.heisO_heisO, smul_smul]

  have hroot : ∀ r ∈ R, ψ (symplOH S T (-x₀) r) ^ (2 * k * k) = 1 := fun r hr =>
    pow_psi_eq_one ψ S T Λ e k hLL hnx (by rw [hneg]; exact neg_mem hkx)
      (hR1 r hr).1 (hR1 r hr).2
  have hN : 0 < 2 * k * k := by positivity
  let ζ : R → Formalism.MainNotions.TaylorLogMetric.Qbar := fun r => ⟨ψ (symplOH S T (-x₀) r.1), mem_qbar_of_pow hN (hroot r.1 r.2)⟩
  have hζ : ∀ r, ζ r ^ (2 * k * k) = 1 := fun r => Subtype.ext (by
    show (ψ (symplOH S T (-x₀) r.1)) ^ (2 * k * k) = 1
    exact hroot r.1 r.2)
  let cc : R → Formalism.MainNotions.TaylorLogMetric.Qbar := fun r => (R.card : Formalism.MainNotions.TaylorLogMetric.Qbar)⁻¹ * ζ r
  have hcc : ∀ r, (cc r : ℂ) = (R.card : ℂ)⁻¹ * ψ (symplOH S T (-x₀) r.1) := fun r => by
    simp [cc, ζ]
  obtain ⟨m, hm⟩ := hRd
  refine ⟨R.card, fun i => cc (R.equivFin.symm i), fun i => -x₀ + (R.equivFin.symm i).1, fun i => ?_, fun i => ?_,
    fun i => ?_, fun ρ => ?_, ?_⟩
  · rw [nsmul_add]
    refine add_mem ?_ (hR1 _ (R.equivFin.symm i).2).2
    rw [hneg]
    exact neg_mem hkx
  · have h1 := GlobalTheory.PlaceDatum.infPart_of_half hinf hnx
    have h2 := GlobalTheory.PlaceDatum.infPart_of_half hinfc (hR1 _ (R.equivFin.symm i).2).1
    ext a b
    have e1 : infPart D ((-x₀) a b) = 0 := by
      have := congrFun (congrFun h1 a) b
      rwa [Matrix.map_apply, Matrix.zero_apply] at this
    have e2 : infPart D ((R.equivFin.symm i).1 a b) = 0 := by
      have := congrFun (congrFun h2 a) b
      rwa [Matrix.map_apply, Matrix.zero_apply] at this
    rw [Matrix.map_apply]
    dsimp only
    rw [Matrix.add_apply, RingHom.map_add, e1, e2, add_zero, Matrix.zero_apply]
  · have hc0 : ((R.card : ℕ) : Formalism.MainNotions.TaylorLogMetric.Qbar) ≠ 0 := Nat.cast_ne_zero.2 hcard
    have e1 : (k : Formalism.MainNotions.TaylorLogMetric.Qbar) ^ (D.R.f * S.rank * T.rank) * cc (R.equivFin.symm i) =
        (m : Formalism.MainNotions.TaylorLogMetric.Qbar) * ζ (R.equivFin.symm i) := by
      simp only [cc]
      rw [← Nat.cast_pow, hm, Nat.cast_mul, ← mul_assoc, mul_comm ((R.card : ℕ) : Formalism.MainNotions.TaylorLogMetric.Qbar), mul_assoc (m : Formalism.MainNotions.TaylorLogMetric.Qbar),
        mul_inv_cancel₀ hc0, mul_one]
    rw [e1]
    have hm' : IsIntegral ℤ ((m : ℕ) : Formalism.MainNotions.TaylorLogMetric.Qbar) := by
      have := isIntegral_algebraMap (R := ℤ) (A := Formalism.MainNotions.TaylorLogMetric.Qbar) (x := (m : ℤ))
      rwa [map_natCast] at this
    exact hm'.mul (IsIntegral.of_pow hN (by rw [hζ]; exact isIntegral_one))
  · have h1 : ∀ r, ‖ρ (cc r)‖ = (R.card : ℝ)⁻¹ := fun r => by
      have hρ : ρ (ζ r) ^ (2 * k * k) = 1 := by rw [← map_pow, hζ, map_one]
      simp only [cc, map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, Complex.norm_natCast,
        Complex.norm_eq_one_of_pow_eq_one hρ hN.ne', mul_one]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_inv_cancel₀ (Nat.cast_ne_zero.2 hcard)]
  · rw [hmain, ← Finset.sum_coe_sort R, ← R.equivFin.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcc]

end GlobalTheory.RowEx.FourierSelfDualModel

open GlobalTheory.RowEx.FourierSelfDualModel in

theorem GlobalTheory.RowEx.fourierVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl G t → ∃ (n : ℕ) (c : Fin n → Formalism.MainNotions.TaylorLogMetric.Qbar) (w : Fin n → WO (G.pS p) (G.pT p)), (∀ i, k • w i ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True) ∧ (∀ i, (w i).map (infPart D) = 0) ∧ (∀ i, IsIntegral ℤ ((k : Formalism.MainNotions.TaylorLogMetric.Qbar) ^ (D.R.f * (G.pS p).rank * (G.pT p).rank) * c i)) ∧ (∀ ρ : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ, ∑ i, ‖ρ (c i)‖ ≤ 1) ∧ S.Z.vec d = ∑ i, (c i : ℂ) • heisO W.ψ (G.pS p) (G.pT p) (w i) (S.Z.vac p) := by
  intro D T L sc G W S t p hp k d hk hc hz hP
  obtain ⟨x₀, hx₀, hkx, hfn⟩ := hc
  have he : IsIdemSum d.e (locPl G t) := hP ▸ d.e_is
  have hag := GlobalTheory.T.mem_gridPairWeilLattice_iff_standard_of_half S t p hp d.e he
  have hcos : halfCoset d.e (pairLat G p) k x₀ = halfCoset d.e (latO (G.pS p) (G.pT p)
      (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) k x₀ := by
    ext x
    simp only [halfCoset, Set.mem_setOf_eq]
    exact exists_congr fun u => ⟨fun ⟨h1, h2, h3⟩ => ⟨(hag u h2).1 h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨(hag u h2).2 h1, h2, h3⟩⟩
  have hkx' := (hag _ (isHalf_nsmul_of k hx₀)).1 hkx
  have hsb : IsSBHalf d.e (latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E))
      (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) d.fn := by
    rw [hfn, hcos]
    exact isSBHalf_halfCoset_indicator hk hx₀ hkx'
  obtain ⟨hSd, hTd⟩ := stdSelfDual S.N hp
  have hv := S.Z.vac_is p hp
  obtain ⟨f, hf⟩ : ∃ f, d.IsTheta W (S.N.latS p) (S.N.latT p) (S.Z.vac p) f :=
    VecEx.exists_isThetaAt_of_vac hSd.1 hTd.1 hSd hTd d.e_is hv hsb
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := id hf
  have hfT : f = Tm d.fn := hall Tm hTm
  have hvec : S.Z.vec d = f := by
    rw [Normal.vec, FinDatum.vec_eq W hf, hz, Prod.mk_one_one, map_one]
    rfl
  obtain ⟨n, c, w, h1, h2, h3, h4, h5⟩ := model_coset W.ψ (G.pS p) (G.pT p) (S.N.latS p) (S.N.latT p) hv.1 hSd hTd d.e _
    d.e_is (S.Z.vac p) Tm hTm k hk x₀ hx₀ hkx'
  refine ⟨n, c, w, h1, h2, h3, h4, ?_⟩
  rw [hvec, hfT, hfn, hcos, h5]
