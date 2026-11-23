import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerIntAtOfSeriesRat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtLinearIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjIdempotentSumOverLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterQuotientValuesInEmbeddingFieldStatement

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.SerStd

theorem exists_of_mem_ratVec {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (i : Fin D.R.m) {c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W}
    {c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W} (hc : CoefficientBaseChange R i D.what₂.embLL (RingHom.id ℂ) c0L c0) (k : Subfield ℂ)
    {w : (R.cV i).W} (hw : w ∈ ratVec R i c0L k) :
    ∃ v : VsV D i ℂ, (∀ m, MvPolynomial.coeff m (v : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) ∈ k) ∧ w = c0 v := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨v', hv', e⟩ := hc v
    exact ⟨v', fun m => by rw [hv', MvPolynomial.coeff_map]; exact hv m, e.symm⟩
  | zero => exact ⟨0, fun m => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, fun m => by simpa using k.add_mem (ha m) (hb m), by simp⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨(c : ℂ) • a, fun m => ?_, ?_⟩
    · simpa using k.mul_mem c.2 (ha m)
    · rw [map_smul]; rfl

theorem sum_mem_ratForms {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {m : ℕ} (β : Fin m → ℂ) (fs : Fin m → Rul C.d.Xo₂ C.d.c₂)
    (hβ : ∀ k, β k ∈ C.σ₂.range) (hf : ∀ k, fs k ∈ C.cuspSec a n) :
    ∑ k, β k • C.rd a (fs k) ∈ C.ratForms a n := by
  choose b hb using fun k => RingHom.mem_range.1 (hβ k)
  refine ⟨∑ k, b k • fs k, ⟨sum_mem fun k _ => (sec _ _ _ _).smul_mem _ (hf k).1, ?_⟩, ?_⟩
  · rw [map_sum]
    exact sum_mem fun k _ => by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hf k).2
  · simp only [Cover.rd, map_sum, map_smulₛₗ, hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.id_apply, smul_comm]

set_option maxHeartbeats 2000000 in

theorem untwRatS : UntwRatS := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hG hFam hMod hTh hTie i hV hFP hstd gramR c0R c0L hFT u hu
  obtain ⟨c0, hc0, -⟩ := GlobalTheory.RationalValuesObj.existsUnique_c0BC R i D.what₂.embLL (RingHom.id ℂ) rfl (c0L i)
  have hcm : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 := ⟨gramR, c0R, c0L, hFT, hc0⟩
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
      ((D.host.level_coprimeS _ (D.host.g_level k)).mul_right (Nat.Coprime.of_dvd_right
        (Dvd.intro _ rfl |>.trans (show D.host.q * (D.host.QS * D.host.d) ∣ D.host.QS * D.host.q * D.host.d from ⟨1, by ring⟩))
        (Nat.Coprime.symm (by rw [Nat.Coprime, Nat.gcd_rec, D.ntypes.g_cond k, Nat.gcd_one_left])))).mul_right
        (D.host.ccK_coprime _ (by simp [D.host.g_level k])).symm
    rw [hMg]
    exact (this 0).mul_left (this 1)
  obtain ⟨ph, hph, hbase⟩ := GlobalTheory.T.coreConstants_eq_vacuumIdentity_up_to_phase D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV hFP
  obtain ⟨ka, hka, J, hJH, hJk, hJ⟩ := GlobalTheory.T.harmonicMap_extremalVector_eq_phase_smul_letters D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd u hu c0 hcm lt hlt
  have hph0 : ph ≠ 0 := fun h => by simp [h] at hph
  have hka0 : ka ≠ 0 := fun h => by simp [h] at hka
  refine ⟨(ka * ph)⁻¹, by rw [norm_inv, norm_mul, hka, hph]; norm_num, fun C hC s hs f hf w hw => ?_⟩
  obtain ⟨hU, hpin, hAux, hSmall, -⟩ := hC
  obtain ⟨v, hvk, rfl⟩ := exists_of_mem_ratVec R i hc0 _ hw
  have hM₂ : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hpd0 : 0 < C.d.pd := hAux.1.pos
  obtain ⟨l, hlge, hl⟩ := Nat.exists_infinite_primes (C.d.pd + 1)
  have hcl : Nat.Coprime C.d.pd l :=
    ((Nat.Prime.coprime_iff_not_dvd hl).2 fun h => by have := Nat.le_of_dvd hpd0 h; omega).symm
  obtain ⟨c₂, hc₂⟩ := series_bound hP (rank_Wc i) hodd hχ hM₀ hpq hΨ hB hlt hDom hLast hl hs
  obtain ⟨hD, hF, hrel, hσ⟩ := GlobalTheory.T.uniformisedCover_isDictionary_frameCompatible D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV C hU
  have hcc := GlobalTheory.T.vacuumIdentityConstants_cover_of_dominantPins D G Pl0 T0 A T R F κ v₀ hL hLev hG hFam hMod hTh hTie i hstd hV ph hph hbase C hU hpin
  have hgood : C.d.l₂.GoodAt l := goodAt_of_dvd hl hM₂ hcl
    (Formalism.L2.Pj.goodAt_of_two_primes hMg (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl)
  have hval := GlobalTheory.T.character_quotient_values_in_embedding_field D G Pl0 T0 A T.Q.c.F R i C.d.c₂.F C.σ₂ hSmall
  obtain ⟨P, e, Φ, he, hPM, hsupp, hper, hΦk, hth⟩ := hf
  obtain ⟨e', P', he', hPM', hce⟩ := GlobalTheory.T.exists_conj_idempotentSum_over_level D _ e P he hPM
  obtain ⟨la, hla⟩ := exists_place_over C.d.c₂.F hl
  have hθf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f :=
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hPr.weil.std hPr.inf hth hvac.2.theta
  have hfld : ∀ x ∈ T.Q.c.F, x ∈ C.σ₂.fieldRange := fun x hx => ⟨C.inc ⟨x, hx⟩, RingHom.congr_fun hU.2.2.1 ⟨x, hx⟩⟩
  have hQO : ∀ mo, (J v).coeff mo ∈ C.σ₂.range := fun mo =>
    RingHom.mem_range.2 (RingHom.mem_fieldRange.1 (hJk C.σ₂.fieldRange hfld v hvk mo))
  have hΦO : ∀ x, Φ x ∈ C.σ₂.range := fun x => RingHom.mem_range.2 (RingHom.mem_fieldRange.1 (hΦk x))
  have hPM₂ : ∀ PP ∈ P', ((C.d.l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by rw [hM₂]; exact hPM'
  have hfn : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e') (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) C.d.l₂.M Φ := by
    rw [hce, hM₂]; exact ⟨hsupp, hper⟩
  have hth' : IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e')
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) Φ f := by rw [hce]; exact hth
  obtain ⟨m, β, fs, hfs, hsum⟩ := hc₂ C.d.l₂ C.d.pd C.d.Xo₂ C.d.c₂ C.σ₂ C.U₂ _ _ _ _ _ hM₂ hU.1.2.2.1 hcl
    (hM₂ ▸ hMb.mul_left hAux.2.2.2.2) hU.2.1 hgood hrel hσ hD hF hcc hval la C.σ₂.range hla (valRing_range _ _) e' P' Φ f he'
    hPM₂ hfn hΦO hth' (J v) (hJH v) hQO
  let Fn : GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ := castDict hV.symm fun g =>
    (l : ℂ) ^ c₂ * ((ka * ph)⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series R i u s f (c0 v) g)
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
  have hR : IsRat T i hV C (κ i) (castDict hV Fn) := by
    refine ⟨Fn, ?_, rfl⟩
    rw [e1]
    refine sum_mem_ratForms C _ _ β fs (fun k => (hfs k).1) fun k => ?_
    rw [hn]; exact ⟨(hfs k).2.1, (hfs k).2.2.1⟩
  have hl0 : ((l : ℂ) ^ c₂) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  have h2 := GlobalTheory.SerRatRay.isRat_const_mul T i hV C (κ i) _ ((l : ℂ) ^ c₂)⁻¹ hR
    ⟨((l : C.d.c₂.F) ^ c₂)⁻¹, by simp⟩
  convert h2 using 1
  funext g
  show _ = ((l : ℂ) ^ c₂)⁻¹ * castDict hV (castDict hV.symm _) g
  rw [castDict_symm, inv_mul_cancel_left₀ hl0]
  rfl

end GlobalTheory.SerStd

end
