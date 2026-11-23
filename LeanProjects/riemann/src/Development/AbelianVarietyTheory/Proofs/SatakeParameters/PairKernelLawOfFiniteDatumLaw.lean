import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LevelNeQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberBadPrimesNoConjugatePairStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOneStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KFiDat

theorem termLaw_of_xi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.X.Ok → IsSel t.X t.sel → (∀ i, t.Pr.g i ∈ t.S) → (∀ v, t.Pr.T v ∈ t.S) → (∀ l ∈ D.host.small, l ∈ t.S) → D.host.q ∈ t.S → (∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta) → ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K), gmap γ.1 ((t.rd u μ).N (i + 1) c') = (t.rd u μ).N (i + 1) c' → (∀ x, ∀ z ∈ mulLat (t.rd u μ).lev (homAt (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')), (t.rd u μ).Xi i c c' (x + z) = (t.rd u μ).Xi i c c' x) → (∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) * t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E)) = t.seam.σ₀ k * (t.rd u μ).Xi i c c' x) → TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
  intro D L hT Gi Gl K Y cX ex t hX hsel hgS hTS h2S hqS hTied u μ i hi c c' γ k hγ hΞ hXi
  obtain ⟨eta, hTied⟩ := hTied
  have hok := t.seam_ok
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  set z : t.X.E := ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) with hz
  have hz0 : z ≠ 0 := Units.ne_zero _
  have hSD' : IsSDLat D.host.E _ (t.seam.lat ((t.rd u μ).N (i + 1) c')) :=
    t.O_lat u μ (i + 1) c' ▸ ((t.O u μ).lat (i + 1) c').2
  obtain ⟨hzs, hzi, hprod1⟩ := GlobalTheory.T.det_unitaryStabiliser_selfDualLattice_normOne D t.X t.seam t.χ hok t.χ_ok _ _ hSD' γ hγ
  let eZ : Fin D.R.m → t.X.Tau → ℤ := fun j τ => (D.chTw u μ).sDiv j (t.seam.iT τ) + ((D.R.N j / 2 : ℕ) : ℤ)
  have heZ : ∀ j τ, ((eZ j τ : ℤ) : ℚ) = (D.hc (t.seam.iT τ)).e j := by
    intro j τ
    have h1 := (D.chTw u μ).sDiv_eq j j.2 (t.seam.iT τ)
    rw [D.hcW_e] at h1
    obtain ⟨m, hm⟩ := rank_even D.R j
    have h2 : ((D.R.N j / 2 : ℕ) : ℚ) = (D.R.N j : ℚ) / 2 := by
      rw [hm]; push_cast; rw [show m + m = 2 * m by ring, Nat.mul_div_cancel_left _ two_pos]; push_cast; ring
    simp only [eZ]
    rw [Int.cast_add, h1, Int.cast_natCast, h2, sExp, Nat.add_sub_cancel]
    ring
  have hTied' : t.Ch.Tied t.glob.σ₀ (fun j τ => ((eZ j τ : ℤ) : ℚ)) t.glob.mu0 eta := by
    have e : (fun j τ => ((eZ j τ : ℤ) : ℚ)) = (fun j τ => (D.hc (t.seam.iT τ)).e j) := funext fun j => funext fun τ => heZ j τ
    rw [e]; exact hTied
  have hP := GlobalTheory.NormOneUnit.prod_muAt t.Ch t.sel (t.tup μ) (t.cst μ) t.glob.σ₀ eZ t.glob.mu0 eta hX t.pr_ok hsel hgS
    (GlobalTheory.T.columnField_ramificationIdxIn_eq_one D t.X t.seam hX hok) hTied' ⟨i, hi⟩ z hzs hzi
  rw [t.glob_σ] at hP
  set M := t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P z) with hMdef
  have hw0 : ∀ τ, t.X.embC t.seam.σ₀ τ z ≠ 0 := fun τ => (map_ne_zero _).2 hz0
  have hP' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(eZ ⟨i, hi⟩ τ)) := hP
  have hM0 : M ≠ 0 := by
    rw [hP']
    exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hw0 τ)
  have hk : ∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) = (t.seam.σ₀ k / M) * (t.rd u μ).Xi i c c' x := by
    intro x
    have := hXi x
    field_simp
    linear_combination this
  have hA : TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) := by
    rw [← t.O_lat, ← t.O_lat]
    exact ⟨rank_even _ _, rank_even _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  have hSSc : ∀ P ∈ (t.rd u μ).SS, conjPrime₂ P ∉ (t.rd u μ).SS := by
    rw [hSS]
    exact GlobalTheory.T.memberBadPrimes_no_conjugatePair t.sel (t.tup μ) hX t.pr_ok hsel (t.word u) (hTS _) hgS
  have h2q : ∀ P ∈ (t.rd u μ).SS, ((D.host.QS : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal ∧ ((D.host.q : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
    intro P hP
    rw [hSS] at hP
    obtain ⟨p, hp, hpP, hk⟩ := sall_nat t.sel (t.tup μ) t.pr_ok hsel (t.word u) hP
    have hp2 : p ∉ D.host.small ∧ p ≠ D.host.q := by
      rcases hk with e | ⟨j, e⟩ | hn
      · rw [e, t.T_rec]; exact ⟨UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u), D.T_ne_q u⟩
      · rw [e, t.g_rec]; exact ⟨UpperTheory.Ram.g_notMem_small D j, GlobalTheory.ShortOwnCompare.level_ne_q D j⟩
      · exact ⟨fun e => hn (h2S _ e), fun e => hn (e ▸ hqS)⟩
    have key : ∀ l : ℕ, l.Prime → l ≠ p → ((l : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
      intro l hl hlp hlP
      have hc : IsCoprime ((p : ℕ) : 𝓞 t.X.E) ((l : ℕ) : 𝓞 t.X.E) := by
        have h1 := (Nat.coprime_primes hp hl).2 (Ne.symm hlp)
        have h2 := (Nat.isCoprime_iff_coprime.2 h1).map (Int.castRingHom (𝓞 t.X.E))
        simpa using h2
      obtain ⟨a, b, hab⟩ := hc
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (P.asIdeal.mul_mem_left a hpP) (P.asIdeal.mul_mem_left b hlP)))
    exact ⟨UpperTheory.Ram.natCast_notMem_of_coprime P.isPrime.ne_top hpP
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (UpperTheory.Small.not_dvd_QS D.host hp hp2.1)).symm, key _ D.host.hyp.1 hp2.2.symm⟩
  have hlev0 : 0 < (t.rd u μ).lev := by
    rw [hlev]
    exact modulus_pos t.sel (t.tup μ) (t.cst μ) (t.word u) (t.pr_ok.T_prime _).pos
  have key := GlobalTheory.KerLaw.thC_left_stab D t.X t.seam t.cc t.δ t.B t.χ t.cD hok t.cc_ok t.δ_ok t.χ_ok _ _ _ _ hA
    (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c') hlev0 hSSc h2q hΞ γ hγ _ hk
  have hdet : (matE t.seam γ.1).det = t.seam.iE z := by
    rw [matE]
    change ((t.seam.iE : t.X.E →+* D.host.E).mapMatrix (LinearMap.toMatrix' γ.1.toLinearMap)).det = _
    rw [← RingHom.map_det, LinearMap.det_toMatrix', hz, LinearEquiv.coe_det]
    rfl
  refine ⟨by rw [hdet]; exact (map_ne_zero _).2 hz0, t.seam.σ₀ k / M, fun w => ?_, ?_⟩
  · rw [t.O_Th]
    unfold KerRead.Th Seam.push
    refine (congrArg _ ?_).trans (key (fun τ => w (t.seam.iT τ)))
    funext τ
    refine congrArg (· * Matrix.of (w (t.seam.iT τ))) ?_
    ext a b
    simp only [matE, Matrix.map_apply]
    exact (hok.1 τ _).symm
  · show t.seam.σ₀ k = t.seam.σ₀ k / M * ∏ τ, TaylorLogMetric.embT D τ (matE t.seam γ.1).det ^ (-(D.chTw u μ).sDiv i τ)
    rw [hdet]
    have hw : ∀ τ, t.X.embC t.seam.σ₀ τ z = TaylorLogMetric.embT D (t.seam.iT τ) (t.seam.iE z) := fun τ => hok.1 τ z
    have hR : ∏ τ, TaylorLogMetric.embT D τ (t.seam.iE z) ^ (-(D.chTw u μ).sDiv i τ) =
        ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) :=
      (Fintype.prod_equiv t.seam.iT _ _ fun τ => by rw [hw]).symm
    have h1 : ∏ τ, t.X.embC t.seam.σ₀ τ z = 1 := by
      rw [← hprod1]
      exact Fintype.prod_equiv t.seam.iT _ _ fun τ => hw τ
    have hM' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) := by
      rw [hP']
      simp only [eZ]
      have e1 : ∀ τ, t.X.embC t.seam.σ₀ τ z ^ (-((D.chTw u μ).sDiv i (t.seam.iT τ) + ((D.R.N i / 2 : ℕ) : ℤ))) =
          t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) * t.X.embC t.seam.σ₀ τ z ^ (-((D.R.N i / 2 : ℕ) : ℤ)) :=
        fun τ => by rw [neg_add, zpow_add₀ (hw0 τ)]
      rw [Finset.prod_congr rfl fun τ _ => e1 τ, Finset.prod_mul_distrib, Finset.prod_zpow, h1, one_zpow, mul_one]
    rw [hR, ← hM']
    field_simp

end GlobalTheory.KFiDat
