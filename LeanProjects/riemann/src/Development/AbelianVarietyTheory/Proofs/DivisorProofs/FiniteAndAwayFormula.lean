import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotLeafMMZero
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.SigmaMonoInConstant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField

namespace LeafFixedPointPairing
section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw matLat)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.IndefR.Datum Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

namespace GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_localization_of_smul_mem₂ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    (M : Submodule (𝓞 K) (Fin n → K)) (y : Fin n → K) (s : K) (hs : s ≠ 0) (δ : ℤ) (hv : vw w s ≤ δ) (h : s • y ∈ M) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
      (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-δ) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M) := by
  obtain ⟨t, ht, hc⟩ := unit_at_val w s hs
  have h1 : s • y ∈ Formalism.HermitianLatticesTheory.idealSmul
      (((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) : Submodule (𝓞 K) K) M := by
    refine Submodule.subset_span ⟨1, ?_, s • y, h, (one_smul _ _).symm⟩
    exact FractionalIdeal.mem_coe.mpr (FractionalIdeal.one_mem_one _)
  have hm := smulK_mem_idealSmul _ _ M _ hc h1
  rw [one_mul] at hm
  have e : (algebraMap (𝓞 K) K t * s⁻¹) • s • y = t • y := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one, algebraMap_smul]
  rw [e] at hm
  exact GlobalTheory.FinitePlacesCompare.scaledAt_anti w M (neg_le_neg hv)
    ((PI.LocGlobInclWork.mem_localization_iff _ _ _).mpr ⟨t, ht, hm⟩)

variable {D : D7}

theorem absNorm_splitAuxiliaryPlace_eq_prime {T : Type} {Lc : LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) :
    Ideal.absNorm P.v0.asIdeal = GlobalTheory.ChiGrid.q0 D := by
  have hp := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  have h : (Ideal.primesOver (Ideal.span {((GlobalTheory.ChiGrid.q0 D : ℕ) : ℤ)}) (𝓞 D.host.E)).ncard =
      Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact Formalism.L2.Host.split_prime_splits_completely D
  have := P.v0.isPrime
  have := (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) (E := D.host.E) hp h P.v0.asIdeal P.basePlace_over_qZero).2
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact this

theorem one_le_b (s : Formalism.BasicNotions.Scale) : 1 ≤ s.b := by
  have h : 0 ≤ s.L := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  exact Real.one_le_exp h

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem sig_le {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hC : CF ≤ C) :
    sig d.G ≤ (d.data (fun _ => 1) Tf dF).Sig0 C p.Z.b := by
  have hb : 1 ≤ p.Z.b := one_le_b L.sc
  refine le_trans (le_of_eq ?_) (GlobalTheory.FinitePlacesProbe.sigma_mono_in_constant _ hC hb)
  show _ = ∑ q ∈ d.G.pl.S0, ((d.O.ee CF p.Z.b q : ℕ) : ℝ) * Real.log (Ideal.absNorm q.asIdeal)
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [GlobalTheory.BigTop.Fun.Model.ee_eq d (absNorm_splitAuxiliaryPlace_eq_prime d.G.pl) v]

theorem local_clause {p : PtAt ex Csz} {CF : ℝ} {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (hT : TieAt d a)
    {dl : GlobalTheory.SumSize.PlL D → ℝ} (hloc : ∀ X' M, IsTestLat a.ch.G a.ch.rp a.ch.n a.ch.e X' M →
      ∀ t w, Away a.ch.G t w → ∀ x ∈ (p.P.A3.A.fam.R t).Mt (p.P.A3.A.fam.lvl p.F.lv2.P0 p.F.lv2.ψ0), ∀ y : Fin a.ch.n → D.what₂.LL,
        (∀ i, D.what₂.embLL (y i) = vK a.ch t (formOf p.F.lv2 t x) i) → ∃ s : D.what₂.LL, s ≠ 0 ∧ (vw w s : ℝ) ≤ dl w ∧ s • y ∈ M)
    (hAw : AwayAt (R := p.R.toRealDat) a.ch) (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hF : ∀ w, dF w = ⌊dl w⌋) (w : GlobalTheory.SumSize.PlL D) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ((d.data (fun _ => 1) Tf dF).vmu ((p.S false).μ w)) ((Df p).Mt ((p.S false).μ w))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-((d.data (fun _ => 1) Tf dF).dF w)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (d.data (fun _ => 1) Tf dF).M) := by
  intro z hz
  obtain ⟨s0, hs0, hz0⟩ := (PI.LocGlobInclWork.mem_localization_iff _ _ _).mp hz
  obtain ⟨x, hx, hxz⟩ := Submodule.mem_map.mp hz0
  have e0 : (d.data (fun _ => 1) Tf dF).vmu ((p.S false).μ w) = d.V ((p.S false).μ w) := by
    show (1 : D.what₂.LL)⁻¹ • d.V _ = _
    simp
  simp only [LinearMap.coe_restrictScalars, e0] at hxz
  obtain ⟨s, hs, hv, hsM⟩ := hloc d.X' d.M hT.test ((p.S false).μ w) w (hAw w) x hx (d.V _ |>.mulVec x)
    (fun i => hT.sums _ (Or.inr ⟨w, rfl⟩) x i)
  have hy := mem_localization_of_smul_mem₂ w d.M _ s hs (dF w) (by rw [hF]; exact Int.le_floor.mpr hv) hsM
  obtain ⟨s1, hs1, h1⟩ := (PI.LocGlobInclWork.mem_localization_iff _ _ _).mp hy
  refine (PI.LocGlobInclWork.mem_localization_iff _ _ _).mpr ⟨s1 * s0, w.asIdeal.primeCompl.mul_mem hs1 hs0, ?_⟩
  rw [mul_smul, ← hxz]
  exact h1

theorem sum_clause {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (hC0 : 0 ≤ C) (hC : CF ≤ C) {dl : GlobalTheory.SumSize.PlL D → ℝ}
    (hsum : ∀ s : Finset (GlobalTheory.SumSize.PlL D), ∑ w ∈ s, lw w * dl w ≤ D.R.m * bOne d.G C p.Z.b / 2)
    (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hF : ∀ w, dF w = ⌊dl w⌋) :
    2 * ∑ w ∈ Tf, lw w * (dF w : ℝ) ≤ (d.data (fun _ => 1) Tf dF).bFP C p.Z.b := by
  have hb : 1 ≤ p.Z.b := one_le_b L.sc
  have hb0 : 0 ≤ p.Z.b := by linarith
  have hL : 0 ≤ Real.log p.Z.b := Real.log_nonneg hb
  have h1 : ∑ w ∈ Tf, lw w * (dF w : ℝ) ≤ ∑ w ∈ Tf, lw w * dl w := by
    refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (GlobalTheory.FinitePlacesCompare.lw_nonneg w)
    rw [hF]
    exact Int.floor_le _
  have h2 := hsum Tf
  have hS := sig_le d Tf dF hC
  have hS0 := Sig0_nonneg (d.data (fun _ => 1) Tf dF) C p.Z.b
  have hN : (d.data (fun _ => 1) Tf dF).N = bigN D := GlobalTheory.BigTop.Fun.Model.N_eq d
  unfold FunData.bFP
  rw [hN]
  show _ ≤ C * (D.R.f : ℝ) * p.Z.b * (bigN D : ℝ) * (D.R.m : ℝ) * ((D.R.m : ℝ) * Real.log p.Z.b + (D.R.m : ℝ) * _) +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + _) * p.Z.b
  set S := (d.data (fun _ => 1) Tf dF).Sig0 C p.Z.b
  have h3 : 0 ≤ C * (D.R.f : ℝ) * p.Z.b * (bigN D : ℝ) * (D.R.m : ℝ) * ((D.R.m : ℝ) * Real.log p.Z.b + (D.R.m : ℝ) * S) := by
    positivity
  have h4 : (D.R.m : ℝ) * bOne d.G C p.Z.b ≤ C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + S) * p.Z.b := by
    unfold bOne
    have : (D.R.m : ℝ) * (C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + sig d.G) * p.Z.b) =
        C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + sig d.G) * p.Z.b := by ring
    rw [this]
    gcongr
  linarith

theorem leaf_at {p : PtAt ex Csz} {CF C : ℝ} {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (hT : TieAt d a) (hC0 : 0 ≤ C) (hC : CF ≤ C)
    (hFin : FinAt p.F.lv2 a.ch C p.Z.b) (hAw : AwayAt (R := p.R.toRealDat) a.ch) :
    ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b := by
  classical
  obtain ⟨dl, ⟨-, hfin, hsum⟩, hloc⟩ := hFin
  refine ⟨hfin.toFinset, fun w => ⌊dl w⌋, ?_, fun w hw => ?_, ?_⟩
  · exact local_clause hT hloc hAw _ _ (fun _ => rfl)
  · have hw' : w ∉ hfin.toFinset := hw
    have : dl w = 0 := by simpa using hw'
    show ⌊dl w⌋ = 0
    simp [this]
  · exact sum_clause d hC0 hC hsum _ _ (fun _ => rfl)

theorem fp_tie : SetAt → FinK → AwayK → FP @Comparison₂ := by
  intro hS hF hA
  obtain ⟨c1, hF⟩ := hF
  obtain ⟨c2, hA⟩ := hA
  refine ⟨max c1 c2, fun CF hCF => ?_⟩
  obtain ⟨C1, hF⟩ := hF CF ((le_max_left _ _).trans hCF)
  obtain ⟨C2, hA⟩ := hA CF ((le_max_right _ _).trans hCF)
  refine hS.imp fun {eps} Fm _ _ a _ => ⟨max (max C1 C2) (max CF 0), fun C hC => ?_⟩
  obtain ⟨x₁, a⟩ := a
  have hC1 : C1 ≤ C := ((le_max_left _ _).trans (le_max_left _ _)).trans hC
  have hC2 : C2 ≤ C := ((le_max_right _ _).trans (le_max_left _ _)).trans hC
  have hCF' : CF ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hC0 : 0 ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  obtain ⟨x₂, hF⟩ := hF eps C hC1
  obtain ⟨x₃, hA⟩ := hA eps C hC2
  refine ⟨max x₁ (max x₂ x₃), fun x hx hle i p hp d hd => ?_⟩
  obtain ⟨-, b, hT⟩ := hd
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hle
  have hx₂ : x₂ ≤ (Fm.L x i).sc.x := ((le_max_left _ _).trans ((le_max_right _ _).trans hle)).trans (Fm.L_x x i hx).ge
  have hx₃ : x₃ ≤ (Fm.L x i).sc.x := ((le_max_right _ _).trans ((le_max_right _ _).trans hle)).trans (Fm.L_x x i hx).ge
  have hset := a x hx hx₁ i p hp hT.ok.eser
  exact leaf_at hT hC0 hCF'
    (hF _ (Fm.L x i) (Fm.L_eps x i) hx₂ _ _ _ _ _ _ _ hset b.ch hT.ok.is b.atScale hT.ok.field)
    (hA _ (Fm.L x i) (Fm.L_eps x i) hx₃ _ _ _ _ _ _ _ hset b.ch hT.ok.is b.atScale hT.ok.field)

end GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm

end

end

end LeafFixedPointPairing
section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
theorem _root_.GlobalTheory.Adopt.finite_and_away_formula : SetAt → FinK → AwayK → FP @Comparison₂ := by
  first | exact @LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.fp_tie | exact LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.fp_tie | (intros; apply LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.fp_tie <;> assumption)

end
