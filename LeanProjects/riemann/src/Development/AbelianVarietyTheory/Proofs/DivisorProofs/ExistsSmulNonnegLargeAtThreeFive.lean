import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnfGroupContainsCongruenceUptoRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRuleAnyLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanShortGenUpto

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LargeCover

open IsDedekindDomain Formalism.MainNotions GlobalTheory.IntCuspLat

set_option maxHeartbeats 1000000 in

theorem exists_smul_nonneg_of_dvd (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o) (w : ℕ)
    (hw : ∀ (u : D.host.E) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n)
    (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n) (hla : ∀ σ k τ i, (w : ℤ) ∣ laU (Y.U σ) a n k τ i)
    (f : Rul Y.d.Xo₂ Y.d.c₂) (hf : f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n) :
    ∃ s : 𝓞 Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  let σ : Y.d.c₂.F →+* ℂ := Y.d.c₂.F.val.toRingHom
  have hσ : GoodEmb Y.d.c₂ σ := rfl
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hU : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) := (Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)
  have hpq : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := hU.1
  have hA : Y.d.l₂.A = 1 := hG.lev.2
  have hC := GlobalTheory.ChartFree.chartIndep
  have hP : ∀ k, PrincUpTo ((Y.U σ).X k) Y.d.l₂.M (laU (Y.U σ) a n k) := fun k =>
    princUpTo_of_root _ _ w hw _ (hla σ k)
      (GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _ _ hU hA hr k)
  obtain ⟨_, hW⟩ := hG.modelW σ hσ
  have hGm : ∀ k k', ((Y.U σ).X k).Gm = ((Y.U σ).X k').Gm ∧ ((Y.U σ).X k).ξ0 = ((Y.U σ).X k').ξ0 :=
    fun k k' => ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  have hχ := fun k => hG.chiTriv σ hσ a n hdom k
  have hf' := (mem_cusp _ _ _ a n f).1 hf
  have h1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := hpq ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n := by
    have h0 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have : D.R.r ≤ Module.finrank ℚ D.host.E * D.R.r := Nat.le_mul_of_pos_left _ h0
    omega
  have hd : ∃ d : DeltaDat Y.d.Xo₂ Y.d.c₂ n, d.IsLev ∧ (∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧
      d.cδ = 1 ∧ d.pd = 1 ∧ d.l₂.A = Y.d.l₂.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ Y.d.Xo₂ Y.d.c₂ h1 n 1 ⊤ Y.d.l₂ Y.d.Xo₂ Y.d.c₂ rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL _ _ _ _ Y.d.Xo₂ Y.d.c₂
  have hone : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y = 1 :=
    fun k _ _ y => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
  have hunit : GlobalTheory.Dict.UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : Y.d.c₂.Fˣ) : Y.d.c₂.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [hone K y, hone K y']
    simp
  have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ σ
    D.R.r _ hU a n).1
  refine exists_smul_nonneg_of_span (fun la => isVal_valSet la)
    (fun b => shortGen Y.d.Xo₂ Y.d.c₂ nab b 0 a n d) (fun b hb => ?_) fun b hb g hg => ?_
  · have htot : ShortValTot Y.d.Xo₂ Y.d.c₂ nab b 0 a n d :=
      GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d (GlobalTheory.levelMaps_closed hL _ _ _ h1)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ Y.d.Xo₂ Y.d.c₂).2.2.1
        (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ Y.d.Xo₂ Y.d.c₂)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
        nab b 0 a
    have hsp := holSub0_le_span_shortGen_upto hC _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d σ D.R.r _ hσ hU hr hA hGm
      hlev hnab hunit h3 (fun _ => ⟨ph, 1, x₀, hpin⟩) nab b 0 a hb hdom hn hP hχ htot
    refine GlobalTheory.mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)))
      (sec Y.d.Xo₂ Y.d.c₂ a n) hind _ (fun g hg => hg.1) hf'.1 (hsp ?_)
    exact ⟨hf'.2 _ hσ, fun k x hx => dif_neg hx⟩
  · obtain ⟨hsec, Λ, N, x0, P, hUn, hTb, hTM, hN, -, hPl, hR⟩ := hg
    obtain ⟨inst, hnab⟩ := hnab
    obtain ⟨t, ht, hb'⟩ := exists_smul_nonneg_of_shortRule_any_level D _ _ _ Y.d.Xo₂ Y.d.c₂ n d hlev hnab
      (fun k _ _ y => by rw [hone k y, one_pow])
      (GlobalTheory.PlaceInt.datum_isIntegral _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d hlev ph 1 x₀ hpin)
      Λ N hUn hTM hN a P hPl x0 g hsec hR
    exact ⟨t, N, ht, hN.1.pos, fun la ℓ hℓ hm hor =>
      hb' la ℓ hℓ hm (hor.elim (trivAt_of_dvd hTb) (trivAt_of_not_dvd hUn hN hℓ))⟩

theorem exists_smul_nonneg_all (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n) (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n)
    (f : Rul Y.d.Xo₂ Y.d.c₂) (hf : f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n) :
    ∃ s : 𝓞 Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  have hmul : CuspMul Y.d.Xo₂ Y.d.c₂ Y.U := cusp_mul_of_M5 ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _
  have hD : ∀ k : ℕ, Dom (k • a) (k * n) := fun k =>
    ⟨fun τ i i' hi => Nat.mul_le_mul_left k (hdom.1 τ hi), hdom.2.mul_left k⟩
  have hpow : ∀ k : ℕ, f ^ (k + 1) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U ((k + 1) • a) ((k + 1) * n) := fun k => by
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [pow_succ, succ_nsmul a (k + 1), Nat.succ_mul (k + 1)]
      exact hmul _ _ _ _ _ _ (hD _) hdom ih hf
  obtain ⟨w, hw0, hw⟩ := exists_pow_root_eq_one D.host.E
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have h2 : ((k + 1 : ℕ) : ℤ) ∣ (((k + 1) * n / 2 : ℕ) : ℤ) := by
    obtain ⟨m, hm⟩ := hdom.2
    rw [hm, ← two_mul, mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
    exact Int.natCast_dvd_natCast.2 (dvd_mul_right _ _)
  have h1 : ∀ x, ((k + 1 : ℕ) : ℤ) ∣ ((((k + 1) • a) x : ℕ) : ℤ) := fun x =>
    Int.natCast_dvd_natCast.2 (dvd_mul_right (k + 1) (a x))
  obtain ⟨s, hs, h⟩ := exists_smul_nonneg_of_dvd D T j Y e o hG (k + 1) hw _ _ (hD (k + 1))
    (hn.trans (Nat.le_mul_of_pos_left _ hw0)) (fun σ c τ i => by
      unfold laU
      split_ifs
      · exact (h1 _).add h2
      · exact (h1 _).neg_right.sub h2) _ (hpow k)
  exact ⟨s, hs, fun la v hv => nonneg_of_pow (fun la => isVal_valSet la) hv s f _ (h la v hv)⟩

end GlobalTheory.LargeCover
