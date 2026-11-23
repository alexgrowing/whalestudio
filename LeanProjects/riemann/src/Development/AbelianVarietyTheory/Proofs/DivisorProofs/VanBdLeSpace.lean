import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedRuleOfFlagComponentSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerTriangularTwoBlockMulWeylTwoBlockEqTransvec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPtMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourierJacobiConstantTermEqZeroOfFlowLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentArcDegeneratingOnModelConvergenceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.VanishingBound

theorem keySec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) : Nonempty (GlobalTheory.ShFam.KeySec Y.d.Xo₂ Y.d.c₂) := by
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf σ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F (by omega) hY.geo

theorem isSec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (la : AllWt.Weight (T.Q.Dw j)) (f : Rul Y.d.Xo₂ Y.d.c₂)
    (hf : f ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k) :
    ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k) := by
  have hU := hY.unf σ hσ
  by_cases hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ →
      (wtOf (T.Q.Dw j) la 0).1 (τ, j') ≤ (wtOf (T.Q.Dw j) la 0).1 (τ, i)
  · by_cases hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q
    · exact GlobalTheory.T.isSec_reading_decreasing_integer_exponents _ _ _ _ _ _ σ _ (Y.U σ) (keySec D T j Y e o hY σ hσ) hσ hU hpq _
        (AllWt.even_wtOf la 0) hdec f hf k
    · have hp : (T.Q.Dw j).p = 0 := by omega
      have hq : (T.Q.Dw j).q = 0 := by omega
      have hG : wtOf (T.Q.Dw j) la 0 = wtZ (fun _ => 0) 0 := by
        refine Prod.ext (funext fun x => ?_) ?_
        · simp only [wtOf, wtZ, hp, hq]
          split_ifs <;> first | (exfalso; omega) | simp
        · simp [wtOf, wtZ]
      rw [hG, AllWt.modelWt_wtZ]
      have hf' : f ∈ sec Y.d.Xo₂ Y.d.c₂ (fun _ => 0) 0 := by
        rw [← AllWt.secZ_nat, ← AllWt.exZ_wtZ, ← hG]
        exact hf
      exact hU.2.2.2.2.1 _ _ ⟨fun τ => fun a b _ => le_refl _, ⟨0, rfl⟩⟩ f hf' k
  · have hex : ∃ (τ : D.host.E →+* ℂ) (m : ℕ) (hm : m + 1 < (T.Q.Dw j).mult τ),
        (wtOf (T.Q.Dw j) la 0).1 (τ, m) < (wtOf (T.Q.Dw j) la 0).1 (τ, m + 1) := by
      by_contra hne
      push_neg at hne
      apply hdec
      intro τ i j' hij hj'
      revert hj'
      induction j', hij using Nat.le_induction with
      | base => intro _; exact le_refl _
      | succ n hn ih => intro hj'; exact (hne τ n hj').trans (ih (by omega))
    obtain ⟨τ, m, hm, hlt⟩ := hex
    have h0 : f = 0 := GlobalTheory.NonDomVanish.eq_zero_of_lt hf τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl hlt
    subst h0
    rw [map_zero]
    exact ⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩

open scoped LaurentSeries in

theorem fjZero (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (la : AllWt.Weight (T.Q.Dw j)) (s) (hs : s ∈ vanBd TF.X Z la)
    (f : GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (hfs : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ GlobalTheory.AllWt.suppOn Z) (hfsec : sec₀ TF.X Z _ f = H0.restr le_top s)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k)
    (hsec : ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k))
    (ξ) (hξ : ((Y.U σ).X k).IsIso ξ) (x) (hx : x ∈ ((Y.U σ).X k).dom) :
    ((Y.U σ).X k).fj (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) ξ 0 (rdU (Y.U σ) f k) x = 0 := by
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hU := hG.unf σ hσ
  letI : Algebra Y.d.c₂.F ℂ⸨X⸩ := (GlobalTheory.ArcId.cstL.comp σ).toAlgebra
  have halg : ∀ x : Y.d.c₂.F, algebraMap Y.d.c₂.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)) :=
    fun _ => rfl
  obtain ⟨y, T₀, s', d, hbd, hd, hw⟩ :=
    GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) halg hσ hU k ξ hξ x hx _ _ TF.Y
  have hc : (algebraMap (PowerSeries ℂ) ℂ⸨X⸩).comp ((PowerSeries.C (R := ℂ)).comp σ) = algebraMap Y.d.c₂.F ℂ⸨X⸩ :=
    RingHom.ext fun t => (halg t).symm
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 none = 0 := rfl
  have hcoef : ∀ m ≤ (0:ℤ), (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff m = 0 := by
    intro m hm
    by_cases hZ : GlobalTheory.AllWt.LiesOn Z y
    · obtain ⟨v, hv, hval⟩ :=
        GlobalTheory.CuspOnTor.evR_mem_maximalIdeal _ _ _ _ _ _ TF.Y TF.X Z la s hs f hfsec (PowerSeries ℂ) ℂ⸨X⸩ _ y hc hZ hbd
      rw [hval]; exact GlobalTheory.CuspFrom.coeff_eq_zero hv hm
    · rw [hfs ℂ⸨X⸩ y ((GlobalTheory.AllWt.liesOff_iff Z y).2 hZ)]; rfl
  exact GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line _ _ _ _ _ ξ x s' d T₀ (fun j => (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff j) hsec
    (GlobalTheory.CuspFrom.freqNonneg _ hf1 hsec) hξ hx hd hcoef fun w hw' => ⟨(hw w hw').1, (hw w hw').2 _ hex _ f.2⟩

end GlobalTheory.HSApp.VanishingBound

namespace GlobalTheory.HSApp

open GlobalTheory.HSApp.VanishingBound in

theorem vanBd_le_space : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), vanBd TF.X Z la ≤ space TF.X Z Y.U la := by
  intro D T j Y e o hG hf Z TF la s hs
  obtain ⟨f, hfZ, hfs⟩ := GlobalTheory.T.exists_supportedRule_of_flagComponentSection _ _ _ _ _ _ _ TF.X Z (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) (H0.restr le_top s)
  have hsec := isSec D T j Y e o hG la f.1 f.2
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hcusp : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0) := by
    refine ⟨GlobalTheory.AllWt.mem_cuspW.2 ⟨f.2, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩, hfZ⟩
    have h0 := fjZero D T j Y e o hG hf Z TF la s hs f hfZ hfs σ hσ k (hsec σ hσ k)
    have h3 := (GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ (hsec σ hσ k) (GlobalTheory.CuspFrom.isModerate _ hf1 (hsec σ hσ k)) h0).1.2
    exact ⟨⟨hsec σ hσ k, h3⟩, fun ξ hξ x hx => h0 ξ hξ x hx⟩
  exact ⟨⟨f.1, hcusp⟩, hfs⟩

end GlobalTheory.HSApp
