import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanShortGenUpto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnfGroupContainsCongruenceUptoRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPairQuotientHorizontalGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormParallelWeightEachComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroScalarWeightCuspFormComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalGeneratorZpowMulCuspFormMemSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantWeightShiftFlatLineDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicRestrictionSubalgebraFrameDomainIsDom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerExponentSectionEqZeroOfIncreasingFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspSectionLargeEvenScalarWeightStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatAnyLevel

section Span

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

set_option maxHeartbeats 1000000 in

theorem holSub0_le_span_cusp_upto : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → l.A = 1 → (∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ σ, GoodEmb c σ → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, GlobalTheory.LargeCover.PrincUpTo ((U σ).X k) l.M (Formalism.L2.PjFree.laU (U σ) a n k)) → (∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → GlobalTheory.Dict.holSub0 (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU (U σ) '' (Formalism.L2.PjFree.cusp Xo c U a n : Set (Rul Xo c))) := by
  intro hC E _ _ _ H Dw l Xo c r U hr hA hU σ hσ hG a n hdom hlast hn hP hχ
  have hrk : r = Dw.p + Dw.q := (hU σ hσ).1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : Dw.p + Dw.q ≤ n := by
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r h0
    omega
  have hd : ∃ d : DeltaDat Xo c n, d.IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧
      d.pd = 1 ∧ d.l₂.A = l.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c h1 n 1 ⊤ l Xo c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l Xo c
  have hunit : UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    have h : ∀ z : FrPt d.Xo₂ d.c₂ K, evR d.Xo₂ d.c₂ d.cδ z = 1 := fun z => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : c.Fˣ) : c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [h y, h y']
    simp
  have htot : ShortValTot Xo c nab 1 0 a n d :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n d (GlobalTheory.levelMaps_closed hL E H Dw h1)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
      nab 1 0 a
  refine (GlobalTheory.LargeCover.holSub0_le_span_shortGen_upto hC E H Dw l Xo c n d σ r (U σ) hσ (hU σ hσ) hr hA hG hlev hnab hunit h3
    (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a Nat.one_pos hdom hn hP hχ htot).trans
    (Submodule.span_mono (Set.image_mono ?_))
  exact GlobalTheory.T.short_thetaSeries_dominant_weight_isCuspForm hC E H Dw l Xo c n d r U hr hU hlev hnab hunit (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a hdom hlast

theorem princUpTo_of_det {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (M : ℕ) (hM : 3 ≤ M)
    (hdet : ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1)
    (la : Wt X.Ψ r) (hla : ∀ τ, (r : ℤ) ∣ ∑ i, la τ i)
    (h : ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
      (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (M : E) • y) →
      ∃ gb ∈ X.Γ, ∃ (u : E) (n : ℕ), 0 < n ∧ u ^ n = 1 ∧
        (gb : Matrix (Fin r) (Fin r) E) = u • (ga : Matrix (Fin r) (Fin r) E)) :
    GlobalTheory.LargeCover.PrincUpTo X M la := by
  intro ga hga hc
  obtain ⟨gb, hgb, u, n, hn, hu, he⟩ := h ga hga fun x hx => by
    obtain ⟨y, hy, e⟩ := hc x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hu; exact zero_ne_one hu
  have hda : (ga : Matrix (Fin r) (Fin r) E).det = 1 :=
    GlobalTheory.LevLaws.eq_one_of_norm_one hM _ (isIntegral_trans (A := 𝓞 E) _
      (GlobalTheory.CongruenceDet.isIntegral_det_sub_one (by omega) X.Λ _ X.Λ_fg X.Λ_span hc))
      (GlobalTheory.CongruenceDet.det_mul_conj X.Gm _ X.Gm_det hga.1)
  have hur : u ^ r = 1 := by
    have := hdet gb hgb
    rwa [he, Matrix.det_smul, hda, _root_.mul_one, Fintype.card_fin] at this
  let b : Frame X.Ψ r := fun τ => (Matrix.diagonal fun _ => τ.1 u : Matrix (Fin r) (Fin r) ℂ)
  have hb : ∀ τ, mat b τ = τ.1 u • (1 : Matrix (Fin r) (Fin r) ℂ) := fun τ => by
    rw [Matrix.smul_one_eq_diagonal]; rfl
  refine ⟨gb, hgb, b, fun τ => ⟨?_, fun a c hac => Matrix.diagonal_apply_ne _ hac.ne'⟩, ?_, fun x => ?_⟩
  · rw [hb, Matrix.det_smul, Matrix.det_one, _root_.mul_one]
    exact pow_ne_zero _ ((map_ne_zero τ.1).2 hu0)
  · refine Finset.prod_eq_one fun τ _ => ?_
    obtain ⟨k, hk⟩ := hla τ
    have h0 : τ.1 u ≠ 0 := (map_ne_zero τ.1).2 hu0
    have e : ∀ s : Finset (Fin r), ∏ i ∈ s, b τ i i ^ la τ i = τ.1 u ^ ∑ i ∈ s, la τ i := fun s => by
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        have : b τ i i = τ.1 u := Matrix.diagonal_apply_eq _ i
        rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, this, zpow_add₀ h0]
    rw [e, hk, _root_.zpow_mul, zpow_natCast, ← map_pow, hur, map_one, _root_.one_zpow]
  · funext τ
    show (gb : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
      (ga : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)
    have : (u • (ga : Matrix (Fin r) (Fin r) E)).map τ.1 = τ.1 u • (ga : Matrix (Fin r) (Fin r) E).map τ.1 := by
      ext a c; simp
    rw [he, this, hb, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]

end Span

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section Laws

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

structure NeatUnf (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop where
  pos : 1 ≤ Dw.p + Dw.q
  lev : l.A = 1
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  geo : FnAlgClosed Xo c
  same : ∀ σ, GoodEmb c σ → ∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0
  chi : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1
  det : ∀ σ, GoodEmb c σ → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1

def SumDvd (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ σ, GoodEmb c σ → ∀ k τ, (r : ℤ) ∣ ∑ i, laU (U σ) a n k τ i

theorem NeatUnf.onto {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (h : NeatUnf U) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : Dom a n) (hp : ∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i))
    (hn : 4 * (finrank ℚ E * r) + 4 ≤ n) (hd : SumDvd U a n) :
    holSub0 (U σ).X (laU (U σ) a n) ≤ Submodule.span ℂ (rdU (U σ) '' (cusp Xo c U a n : Set (Rul Xo c))) := by
  have hr : 1 ≤ r := (h.unf σ hσ).1 ▸ h.pos
  have key := holSub0_le_span_cusp_upto GlobalTheory.chartIndependence_unconditional E H Dw l
    Xo c r (fun s => Formalism.L2.PjFree.Unf.ofPj (U s)) hr h.lev
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf s hs)) σ hσ (h.same σ hσ)
    a n ha (fun τ _ h0 => hp τ _ (by omega)) hn
    (fun k => princUpTo_of_det _ _ l.three_le (h.det σ hσ k) _ (hd σ hσ k)
      (GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
        (Formalism.L2.PjFree.Unf.ofPj (U σ)) (h.unf σ hσ) h.lev hr k))
    (fun k => h.chi σ hσ a n ha k)
  intro P hP
  exact key ⟨hP.1, hP.2⟩

end Laws

section Chain

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

open AlgebraicGeometry in

theorem framesOn_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), NeatUnf U → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∃ k, framesOn (U σ) Z = {z | z.1 = k ∧ z.2 ∈ ((U σ).X z.1).dom} := by
  intro E _ _ _ H Dw l Xo c r U hL Z σ hσ
  obtain ⟨q, hq⟩ : ∃ q : (U σ).Comp ≃ Comp Xo c, ∀ k (y : ((U σ).X k).dom) (s : Sp (CAt σ)),
      ptF ((U σ).un k y) s ∈ (q k).1 :=
    GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj (U σ)) hσ (hL.unf σ hσ)
      (fun k => GlobalTheory.CompBij.frames_nonempty _) hL.geo
  refine ⟨q.symm Z, Set.ext fun ⟨k, y⟩ => ⟨?_, ?_⟩⟩
  · rintro ⟨hy, hl⟩
    refine ⟨?_, hy⟩
    have hk : q k = Z := by
      by_contra hne
      let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) (hq k ⟨y, hy⟩ s) (hl s)
    exact (Equiv.eq_symm_apply q).2 hk
  · rintro ⟨hk, hy⟩
    obtain rfl : k = q.symm Z := hk
    refine ⟨hy, fun s => ?_⟩
    have := hq (q.symm Z) ⟨y, hy⟩ s
    rwa [Equiv.apply_symm_apply] at this

theorem cuspOn_fd_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), NeatUnf U → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → SumDvd U a n → FiniteDimensional c.F (cuspOn U Z (wtZ a n)) ∧ ∀ P ∈ holSub (U σ).X (modelWt (U σ) (wtZ a n)), (∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z → P k y = 0) → P ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U h Z σ hσ a n hD hpos hn hdv
  refine ⟨?_, fun P hP hoffZ => ?_⟩
  · haveI := GlobalTheory.cuspForms_finiteDimensional_of_goodEmb E H Dw l Xo c r U σ hσ (h.unf σ hσ) a n hD
    have hle : cuspOn U Z (wtZ a n) ≤ cusp Xo c U a n := by
      rw [← cuspW_wtZ]; exact cuspOn_le U Z (wtZ a n)
    exact Submodule.finiteDimensional_of_le hle
  · have htest : ∀ z ∈ framesOn (U σ) Z, ∀ hz : z.2 ∈ ((U σ).X z.1).dom, Tested ((U σ).un z.1 ⟨z.2, hz⟩) :=
      fun z _ hz => by
        obtain ⟨⟨-, -, -, -, hA, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
        haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
        exact hA _ _
    have hoff : P ∈ offZero (U σ).X := fun k y hy => hoffZ k y fun hz => hy hz.1
    have hP0 : P ∈ holSub0 (U σ).X (laU (U σ) a n) := ⟨by rwa [← modelWt_wtZ], hoff⟩
    have hsp := h.onto σ hσ a n hD hpos hn hdv hP0
    have hfix : rdU (U σ) (idem Z) * P = P := by
      funext k y
      show rdU (U σ) (idem Z) k y * P k y = P k y
      by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨hd, hl⟩ := hz
        have h1 : rdU (U σ) (idem Z) k y = 1 := by
          simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_pos]
          rw [evR_idem hl (htest _ ⟨hd, hl⟩ hd)]
          rfl
        rw [h1, one_mul]
      · rw [hoffZ k y hz, mul_zero]
    let g : FDSec (U σ).X →ₗ[ℂ] FDSec (U σ).X := LinearMap.mulLeft ℂ (rdU (U σ) (idem Z))
    have hmap := Submodule.mem_map_of_mem (f := g) hsp
    rw [Submodule.map_span] at hmap
    have hg : g P = P := hfix
    rw [hg] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨idem Z * f, ⟨?_, ?_⟩, ?_⟩
    · rw [← cuspW_wtZ] at hf
      exact GlobalTheory.CompRestr.idem_mul_mem_cuspW h.unf Z hf
    · rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
    · show rdU (U σ) (idem Z * f) = rdU (U σ) (idem Z) * rdU (U σ) f
      exact AllWt.rdU_mul (U σ) _ _

open GlobalTheory.FlatCore.MulSpan in

theorem horizGen_mul_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), NeatUnf U → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (k0 : (U σ).Comp), framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} → ∀ (τ' : ((U σ).X k0).Ψ) (m : ℤ) (b b' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom b n → Dom b' n → (∀ ρ i, i < Dw.mult ρ → 1 ≤ b' (ρ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → SumDvd U b' n → modelWt (U σ) (wtZ b' n) k0 = modelWt (U σ) (wtZ b n) k0 + m • modelFlat r τ' → ∀ f ∈ cuspOn U Z (wtZ b n), (fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1) ∈ Submodule.span ℂ ((fun g : Rul Xo c => fun y : ↥((U σ).X k0).dom => rdU (U σ) g k0 y.1) '' (cuspOn U Z (wtZ b' n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U hL Z σ hσ k0 hk τ' m b b' n hb hb' hpos hn hdv hw f hf
  have hP : rdU (U σ) f ∈ holSub (U σ).X (modelWt (U σ) (wtZ b n)) := (mem_cuspW.1 (cuspOn_le U Z _ hf)).2 σ hσ
  have hLP : mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) ∈
      holSub (U σ).X (modelWt (U σ) (wtZ b' n)) := by
    refine mulAt_mem_holSub _ k0 _ _ _ (fun Q hQ => ?_) hP
    rw [hw]
    refine HorizMul.horizGen_zpow_mul_mem_SS E r _ τ' _ m (hL.det σ hσ k0) (fun γ hγ => ?_) Q hQ
    rw [← hw, modelWt_wtZ, modelWt_wtZ, hL.chi σ hσ b n hb k0 γ hγ, hL.chi σ hσ b' n hb' k0 γ hγ]
  have hoff : ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k y = 0 := by
    intro k y hy
    by_cases hkk : k = k0
    · subst hkk
      have hd : y ∉ ((U σ).X k).dom := fun hd => hy (by rw [hk]; exact ⟨rfl, hd⟩)
      have h0 : rdU (U σ) f k y = 0 := by
        simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_neg, not_false_eq_true]
      rw [mulAt_same]
      simp only [h0, mul_zero]
    · rw [mulAt_ne _ _ _ _ hkk]
      rfl
  have hsp := (cuspOn_fd_span E H Dw l Xo c r U hL Z σ hσ b' n hb' hpos hn hdv).2 _ hLP hoff
  let R : FDSec (U σ).X →ₗ[ℂ] (↥((U σ).X k0).dom → ℂ) :=
    { toFun := fun Q y => Q k0 y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmap := Submodule.mem_map_of_mem (f := R) hsp
  rw [Submodule.map_span, Set.image_image] at hmap
  have e : R (mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f)) =
      fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1 := by
    funext y
    show mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k0 y.1 = _
    rw [mulAt_same]
  rw [e] at hmap
  exact hmap

theorem exists_model_cusp {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hL : NeatUnf U) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    (k : (U σ).Comp) : ∃ n : ℕ, 0 < n ∧ Even n ∧ ∃ P ∈ ((U σ).X k).SS (laU (U σ) 0 n k), ∃ y ∈ ((U σ).X k).dom,
      P y ≠ 0 := by
  have hU := hL.unf σ hσ
  have hr : r = Dw.p + Dw.q := hU.1
  have hp0 : ((U σ).X k).p0 = Dw.q := (hU.2.1 k).1
  by_cases hdef : Dw.p = 0 ∨ Dw.q = 0
  · obtain ⟨y, hy⟩ := GlobalTheory.CompBij.frames_nonempty ((U σ).X k)
    obtain ⟨n, hn, he, f, hf, hne⟩ := GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H Dw l Xo c σ ((U σ).un k ⟨y, hy⟩)
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, he⟩
    have hs := hU.2.2.2.2.1 0 n hD f hf k
    obtain ⟨τ0⟩ : Nonempty ((U σ).X k).Ψ := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : τ ∈ ((U σ).X k).Ψ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, not_not.mp (fun h' => h ((((U σ).X k).cmType τ).mpr h'))⟩⟩
    have hp : ((U σ).X k).p0 = 0 ∨ ((U σ).X k).p0 = r := by omega
    refine ⟨n, hn, he, _, GlobalTheory.BoundedCusp.mem_SS_of_definite _ _ τ0 hp _
      ⟨hs, GlobalTheory.ScalarCusp.bdd_of_definite _ hp _ _ hs⟩, y, hy, ?_⟩
    have e : rdU (U σ) f k y = toC (evR Xo c f ((U σ).un k ⟨y, hy⟩)) := dif_pos hy
    rw [e]
    exact hne
  · have hla : ∀ n : ℕ, laU (U σ) 0 n k = fun (τ : ((U σ).X k).Ψ) (j : Fin r) =>
        if ((U σ).X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ) := fun n => by
      funext τ j
      simp [laU]
    obtain ⟨n, hn, hev, P, hPm, y, hy, hne⟩ := GlobalTheory.T.exists_nonzero_cuspSection_large_evenScalarWeight E r ((U σ).X k) (by omega) (by omega)
      (fun n hn γ hγ => by rw [← hla]; exact hL.chi σ hσ 0 n ⟨fun _ => antitone_const, hn⟩ k γ hγ) 1
    exact ⟨n, hn, hev, P, hla n ▸ hPm, y, hy, hne⟩

theorem exists_cuspOn_two {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hL : NeatUnf U) (Z : Comp Xo c) :
    ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧
      4 * (finrank ℚ E * r) + 4 ≤ n ∧ SumDvd U a n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  classical
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  generalize c.F.val.toRingHom = σ at hσ
  have hr : 1 ≤ r := (hL.unf σ hσ).1 ▸ hL.pos
  obtain ⟨k, hk⟩ := framesOn_model E H Dw l Xo c r U hL Z σ hσ
  obtain ⟨n₀, hn₀, ⟨t, ht⟩, P, hP, y, hy, hne⟩ := exists_model_cusp hL hσ k
  have hpow : ∀ j : ℕ, P ^ (j + 1) ∈ ((U σ).X k).SS (laU (U σ) 0 ((j + 1) * n₀) k) := by
    intro j
    induction j with
    | zero => simpa using hP
    | succ j ih =>
      have e : laU (U σ) 0 ((j + 1 + 1) * n₀) k = laU (U σ) 0 ((j + 1) * n₀) k + laU (U σ) 0 n₀ k := by
        have e1 : (j + 1 + 1) * n₀ / 2 = (j + 1) * n₀ / 2 + n₀ / 2 := by
          have h1 : (j + 1 + 1) * n₀ = 2 * ((j + 1) * t + t) := by rw [ht]; ring
          have h2 : (j + 1) * n₀ = 2 * ((j + 1) * t) := by rw [ht]; ring
          rw [h1, h2]; omega
        funext τ i
        simp only [laU, Pi.zero_apply, Pi.add_apply, e1]
        split_ifs <;> push_cast <;> ring
      rw [e, pow_succ]
      exact (siegelSpaceAlgebra_holds (E := E) r ((U σ).X k) _ _ 0).2.1 _ ih P hP.1
  obtain ⟨B, hB⟩ : ∃ B, B = 4 * (finrank ℚ E * r) + 8 := ⟨_, rfl⟩
  have hBr : B ≤ r * B * t := by
    have : 1 ≤ t := by omega
    calc B = 1 * B * 1 := by ring
      _ ≤ r * B * t := by gcongr
  obtain ⟨M, hM⟩ : ∃ M, r * B = M + 1 := ⟨r * B - 1, by
    have : 1 ≤ r * B := Nat.mul_pos hr (by omega)
    omega⟩
  have hMn : (M + 1) * n₀ = 2 * (r * B * t) := by rw [← hM, ht]; ring
  obtain ⟨n, hn⟩ : ∃ n, 2 * (r * B * t) = n + 2 * 2 := ⟨2 * (r * B * t) - 4, by omega⟩
  have hnev : Even n := ⟨r * B * t - 2, by omega⟩
  have hnb : 4 * (finrank ℚ E * r) + 4 ≤ n := by omega
  have hla : ∀ {s : c.F →+* ℂ} (V : Unf Xo c s r), laU V (fun _ => 2) n = laU V 0 (2 * (r * B * t)) := fun V =>
    funext fun k' => by rw [GlobalTheory.FlatCore.NonzeroCusp.laU_const, hn]
  have hdv : SumDvd U (fun _ => 2) n := fun s _ k' τ => by
    rw [hla]
    refine Finset.dvd_sum fun i _ => ?_
    have h2 : (r : ℤ) ∣ ((2 * (r * B * t) / 2 : ℕ) : ℤ) := by
      rw [Nat.mul_div_cancel_left _ two_pos, mul_assoc]
      exact Int.natCast_dvd_natCast.2 (dvd_mul_right _ _)
    unfold laU
    split_ifs
    · exact (dvd_zero _).add h2
    · exact (dvd_zero _).neg_right.sub h2
  have hQm := hpow M
  rw [hMn] at hQm
  let P₀ : FDSec (U σ).X := Pi.single k (((U σ).X k).dom.indicator (P ^ (M + 1)))
  have hQ : P₀ ∈ holSub0 (U σ).X (laU (U σ) (fun _ => 2) n) := by
    rw [hla]
    refine ⟨holCusp_mem_holSub _ _ fun k' => ?_, fun k' y' hy' => ?_⟩
    · by_cases h : k' = k
      · subst h
        simp only [P₀, Pi.single_eq_same]
        exact (GlobalTheory.DomCongr.bddSec_cusp_congr E r _ _ _ _ (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hQm
      · simp only [P₀, Pi.single_eq_of_ne h]
        exact GlobalTheory.FlatCore.MulSpan.zero_mem_SS' _ _
    · by_cases h : k' = k
      · subst h
        simp only [P₀, Pi.single_eq_same]
        exact Set.indicator_of_notMem hy' _
      · simp only [P₀, Pi.single_eq_of_ne h, Pi.zero_apply]
  have hQy : P₀ k y ≠ 0 := by
    simp only [P₀, Pi.single_eq_same]
    rw [Set.indicator_of_mem hy]; exact pow_ne_zero _ hne
  have hspan := hL.onto _ hσ (fun _ => 2) n ⟨fun _ => antitone_const, hnev⟩ (fun _ _ _ => by norm_num) hnb hdv hQ
  obtain ⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 2) n, rdU (U σ) f k y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let ev : FDSec (U σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (U σ) '' (cusp Xo c U (fun _ => 2) n : Set (Rul Xo c))) ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    exact hQy (hle hspan)
  have hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
    rw [hk]; exact ⟨rfl, hy⟩
  obtain ⟨hy', hlies⟩ := hz
  obtain ⟨g, hg, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 2) n)
    ⟨f, by rw [cuspW_wtZ]; exact hf⟩
  refine ⟨fun _ => 2, n, ⟨fun _ => antitone_const, hnev⟩, fun _ _ _ => le_rfl, hnb, hdv, g, g.2, ?_⟩
  intro h0
  have e : rdU (U σ) (g : Rul Xo c) k y = rdU (U σ) f k y := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy']
    rw [hg _ _ hlies]
  rw [h0, map_zero] at e
  exact hfy e.symm

theorem res_ind {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hL : NeatUnf U) (Z : Comp Xo c)
    (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (k0 : (U σ).Comp)
    (hk : framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom}) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c a n) → (∀ i, b i ∈ suppOn Z) →
      LinearIndependent c.F b →
      LinearIndependent ℂ (fun i => fun y : ↥((U σ).X k0).dom => rdU (U σ) (b i) k0 y.1)) ∧
    ∀ f ∈ sec Xo c a n, f ∈ suppOn Z → f ≠ 0 → ∃ y : ↥((U σ).X k0).dom, rdU (U σ) f k0 y.1 ≠ 0 := by
  have hR := GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ H Dw l Xo c σ r
    (Formalism.L2.PjFree.Unf.ofPj (U σ)) (hL.unf σ hσ) a n
  simp only [Formalism.L2.PjFree.rdU_ofPj] at hR
  have hoff : ∀ f ∈ suppOn Z, ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      rdU (U σ) f k y = 0 := fun f hf k y hz => rdU_eq_zero (U σ) hf hz
  refine ⟨fun m b hb hs hli => ?_, fun f hf hs hne => ?_⟩
  · have h0 : LinearIndependent ℂ (fun i => rdU (U σ) (b i)) := hR.1 m b hb hli
    rw [Fintype.linearIndependent_iff] at h0 ⊢
    intro w hw
    refine h0 w ?_
    funext k y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy⟩ := hz
      have := congrFun hw ⟨y, hy⟩
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    · exact Finset.sum_eq_zero fun i _ => by rw [hoff _ (hs i) k y hz, mul_zero]
  · by_contra hall
    push_neg at hall
    refine hne (hR.2 f hf fun k y hy => ?_)
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy'⟩ := hz
      exact hall ⟨y, hy'⟩
    · exact hoff f hs k y hz

open GlobalTheory.FlatPair in

theorem exists_flat_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), NeatUnf U → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (G : WTZ E) (f g : Rul Xo c), Even G.2 ∧
      f ∈ cuspOn U Z G ∧ g ∈ cuspOn U Z (G + wtOf Dw (flatWt Dw τ) 0) ∧ f ≠ 0 ∧ IsFlatQuot U Z τ f g := by
  intro E _ _ _ H Dw l Xo c r U hL Z τ
  obtain ⟨a, n, hD, h2, hn, hdv, f0, hf0, hf0ne⟩ := exists_cuspOn_two hL Z
  obtain ⟨a', hD', h1', hex⟩ := GlobalTheory.FlatShift.exists_shift E H Dw a n τ hD h2
  have h1 : ∀ ρ i, i < Dw.mult ρ → 1 ≤ a (ρ, i) := fun ρ i hi => le_trans (by norm_num) (h2 ρ i hi)
  have hT : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
  have hEv : Even (wtZ a n).2 := by
    obtain ⟨m, hm⟩ := hD.2
    exact ⟨m, by simp [wtZ, hm]⟩
  have hVV' : cuspOn U Z (wtZ a' n) = cuspOn U Z (wtZ a n + wtOf Dw (flatWt Dw τ) 0) :=
    cuspOn_congr hL.unf Z hex
  have hdv' : SumDvd U a' n := fun σ hσ k ρ => by
    have hτ := relab_mem (U σ) hσ (hL.unf σ hσ) τ k
    have hw := modelWt_shift (U σ) hσ (hL.unf σ hσ) τ hEv hex k hτ
    rw [modelWt_wtZ, modelWt_wtZ] at hw
    rw [hw]
    simp only [Pi.add_apply, Finset.sum_add_distrib, modelFlat, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    exact (hdv σ hσ k ρ).add (dvd_mul_right _ _)
  have hsec : ∀ (b : (E →+* ℂ) × ℕ → ℕ), cuspOn U Z (wtZ b n) ≤ sec Xo c b n := fun b f hf => by
    have := cuspW_le_secZ (U := U) (wtZ b n) (cuspOn_le U Z _ hf)
    rwa [AllWt.exZ_wtZ, secZ_nat] at this
  have hsupp : ∀ (G : WTZ E), cuspOn U Z G ≤ suppOn Z := fun G => inf_le_right
  have pk : ∀ σ, GoodEmb c σ → ∃ (k0 : (U σ).Comp) (hτ : relab c σ τ.1 ∈ ((U σ).X k0).Ψ),
      framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} ∧
      (∀ f ∈ cuspOn U Z (wtZ a n), (fun y : ↥((U σ).X k0).dom => horizGen ⟨_, hτ⟩ y.1) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a' n) : Set (Rul Xo c)))) ∧
      (∀ f ∈ cuspOn U Z (wtZ a' n), (fun y : ↥((U σ).X k0).dom => (horizGen ⟨_, hτ⟩ y.1)⁻¹) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c)))) := by
    intro σ hσ
    obtain ⟨k0, hk⟩ := framesOn_model E H Dw l Xo c r U hL Z σ hσ
    have hτ := relab_mem (U σ) hσ (hL.unf σ hσ) τ k0
    have hw := modelWt_shift (U σ) hσ (hL.unf σ hσ) τ hEv hex k0 hτ
    refine ⟨k0, hτ, hk, fun f hf => ?_, fun f hf => ?_⟩
    · have := horizGen_mul_mem_span E H Dw l Xo c r U hL Z σ hσ k0 hk ⟨_, hτ⟩ 1 a a' n hD hD' h1' hn hdv' (by rw [hw, one_smul]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
    · have := horizGen_mul_mem_span E H Dw l Xo c r U hL Z σ hσ k0 hk ⟨_, hτ⟩ (-1) a' a n hD' hD h1 hn hdv
        (by rw [hw, neg_one_smul, add_neg_cancel_right]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
  obtain ⟨σ0, hσ0⟩ : ∃ σ, GoodEmb c σ := ⟨_, goodEmb_goodOf c c.F.val.toRingHom⟩
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a n)) :=
    (cuspOn_fd_span E H Dw l Xo c r U hL Z σ0 hσ0 a n hD h1 hn hdv).1
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a' n)) :=
    (cuspOn_fd_span E H Dw l Xo c r U hL Z σ0 hσ0 a' n hD' h1' hn hdv').1
  have hprod : ∀ f ∈ cuspOn U Z (wtZ a n), ∀ g ∈ cuspOn U Z (wtZ a' n),
      f * g ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := by
    intro f hf g hg
    have e : exZ Dw (wtZ (a + a') (n + n)) = exZ Dw (wtZ a n) + exZ Dw (wtZ a' n) := by
      rw [wtZ_add]; funext i; exact exZ_add _ _ i
    have hm := mul_mem_secZ (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hf))
      (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hg))
    rw [← e, AllWt.exZ_wtZ, secZ_nat] at hm
    refine ⟨hm, ?_⟩
    rw [mul_comm]
    exact mul_mem_suppOn g (hsupp _ hf)
  obtain ⟨k0, hτ0, hk0, hA0, -⟩ := pk σ0 hσ0
  obtain ⟨T, hT0, hTc⟩ := GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier c.F (Rul Xo c) (↥((U σ0).X k0).dom → ℂ) σ0 (resRd (U σ0) hT k0)
    (resRd_smul (U σ0) hT k0) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun m b hb hli => by
      have hb' : ∀ i, b i ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := fun i =>
        (Submodule.mul_le.2 hprod) (hb i)
      exact (res_ind hL Z σ0 hσ0 k0 hk0 (a + a') (n + n)).1 m b (fun i => (hb' i).1) (fun i => (hb' i).2) hli)
    (fun y => horizGen ⟨_, hτ0⟩ y.1) hA0 ⟨f0, hf0, fun h0 => by
      obtain ⟨y, hy⟩ := (res_ind hL Z σ0 hσ0 k0 hk0 a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
      have := congrFun h0 y
      simp only [Pi.mul_apply, resRd_apply, Pi.zero_apply, mul_eq_zero] at this
      rcases this with h | h
      · exact (horizGen_mem _ _).2.2 y.1 y.2 h
      · exact hy h⟩
  refine ⟨wtZ a n, f0, T ⟨f0, hf0⟩, hEv, hf0, hVV' ▸ (T ⟨f0, hf0⟩).2, hf0ne, fun σ hσ => ?_⟩
  obtain ⟨k1, hτ, hk, hA, hA'⟩ := pk σ hσ
  obtain ⟨y0, -⟩ := (res_ind hL Z σ hσ k1 hk a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
  haveI := GlobalTheory.FlatPair.holAlg_isDomain E r ((U σ).X k1) ⟨y0.1, y0.2⟩
  obtain ⟨hh, hh', hne⟩ := horizGen_mem ((U σ).X k1) ⟨_, hτ⟩
  obtain ⟨α, hα, hαT⟩ := GlobalTheory.commuting_multiplier_eq_const_smul_generator c.F (Rul Xo c) (↥((U σ).X k1).dom → ℂ) σ (resRd (U σ) hT k1)
    (resRd_smul _ _ _) (holAlg ((U σ).X k1)) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun m b hb hli => (res_ind hL Z σ hσ k1 hk a n).1 m b (fun i => hsec a (hb i)) (fun i => hsupp _ (hb i)) hli)
    (fun m b hb hli => (res_ind hL Z σ hσ k1 hk a' n).1 m b (fun i => hsec a' (hb i)) (fun i => hsupp _ (hb i))
      hli)
    _ _ hh hh' (by funext y; exact mul_inv_cancel₀ (hne y.1 y.2)) hA' T hT0 hTc
  refine ⟨α, hα, fun k hτk y hy => ?_⟩
  rw [hk] at hy
  obtain ⟨rfl, hyd⟩ := hy
  have e := congrFun (hαT ⟨f0, hf0⟩) ⟨y, hyd⟩
  simp only [resRd_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at e
  rw [e]
  ring

open GlobalTheory.SecDivision ReciprocityTheory.ChartRestriction.G GlobalTheory.Reg GlobalTheory.GenericFrames GlobalTheory.FlagTan in

theorem exists_quot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), NeatUnf U → ∀ (Z : Comp Xo c) (e e' : Ix Dw → ℤ) (f g : Rul Xo c), f ∈ secZ Xo c e → f ∈ suppOn Z → g ∈ secZ Xo c e' → g ∈ suppOn Z → f ≠ 0 → ∀ σ, GoodEmb c σ → ∀ q : FDSec (U σ).X, (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) g z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∃ s ∈ secZ Xo c (e' - e), idem Z * s = s ∧ s * f = g := by
  intro E _ _ _ H Dw l Xo c r U hL Z e e' f g hf hfZ hg hgZ hf0 σ hσ q hq hfg
  obtain ⟨-, -, h, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have off : ∀ {u : Rul Xo c}, u ∈ suppOn Z → ∀ Z', Z' ≠ Z → genVal Z' u = 0 := fun hu Z' hZ => by
    rw [genVal_apply h]; exact evC_eq_zero h hZ hu
  have hfz : genVal Z f ≠ 0 := fun h0 => hf0 (secZ_eq_zero_of_genVal hf fun Z' => by
    by_cases hZ : Z' = Z
    · rw [hZ, h0]
    · exact off hfZ Z' hZ)
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (e' - e)
    (fun Z' => genVal Z' g / genVal Z' f) fun C => by
      by_cases hZ : C.Z = Z
      swap
      · rw [off hgZ _ hZ, zero_div, mul_zero]; exact zero_mem _
      subst hZ
      obtain ⟨a, ha1, ha2⟩ := GlobalTheory.DegCmp.fChart_exists_val C hf
      obtain ⟨b, hb1, hb2⟩ := GlobalTheory.DegCmp.fChart_exists_val C hg
      have ha0 : (a : Om C.Z) ≠ 0 := by rw [ha1]; exact mul_ne_zero (Units.ne_zero _) hfz
      obtain ⟨u, hu⟩ := chart_dvd (U σ) hσ (hL.unf σ hσ) C hf hg q hq hfg (fun h0 => ha0 (by rw [h0]; rfl))
        (ha2 _) (hb2 _)
      have hu' : (b : Om C.Z) = a * u := by rw [hu]; rfl
      have hp : (∏ i, C.t i ^ e' i) = (∏ i, C.t i ^ (e' - e) i) * ∏ i, C.t i ^ e i := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by rw [← zpow_add, Pi.sub_apply, sub_add_cancel]
      have : ((∏ i, C.t i ^ (e' - e) i : (Om C.Z)ˣ) : Om C.Z) * (genVal C.Z g / genVal C.Z f) = u := by
        refine mul_left_cancel₀ ha0 ?_
        rw [← hu', ha1, hb1, hp, Units.val_mul]
        field_simp
      rw [this]
      exact u.2
  have hsv' : ∀ Z' : Comp Xo c, genVal Z' s = genVal Z' g / genVal Z' f := fun Z' => (genVal_apply h Z' s).trans (hsv Z')
  refine ⟨s, hs, sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (idem_mul_mem Z hs).1 hs) fun Z' => ?_),
    sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (sub_add_cancel e' e ▸ mul_mem_secZ hs hf) hg) fun Z' => ?_)⟩
  · rw [map_sub, map_mul]
    by_cases hZ : Z' = Z
    · rw [hZ, GlobalTheory.DegCmp.genVal_idem_self, one_mul, sub_self]
    · rw [hsv', off hgZ _ hZ, zero_div, mul_zero, sub_self]
  · rw [map_sub, map_mul, hsv']
    by_cases hZ : Z' = Z
    · rw [hZ, div_mul_cancel₀ _ hfz, sub_self]
    · rw [off hgZ _ hZ, zero_div, zero_mul, sub_self]

theorem contOn_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), NeatUnf U → ∀ (e : Ix Dw → ℤ), e none = 0 → ∀ s ∈ secZ Xo c e, ∀ σ, GoodEmb c σ → ∀ k, ContinuousOn (rdU (U σ) s k) ((U σ).X k).dom := by
  intro E _ _ _ H Dw l Xo c r U hL e he0 s hs σ hσ k
  by_cases hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩)
  · exact (GlobalTheory.ReadCont.differentiableOn_rdU_of_antitone (hL.unf σ hσ) hL.pos he0 hanti hs k).continuousOn
  · push_neg at hanti
    obtain ⟨τ, i, j, hij, hlt⟩ := hanti
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    rw [GlobalTheory.IncrZero.secZ_eq_zero_of_lt E H Dw l Xo c e τ i j hij' hlt s hs, map_zero]
    exact continuousOn_const

section Cancel
open Filter Topology
variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}

theorem exists_frame_ne (hL : NeatUnf U) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (hf : f ∈ cuspOn U Z G)
    (hf0 : f ≠ 0) : ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f z.1 z.2 ≠ 0 := by
  have hfs : f ∈ secZ Xo c (exZ Dw G) := cuspW_le_secZ G (Submodule.mem_inf.1 hf).1
  obtain ⟨R, hR, t, hmem, hφ⟩ :=
    GlobalTheory.DegCmp.exists_chart_read_at_frames E H Dw l Xo c r σ (U σ) (hL.unf σ hσ) Z
  let b : R := ⟨_, hmem _ f hfs⟩
  have hb : ¬ IsNilpotent b := fun h => by
    have h2 : ((b : Om Z)) = 0 := by rw [h.eq_zero]; rfl
    exact genVal_ne_zero_of_mem_cuspOn hf hf0 ((mul_eq_zero.1 h2).resolve_left (Units.ne_zero _))
  obtain ⟨φ, hφσ, hφb⟩ := exists_ringHom_ne_zero_of_not_isNilpotent σ hb
  obtain ⟨z, hz, s, hread⟩ := hφ φ hφσ
  refine ⟨z, hz, fun h0 => hφb ?_⟩
  rw [hread _ f hfs b rfl, h0, mul_zero]

theorem rdU_cancel (hL : NeatUnf U) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (hf : f ∈ cuspOn U Z G)
    (hf0 : f ≠ 0) {e' : Ix Dw → ℤ} (he : e' none = 0) {s : Rul Xo c} (hs : s ∈ secZ Xo c e')
    (q : FDSec (U σ).X) (hq : ∀ k, ContinuousOn (q k) ((U σ).X k).dom)
    (hrel : ∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) :
    ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2 := by
  obtain ⟨k, hk⟩ := framesOn_model E H Dw l Xo c r U hL Z σ hσ
  have hex : ∃ y ∈ ((U σ).X k).dom, rdU (U σ) f k y ≠ 0 := by
    obtain ⟨⟨k₀, y₀⟩, hz₀, hne⟩ := exists_frame_ne hL hσ hf hf0
    rw [hk] at hz₀
    obtain ⟨h1, hy₀⟩ := hz₀
    subst h1
    exact ⟨y₀, hy₀, hne⟩
  have hdiff : DifferentiableOn ℂ (rdU (U σ) f k) ((U σ).X k).dom :=
    differentiableOn_of_mem_holSub ((mem_cuspW.1 (Submodule.mem_inf.1 hf).1).2 σ hσ) k
  have hint := interior_closure_zero ((U σ).X k) hdiff hex
  have hcont : ContinuousOn (fun y => rdU (U σ) s k y - q k y) ((U σ).X k).dom :=
    (contOn_rdU E H Dw l Xo c r U hL e' he s hs σ hσ k).sub (hq k)
  have hO := FourierCoefficientDomain.isOpen_dom ((U σ).X k)
  have key : ∀ y ∈ ((U σ).X k).dom, rdU (U σ) s k y = q k y := by
    intro y hy
    by_contra hne
    have hev : ∀ᶠ w in 𝓝 y, rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom :=
      ((hcont.continuousAt (hO.mem_nhds hy)).eventually_ne (sub_ne_zero.2 hne)).and (hO.mem_nhds hy)
    have hsub : {w | rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom} ⊆
        closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0} := by
      rintro w ⟨hw, hwd⟩
      refine subset_closure ⟨hwd, ?_⟩
      have h3 := hrel ⟨k, w⟩ (by rw [hk]; exact ⟨rfl, hwd⟩)
      rw [GlobalTheory.AllWt.rdU_mul (U σ)] at h3
      have h2 : (rdU (U σ) s k w - q k w) * rdU (U σ) f k w = 0 := by
        rw [sub_mul, sub_eq_zero]
        exact h3
      exact (mul_eq_zero.1 h2).resolve_left hw
    have hy' : y ∈ interior (closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0}) :=
      interior_mono hsub (mem_interior_iff_mem_nhds.2 hev)
    rw [hint] at hy'
    exact hy'
  rintro ⟨k', y⟩ hz
  rw [hk] at hz
  obtain ⟨h1, hy⟩ := hz
  subst h1
  exact key y hy

theorem cusp_cancel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), NeatUnf U → ∀ (Z : Comp Xo c) (G : WTZ E) (e' : Ix Dw → ℤ) (f s : Rul Xo c), f ∈ cuspOn U Z G → f ≠ 0 → s ∈ secZ Xo c e' → (s * f = 0 → idem Z * s = 0) ∧ (e' none = 0 → ∀ σ, GoodEmb c σ → ∀ (q : FDSec (U σ).X), (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2) := by
  intro E _ _ _ H Dw l Xo c r U hL Z G e' f s hf hf0 hs
  exact ⟨idem_mul_eq_zero_of_mul_eq_zero hf hf0 hs,
    fun he σ hσ q hq hrel => rdU_cancel hL hσ hf hf0 he hs q hq hrel⟩

end Cancel

theorem archEx {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hL : NeatUnf U) (x : ℝ) : ArchEx U x := by
  intro Z τ
  obtain ⟨G, f, g, -, hf, hg, hf0, hq⟩ := exists_flat_pair E H Dw l Xo c r U hL Z τ
  have hfs : f ∈ secZ Xo c (exZ Dw G) := cuspW_le_secZ G hf.1
  have hgs : g ∈ secZ Xo c (exZ Dw (G + wtOf Dw (flatWt Dw τ) 0)) := cuspW_le_secZ _ hg.1
  have hex : exZ Dw (G + wtOf Dw (flatWt Dw τ) 0) - exZ Dw G = exOf Dw (flatWt Dw τ) 0 := by
    funext i; rw [Pi.sub_apply, exZ_add, exOf, add_sub_cancel_left]
  have hmem : ∀ σ (hσ : GoodEmb c σ) k, relab c σ τ.1 ∈ ((U σ).X k).Ψ := fun σ hσ k =>
    archEx_relab_mem (U σ) hσ (hL.unf σ hσ) τ k
  have hgood : ∀ σ, GoodEmb c (goodOf c σ) := fun σ => goodEmb_goodOf c σ
  have hσ₀ := hgood c.F.val.toRingHom
  generalize goodOf c c.F.val.toRingHom = σ₀ at hσ₀
  obtain ⟨a₀, ha₀, h₀⟩ := hq σ₀ hσ₀
  obtain ⟨sig, hsig, hsi, hsf⟩ := exists_quot E H Dw l Xo c r U hL Z _ _ f g hfs hf.2 hgs hg.2 hf0 σ₀ hσ₀
    (fun k y => a₀ * horizGen ⟨_, hmem σ₀ hσ₀ k⟩ y)
    (fun k => continuousOn_const.mul (archEx_continuousOn_horizGen _ _)) (fun z hz => h₀ z.1 _ z.2 hz)
  rw [hex] at hsig
  have hrd : ∀ σ (hσ : GoodEmb c σ), ∃ a : ℂ, a ≠ 0 ∧ ∀ z ∈ framesOn (U σ) Z,
      rdU (U σ) sig z.1 z.2 = a * horizGen ⟨_, hmem σ hσ z.1⟩ z.2 := fun σ hσ => by
    obtain ⟨a, ha, h⟩ := hq σ hσ
    exact ⟨a, ha, (cusp_cancel E H Dw l Xo c r U hL Z G _ f sig hf hf0 hsig).2 rfl σ hσ
      (fun k y => a * horizGen ⟨_, hmem σ hσ k⟩ y)
      (fun k => continuousOn_const.mul (archEx_continuousOn_horizGen _ _))
      (fun z hz => hsf.symm ▸ h z.1 _ z.2 hz)⟩
  have hnorm : ∀ σ (hσ : GoodEmb c σ), ∃ b : ℝ, 0 < b ∧
      homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) sig '' framesOn (U σ) Z = {b} := fun σ hσ => by
    obtain ⟨a, ha, h⟩ := hrd σ hσ
    obtain ⟨k, hk⟩ := framesOn_model E H Dw l Xo c r U hL Z σ hσ
    obtain ⟨y, hy⟩ := GlobalTheory.CompBij.frames_nonempty ((U σ).X k)
    refine ⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 ((U σ).X k).Gm.det‖),
      mul_pos (lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 ha) (Real.sqrt_pos.2 (norm_pos_iff.2
        ((map_ne_zero _).2 ((U σ).X k).Gm_det)))), image_eq_singleton_iff.2 ⟨⟨⟨k, y⟩, ?_⟩, ?_⟩⟩
    · rw [hk]; exact ⟨rfl, hy⟩
    · rintro ⟨k', y'⟩ hz
      have h1 := h _ hz
      have hz' := hz
      rw [hk] at hz'
      obtain ⟨rfl, hy'⟩ : k' = k ∧ y' ∈ ((U σ).X k').dom := hz'
      rw [← pnorm_horizGen ((U σ).X k') ⟨_, hmem σ hσ k'⟩ hy', homN, ptN,
        modelWt_flatWt (U σ) hσ (hL.unf σ hσ) τ k' (hmem σ hσ k')]
      simp only at h1
      simp only [Data.pnorm, h1, norm_mul, mul_assoc]
  have hg0 : g ≠ 0 := fun h0 => by
    have h1 : sig = 0 := hsi.symm.trans
      ((cusp_cancel E H Dw l Xo c r U hL Z G _ f sig hf hf0 hsig).1 (hsf.trans h0))
    obtain ⟨b, hb, h2⟩ := hnorm σ₀ hσ₀
    obtain ⟨⟨z, hz⟩, h3⟩ := image_eq_singleton_iff.1 h2
    have h4 := h3 z hz
    rw [h1, ← zero_smul c.F (0 : Rul Xo c), homN_smul, map_zero, norm_zero, zero_mul] at h4
    exact hb.ne h4
  obtain ⟨inv, hinv, hii, hig⟩ := exists_quot E H Dw l Xo c r U hL Z _ _ g f hgs hg.2 hfs hf.2 hg0 σ₀ hσ₀
    (fun k y => a₀⁻¹ * (mat y ⟨_, hmem σ₀ hσ₀ k⟩).det)
    (fun k => (continuous_const.mul (archEx_continuous_det _)).continuousOn) (fun z hz => by
      have hd := (hz.1 ⟨_, hmem σ₀ hσ₀ z.1⟩).1
      rw [h₀ z.1 (hmem σ₀ hσ₀ z.1) z.2 hz, horizGen]
      field_simp)
  rw [← neg_sub, hex] at hinv
  have hif : idem Z * f = f := by rw [← hig, ← mul_assoc, hii]
  have hs0 : sig * inv - idem Z ∈ secZ Xo c 0 := by
    have := mul_mem_secZ hsig hinv
    rw [add_neg_cancel] at this
    exact Submodule.sub_mem _ this (idem_mem_secZ Z)
  have hone : sig * inv = idem Z := by
    have h1 := (cusp_cancel E H Dw l Xo c r U hL Z G _ f _ hf hf0 hs0).1 (by
      rw [sub_mul, hif, mul_right_comm, hsf, mul_comm, hig, sub_self])
    rwa [mul_sub, ← mul_assoc, hsi, idem_mul_idem, sub_eq_zero] at h1
  choose b hb hb' using fun σ => hnorm _ (hgood σ)
  exact ⟨⟨sig, inv, hsig, hinv, hsi, hii, hone, b, hb, hb'⟩⟩

end Chain

end GlobalTheory.FlatAnyLevel

end

section Cover

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

theorem GlobalTheory.FlatAnyLevel.neatUnf_of_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ)
    (hG : Y.Good e o) : GlobalTheory.FlatAnyLevel.NeatUnf Y.U := by
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have hN : 3 ≤ D.host.g 0 * D.host.g 1 * Y.d.pd := by
    have h0 := (D.host.g_prime 0).two_le
    have h1 := (D.host.g_prime 1).two_le
    have hp : 1 ≤ Y.d.pd := by rw [hG.pd]; exact Nat.one_le_pow _ _ (by norm_num)
    have : 4 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul h0 h1
    nlinarith
  refine ⟨?_, hG.lev.2, hG.unf, hG.geo, fun σ hσ k k' => ?_, hG.chiTriv, fun σ hσ k γ hγ => ?_⟩
  · have e : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (hG.unf Y.d.c₂.F.val.toRingHom rfl).1
    omega
  · obtain ⟨_, hW⟩ := hG.modelW σ hσ
    exact ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  · obtain ⟨th, hrk, hth, hD⟩ := hG.dictU σ hσ
    exact GlobalTheory.LevLaws.det_eq_one _ hrk hr (Y.U σ).X (Y.dict σ) Y.Kf th hth hD (hG.unit σ hσ) _ hN hG.levelK k γ hγ

open GlobalTheory.FlatCore GlobalTheory.FlatLine GlobalTheory.AllWt in

theorem GlobalTheory.FlatAnyLevel.exists_flat_unit_bdd : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ s i : Rul Y.d.Xo₂ Y.d.c₂, s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C) := by
  intro _ D T j Y e o hG _
  refine ⟨1, one_pos, fun Z τ => ?_⟩
  obtain ⟨A⟩ := GlobalTheory.FlatAnyLevel.archEx (GlobalTheory.FlatAnyLevel.neatUnf_of_good D T j Y e o hG) (xiR D) Z τ
  simp only [Nat.cast_one, one_smul]
  refine ⟨A.sig, A.inv, A.sig_mem, A.inv_mem, A.idem_sig, A.idem_inv, A.mul_inv, fun σ hσ => ?_⟩
  have hg : goodOf Y.d.c₂ σ = σ := if_pos hσ
  have hn := A.norm_inf σ
  rw [hg] at hn
  refine ⟨max (A.cInf σ) (A.cInf σ)⁻¹, fun z hz => ?_⟩
  have hs : homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0) A.sig z = A.cInf σ := by
    have := hn ▸ Set.mem_image_of_mem _ hz
    exact this
  obtain ⟨hdom, hlies⟩ := hz
  have hpos := A.cInf_pos σ
  have ht := tested_of_homN_ne (U := Y.U σ) (x := xiR D) hdom (hs.trans_ne hpos.ne')
  have hi := homN_idem (U := Y.U σ) (x := xiR D) hdom hlies ht
  have hm := homN_mul (Y.U σ) (xiR D) (G := wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)
    (G' := -(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) ⟨0, by simp [wtOf_snd]⟩ ⟨0, by simp [wtOf_snd]⟩ A.sig A.inv z hdom
  rw [add_neg_cancel, A.mul_inv, hi, hs] at hm
  refine ⟨hs ▸ le_max_left _ _, ?_⟩
  have : homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) A.inv z = (A.cInf σ)⁻¹ := by
    field_simp
    linarith
  rw [this]; exact le_max_right _ _

end Cover
