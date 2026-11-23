import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.NuHost
import Formalism.SharpRestriction.GlobalTheoremInputs
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitBoundOfParamsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.SemisimpleDecompositionOf
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.ElevenLe
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkTyp

theorem typePrime_size_terms_le_elementary (n t r nV f η eta vdel constantSecondHub C1 x : ℝ) (hf : f = 2 * n) (hnV0 : 0 ≤ nV) (hnV : nV ≤ 2 * t)
    (hr0 : 0 ≤ r) (hr : r ≤ t) (he0 : 0 ≤ eta) (he : eta ≤ η) (ht1 : 1 ≤ t) (hte : t ≤ η) (hn1 : 1 ≤ n)
    (hnx : n ≤ x ^ C1) (htx : t ≤ x ^ C1) (hv0 : 0 ≤ vdel) (hv : vdel ≤ 2 * t) (hC68 : 0 ≤ constantSecondHub) (hC1 : 1 ≤ C1)
    (hx : 1 ≤ x) :
    4 * f * nV * (constantSecondHub * nV ^ 2 * (nV + eta + t)) + 2 * f * r ^ 2 + 4 * nV * vdel ≤
      (2000 * (constantSecondHub + 1) + 5 * C1) * x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * η := by
  have hη1 : 1 ≤ η := ht1.trans hte
  have ht0 : 0 ≤ t := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hη0 : 0 ≤ η := by linarith
  have e1 : nV ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have e2 : nV + eta + t ≤ 4 * η := by linarith
  have eT : constantSecondHub * nV ^ 2 * (nV + eta + t) ≤ constantSecondHub * (4 * t ^ 2) * (4 * η) := by
    have h0 : 0 ≤ nV + eta + t := by linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hC68) e2 h0 (by positivity)
  have A : 4 * f * nV * (constantSecondHub * nV ^ 2 * (nV + eta + t)) ≤ 256 * constantSecondHub * (n * t ^ 3) * η := by
    rw [hf]
    have h1 : 4 * (2 * n) * nV ≤ 4 * (2 * n) * (2 * t) := mul_le_mul_of_nonneg_left hnV (by positivity)
    have h2 : 0 ≤ constantSecondHub * nV ^ 2 * (nV + eta + t) := by
      have : 0 ≤ nV + eta + t := by linarith
      positivity
    calc 4 * (2 * n) * nV * (constantSecondHub * nV ^ 2 * (nV + eta + t))
        ≤ 4 * (2 * n) * (2 * t) * (constantSecondHub * (4 * t ^ 2) * (4 * η)) :=
          mul_le_mul h1 eT h2 (by positivity)
      _ = 256 * constantSecondHub * (n * t ^ 3) * η := by ring
  have ht3 : t ^ 2 ≤ t ^ 3 := by nlinarith
  have B : 2 * f * r ^ 2 ≤ 4 * (n * t ^ 3) * η := by
    rw [hf]
    have h1 : r ^ 2 ≤ t ^ 2 := by nlinarith
    have h2 : n * t ^ 3 ≤ n * t ^ 3 * η := le_mul_of_one_le_right (by positivity) hη1
    nlinarith [mul_le_mul_of_nonneg_left h1 hn0, mul_le_mul_of_nonneg_left ht3 hn0]
  have Cc : 4 * nV * vdel ≤ 16 * (n * t ^ 3) * η := by
    have h1 : 4 * nV * vdel ≤ 4 * (2 * t) * (2 * t) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnV (by norm_num)) hv hv0 (by positivity)
    have h2 : t ^ 2 ≤ n * t ^ 3 := by nlinarith
    have h3 : n * t ^ 3 ≤ n * t ^ 3 * η := le_mul_of_one_le_right (by positivity) hη1
    nlinarith
  have hX0 : 0 ≤ x ^ C1 := Real.rpow_nonneg (by linarith) _
  have hnt : n * t ^ 3 ≤ x ^ (4 * C1) := by
    have : x ^ (4 * C1) = x ^ C1 * (x ^ C1) ^ 3 := by
      rw [show (4 : ℝ) * C1 = C1 + C1 * (3 : ℕ) by push_cast; ring, Real.rpow_add (by linarith),
        Real.rpow_mul_natCast (by linarith : (0 : ℝ) ≤ x)]
    rw [this]
    exact mul_le_mul hnx (pow_le_pow_left₀ ht0 htx 3) (by positivity) hX0
  have hexp : x ^ (4 * C1) ≤ x ^ (2000 * (constantSecondHub + 1) + 5 * C1) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hK : 256 * constantSecondHub + 20 ≤ 2000 * (constantSecondHub + 1) + 5 * C1 := by linarith
  have hxC0 : 0 ≤ x ^ (2000 * (constantSecondHub + 1) + 5 * C1) := Real.rpow_nonneg (by linarith) _
  have hsum : 4 * f * nV * (constantSecondHub * nV ^ 2 * (nV + eta + t)) + 2 * f * r ^ 2 + 4 * nV * vdel ≤
      (256 * constantSecondHub + 20) * (n * t ^ 3) * η := by nlinarith
  calc _ ≤ (256 * constantSecondHub + 20) * (n * t ^ 3) * η := hsum
    _ ≤ (2000 * (constantSecondHub + 1) + 5 * C1) * x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * η := by
        apply mul_le_mul_of_nonneg_right _ hη0
        exact mul_le_mul hK (hnt.trans hexp) (by positivity) (by linarith)

end GlobalTheory.NLinkTyp

namespace GlobalTheory.NLinkTyp

open Classical in

theorem starH_of_local {D : D7} (L : SizeData₂ D) (C : ℝ)
    (hloc : ∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∈ TwistedPlaces.gset D →
      (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) *
        (C * L.sc.x ^ C * L.etaSz + TwistedPlaces.epsL (D.nd.l i) + TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) +
          TwistedPlaces.epsL (D.nd.l i)))
    (hM : ∀ l ∈ TwistedPlaces.gset D,
      0 ≤ C * L.sc.x ^ C * L.etaSz + TwistedPlaces.epsL l + TwistedPlaces.VVr D l + TwistedPlaces.vhE D l + TwistedPlaces.epsL l)
    (hmult : MultLe L) (h3 : TwistedPlaces.adm3 L) : StarH L C := by
  intro j hj l hl
  set M := C * L.sc.x ^ C * L.etaSz + TwistedPlaces.epsL l + TwistedPlaces.VVr D l + TwistedPlaces.vhE D l + TwistedPlaces.epsL l with hMdef
  have hM0 : 0 ≤ M := hM l hl
  have hlp : l.Prime := by
    unfold TwistedPlaces.gset at hl
    rcases Finset.mem_insert.1 hl with h | h
    · rw [h]; exact D.host.g_prime 0
    · rw [Finset.mem_singleton.1 h]; exact D.host.g_prime 1
  have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
  have hw : ∀ w ∈ TwistedPlaces.twAt L l, (D.what₂.etaJ j w : ℝ) ≤ (L.dZ0 j : ℝ) * M := by
    intro w hw
    obtain ⟨_, htw, hres⟩ := TwistedPlaces.mem_twAt.1 hw
    rw [D.etaJ_tie j w hj'.1 hj'.2]
    push_cast
    calc ∑ i ∈ D.nd.locs j w, (D.nd.etaLoc i : ℝ)
        ≤ ∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * M := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hli : D.nd.l i = l := by
            rw [← D.nd.w_l i, ((D.nd.locs_mem j w i).1 hi).2, hres]
          have := hloc i (htw.twLoc hi) (hli ▸ hl)
          rw [hli] at this
          exact this
      _ = (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) * M := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
      _ ≤ (L.zeroSpaceRankAtPlace j w : ℝ) * M := mul_le_mul_of_nonneg_right (hmult j hj w htw) hM0
      _ = (L.dZ0 j : ℝ) * M := by rw [h3 j hj w htw]
  unfold TwistedPlaces.etaAt
  have hnn : ∀ w, 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := fun w =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  calc ∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ)
      ≤ ∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * ((L.dZ0 j : ℝ) * M) :=
        Finset.sum_le_sum fun w h => mul_le_mul_of_nonneg_left (hw w h) (hnn w)
    _ = (∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * ((L.dZ0 j : ℝ) * M) := by
        rw [Finset.sum_mul]
    _ ≤ Real.log l * ((L.dZ0 j : ℝ) * M) :=
        mul_le_mul_of_nonneg_right (TwistedPlaces.admissibleMeanCondition_holds L l hlp) (mul_nonneg (Nat.cast_nonneg _) hM0)
    _ = Real.log l * (L.dZ0 j : ℝ) * M := by ring

end GlobalTheory.NLinkTyp

namespace GlobalTheory.NLinkTyp

theorem rhs_le {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (constantSecondHub C1 : ℝ) (hC68 : 0 ≤ constantSecondHub)
    (hC1 : 1 ≤ C1) (hpar : TwistedPlaces.ParametersPolynomiallyBounded L C1 P) (heta : (X.eta : ℝ) ≤ L.etaSz) (hK : KillingConditions.KillAt X.ρ)
    (i : D.nd.Loc) (hi : TwistedPlaces.TwLoc D i) (hl2 : D.nd.l i ∉ D.host.small) (hν : TwistedPlaces.nuL D (D.nd.l i) = 0) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) :
    PairedCharacterCondition.rhs constantSecondHub X.eta i (X.ρ i) π ≤
      (2000 * (constantSecondHub + 1) + 5 * C1) * L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * L.etaSz + TwistedPlaces.epsL (D.nd.l i) +
        TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) + TwistedPlaces.epsL (D.nd.l i) := by
  have hK1 := ((hK i hi).1 π hπ).2
  rw [hν, zero_add] at hK1
  have hK2 := (hK i hi).2
  have hVV : TwistedPlaces.VVr D (D.nd.l i) = ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℝ) := by
    have : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
      show ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) = _
      congr 2
    rw [this]
    push_cast
    rfl
  have hvh : TwistedPlaces.vhE D (D.nd.l i) = (padicValNat (D.nd.l i) (hE D.host) : ℝ) := rfl
  have hZ : (∑ q ∈ D.nd.Q i, (PairedCharacterCondition.vZeta i q : ℝ)) = ((∑ v ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) := by
    push_cast
    rfl

  have htr := TwistedPlaces.t_ge D
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hv0 : (0 : ℝ) ≤ (D.nd.vdel i : ℝ) := by
    have : (0 : ℚ) ≤ D.nd.vdel i := by unfold NData.vdel; positivity
    exact_mod_cast this
  have hv : (D.nd.vdel i : ℝ) ≤ 2 * D.R.t := by
    have h1 := LargeLevelLemmas.vdel_le (D := D) i
    rw [UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hl2] at h1
    have h2 : (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) ≤ D.R.t := by
      exact_mod_cast padicValNat_factorial_le (D.nd.l i) D.R.t
    have h3 : D.nd.vdel i ≤ 2 * (D.R.t : ℚ) := by push_cast at h1; linarith
    exact_mod_cast h3
  have hS := typePrime_size_terms_le_elementary (D.R.n : ℝ) D.R.t D.R.r D.R.nV D.R.f L.etaSz (X.eta : ℝ) (D.nd.vdel i : ℝ) constantSecondHub C1 L.sc.x
    (TwistedPlaces.f_eq D) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) heta
    (TwistedPlaces.t_ge_one D) (TwistedPlaces.t_le_eta L P) (TwistedPlaces.n_ge_one D) hpar.2.2.2.1 hpar.2.2.2.2.1 hv0 hv hC68 hC1
    L.sc.one_lt_alt.le
  unfold PairedCharacterCondition.rhs PairedCharacterCondition.eT
  rw [hVV, hvh, hZ]
  linarith

end GlobalTheory.NLinkTyp

namespace GlobalTheory.NLinkTyp

theorem g_two_lt {D : D7} (L : SizeData₂ D) (hG : SizeG L) (k : Fin 2) : 2 < D.host.g k := by
  have h := (hG k k).1
  have hk : (5 : ℝ) ≤ D.R.k := TwistedPlaces.k_ge_five D
  have hb : 1 ≤ L.sc.b := by
    rw [TwistedPlaces.b_eq]
    exact Real.one_le_exp (by linarith [TwistedPlaces.L_ge_one L])
  have h5 : (5 : ℝ) ≤ D.R.k * L.sc.b := by nlinarith
  have h8 : (5 : ℝ) ^ 8 ≤ (D.R.k * L.sc.b) ^ 8 := pow_le_pow_left₀ (by norm_num) h5 8
  have : (2 : ℝ) < D.host.g k := by nlinarith
  exact_mod_cast this

theorem etaLoc_le_rhs (hPr : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (X : KillingConditions.HubData D) (C₂ : ℝ) (hS : Setup L nch HW X C₂) (constantSecondHub : ℝ) (CT : ℕ)
    (hCT : (CT : ℝ) ≤ L.sc.b) (h68 : PairedCharacterCondition.aux₃ (D := D) constantSecondHub CT) (hG : SizeG L)
    (i : D.nd.Loc) (hi : TwistedPlaces.TwLoc D i) (k k' : Fin 2) (hkk : k ≠ k') (hlk : D.nd.l i = D.host.g k) :
    (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * PairedCharacterCondition.rhs constantSecondHub X.eta i (X.ρ i) π := by
  by_cases hHG : HG D.nd D.naut i
  · have hX := GlobalTheory.T.split_bound_of_params hPr.font hPr.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 CT hS.canon P
      (by linarith [hS.big]) (by norm_num) hCT (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
      hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
      hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hT, -⟩ := hX
    obtain ⟨hgood, hZρ, s, S, sg, U, hs, hCTg, hsg, hHJ, hSQ⟩ := hT i k hi hlk hHG
    have hAN : SumRepresentations.adm5 D := hS.facts.toCore.admA.2.2.2.2.2.2
    have hl2 : 2 < D.nd.l i := hlk ▸ g_two_lt L hG k
    have hodd : Odd (D.nd.l i) := (D.nd.lPrime i).out.odd_of_ne_two (by omega)
    have hlog : Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ) := by
      have h1 := (hG k' k).2.1
      have hg0 : (0 : ℝ) < D.host.g k' := by exact_mod_cast (D.host.g_prime k').pos
      have hg2 : (2 : ℝ) ≤ D.host.g k := by exact_mod_cast (D.host.g_prime k).two_le
      have h2 := Real.log_le_log hg0 h1
      rw [Real.log_mul (by norm_num) (by linarith)] at h2
      have h3 : Real.log 2 ≤ Real.log (D.host.g k : ℝ) := Real.log_le_log (by norm_num) hg2
      linarith
    have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
      intro e he
      rw [Finset.mem_Ioo] at he
      exact lt_top_iff_ne_top.2 (hS.sha (D.nd.l i) e he.1 he.2)
    exact h68 i k k' hkk hlk (X.r i) (X.ρ i) hgood
      (fun π hπ => semisimple_decomposition_of D i (X.r i) (X.ρ i) π hAN hgood (hZρ π hπ).1 (hZρ π hπ).2)
      X.eta s S sg U hs hlog hCTg hsg hHJ hSQ (fun π hπ => ((hS.kill i hi).1 π hπ).1) hsha
  · have hZ : D.nd.Zgood i = ∅ :=
      Finset.eq_empty_of_forall_notMem fun x hx => hHG ⟨x, (D.Zgood_tie i x).1 hx⟩
    have hP := TruncatedSeriesCountingIdentities.endomorphism_index_bound i (D.nd.Zgood i) (Formalism.L2.zgoodSub D i) 0 1 one_ne_zero
      (fun f => by simp) (fun x hx => by rw [hZ] at hx; simp at hx) (fun x _ _ u _ => by simp)
    rw [← TruncatedSeriesCountingIdentities.Br.etaLoc_eq, hZ, Finset.sum_empty] at hP
    rw [hZ, Finset.sum_empty]
    exact_mod_cast hP

end GlobalTheory.NLinkTyp

namespace GlobalTheory.NLinkTyp

theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ (constantSecondHub C1 : ℝ) (CT : ℕ), 0 ≤ constantSecondHub → 1 ≤ C1 → (CT : ℝ) ≤ L.sc.b → PairedCharacterCondition.aux₃ (D := D) constantSecondHub CT → MultLe L → TwistedPlaces.ParametersPolynomiallyBounded L C1 P → SizeG L → StarH L (2000 * (constantSecondHub + 1) + 5 * C1) := by
  intro hPr D L P nch HW F _ X C₂ hS constantSecondHub C1 CT hC68 hC1 hCT h68 hmult hpar hG
  have heta : (X.eta : ℝ) ≤ L.etaSz := by
    rw [hS.canon.eta]
    exact Nat.floor_le (by linarith [TwistedPlaces.one_le_eta L P])
  have hM : ∀ l ∈ TwistedPlaces.gset D, 0 ≤ (2000 * (constantSecondHub + 1) + 5 * C1) * L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * L.etaSz +
      TwistedPlaces.epsL l + TwistedPlaces.VVr D l + TwistedPlaces.vhE D l + TwistedPlaces.epsL l := by
    intro l _
    have h1 : 0 ≤ L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1) := Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
    have h2 : 0 ≤ L.etaSz := by linarith [TwistedPlaces.one_le_eta L P]
    have h3 : 0 ≤ TwistedPlaces.epsL l := by unfold TwistedPlaces.epsL; positivity
    have h4 : 0 ≤ TwistedPlaces.VVr D l := by
      show (0 : ℝ) ≤ ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen l e : ℚ) : ℝ)
      exact_mod_cast Finset.sum_nonneg fun e _ => D.what₂.shaLen_nonneg l e
    have h5 : 0 ≤ TwistedPlaces.vhE D l := by unfold TwistedPlaces.vhE; positivity
    have h6 : 0 ≤ 2000 * (constantSecondHub + 1) + 5 * C1 := by linarith
    have := mul_nonneg (mul_nonneg h6 h1) h2
    linarith
  refine starH_of_local L _ (fun i hi hl => ?_) hM hmult (hS.facts.toCore.a3 L)
  have hk : ∃ k k' : Fin 2, k ≠ k' ∧ D.nd.l i = D.host.g k := by
    unfold TwistedPlaces.gset at hl
    rcases Finset.mem_insert.1 hl with h | h
    · exact ⟨0, 1, by decide, h⟩
    · exact ⟨1, 0, by decide, Finset.mem_singleton.1 h⟩
  obtain ⟨k, k', hkk, hlk⟩ := hk
  have hl2 : D.nd.l i ≠ 2 := by have := g_two_lt L hG k; omega
  refine (etaLoc_le_rhs hPr D L P nch HW F X C₂ hS constantSecondHub CT hCT h68 hG i hi k k' hkk hlk).trans ?_
  refine Finset.sum_le_sum fun π hπ => ?_
  exact mul_le_mul_of_nonneg_left (rhs_le L P X constantSecondHub C1 hC68 hC1 hpar heta hS.kill i hi
    (by rw [hlk]; exact UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k))
    (UpperTheory.KStar.nuL_eq_zero_of_g D _ (by rw [hlk]; fin_cases k <;> simp [TwistedPlaces.gset]) hl2) π hπ) (Nat.cast_nonneg _)

end GlobalTheory.NLinkTyp
