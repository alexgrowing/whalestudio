import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.LocalRingCardinality.SpanPowerMembership.EntPlNonempty
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoicesKernelDatumAdaptedBasesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeLayerTrueColumnsParametersFreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlaceStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparisonStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.WLeWjOne

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.CloudRec

def ScaleOK (K : Ctx) : Prop :=
  ∀ R : Ranks, RankVal K.s R →
    16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) + R.k + 2 ≤ K.s.w'' R.n ∧ K.s.w'' R.n ≤ K.s.b

theorem scaleOK_large (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (cD : ℝ) (hcD : 0 ≤ cD) :
    ∃ x1 : ℝ, ∀ K : Ctx, K.s.eps = eps → K.cD = cD → x1 ≤ K.s.x → ScaleOK K := by
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (cD + 6) (1 / 2) he (by norm_num)
  obtain ⟨x3, hx3⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  refine ⟨max 35 (max x2 x3), fun K e1 e2 hx R hR => ?_⟩
  have h35 : 35 ≤ K.s.x := le_trans (le_max_left _ _) hx
  have hxa : x2 ≤ K.s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxb : x3 ≤ K.s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hf, -, hr, hkr, -⟩ := hx3 K.s R e1 hxb hR
  have hx0 : 0 < K.s.x := by linarith
  have hx1 : 1 ≤ K.s.x := by linarith
  have hn1 : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have hn3 : (R.n : ℝ) ≤ K.s.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    simp only [Ranks.f]; push_cast
    have : (0:ℝ) ≤ R.n := Nat.cast_nonneg _
    linarith
  have H := hx2 K.s e1 hxa
  obtain ⟨-, -, -, hb'b, -, hw, -⟩ := H
  obtain ⟨hw1, hw2, -⟩ := hw R.n hn1 hn3
  have hL0 : 0 ≤ K.s.L := by unfold Scale.L; positivity
  have hb1 : 1 ≤ K.s.b := by unfold Scale.b; exact Real.one_le_exp hL0
  have hbk : 1 ≤ K.s.b ^ (1 - (1 / 2 : ℝ)) := Real.one_le_rpow hb1 (by norm_num)
  have hxc0 : 0 ≤ K.s.x ^ (cD + 6) := by positivity
  have hxc : K.s.x ^ (cD + 6) ≤ K.s.w'' R.n := by
    calc K.s.x ^ (cD + 6) = 1 * K.s.x ^ (cD + 6) := by ring
      _ ≤ K.s.b ^ (1 - (1 / 2 : ℝ)) * K.s.x ^ (cD + 6) := by gcongr
      _ ≤ _ := hw1
  have hxc1 : 1 ≤ K.s.x ^ (cD + 0) := by rw [add_zero]; exact Real.one_le_rpow hx1 hcD
  have hD : (Delv K.s K.cD : ℝ) ≤ 2 * K.s.x ^ cD := by
    unfold Delv
    rw [e2]
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le cD)
    rw [add_zero] at hxc1
    linarith
  have hk5 : (R.k : ℝ) ≤ K.s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hsplit : K.s.x ^ (cD + 6) = K.s.x ^ cD * K.s.x ^ (5 : ℝ) * K.s.x := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']; ring_nf
  have hxcD : 1 ≤ K.s.x ^ cD := by rw [add_zero] at hxc1; exact hxc1
  have hx5 : 1 ≤ K.s.x ^ (5 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hk0 : (0 : ℝ) ≤ R.k := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (Delv K.s K.cD : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, le_trans hw2 ?_⟩
  · have h1 : 16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) ≤ 32 * (K.s.x ^ cD * K.s.x ^ (5 : ℝ)) := by
      calc 16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) ≤ 16 * K.s.x ^ (5 : ℝ) * (2 * K.s.x ^ cD) := by gcongr
        _ = _ := by ring
    have h2 : 1 ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) := one_le_mul_of_one_le_of_one_le hxcD hx5
    have h3 : (R.k : ℝ) ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) := le_trans hk5 (le_mul_of_one_le_left (by linarith) hxcD)
    have h4 : 35 * (K.s.x ^ cD * K.s.x ^ (5 : ℝ)) ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) * K.s.x := by
      rw [mul_comm 35]; gcongr
    linarith
  · have := hb'b
    have h0 : 0 ≤ K.s.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
    have hx6 : 1 ≤ K.s.x ^ (cD + 6) := Real.one_le_rpow hx1 (by linarith)
    nlinarith

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl.CloudRec

theorem facts_pre {K : Ctx} (hS : ScaleOK K) {Bp : Pre} (hO : K.Over Bp) :
    (1 : ℝ) ≤ (Delv K.s K.cD : ℝ) ∧
    (∀ u (τ : Tau Bp.R) (i : Fin Bp.R.k), 1 ≤ i.1 → i.1 + 1 < Bp.R.k →
      3 * (Delv K.s K.cD : ℝ) - 1 / 2 ≤ (((Bp.hcW u τ).u i : ℚ) : ℝ) ∧
      (((Bp.hcW u τ).u i : ℚ) : ℝ) ≤ 4 * (Bp.R.k : ℝ) * (Delv K.s K.cD : ℝ)) ∧
    (∀ u (τ : Tau Bp.R) (hk : 0 < Bp.R.k), (τ : Bp.R.GG) ∉ Bp.host.topPlaces →
      (((Bp.hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ) =
        ((Bp.R.k - 2 : ℕ) : ℝ) * (4 * (Delv K.s K.cD : ℝ)) + (Bp.R.k : ℝ) * (4 * (Delv K.s K.cD : ℝ)) + 1 / 2 ∧
      (((Bp.hcW u τ).u ⟨Bp.R.k - 1, by omega⟩ : ℚ) : ℝ) = -1 / 2) ∧
    (∀ u (τ : Tau Bp.R) (hm : 0 < Bp.R.m),
      16 * (Bp.R.k : ℝ) * (Delv K.s K.cD : ℝ) + ((Bp.R.k : ℝ) + Bp.R.t + 1) / 2 + 1 ≤ (((Bp.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ)) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hO
  dsimp only [Pre.ofCh]
  have ok := K.ok
  have hx1 : 1 < K.s.x := K.s.one_lt_alt
  have hx0 : 0 < K.s.x := by linarith
  have hD1 : (1 : ℝ) ≤ (Delv K.s K.cD : ℝ) := by
    unfold Delv
    have h : 0 < K.s.x ^ K.cD := Real.rpow_pos_of_pos hx0 _
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
      intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
  obtain ⟨hS1, hS2⟩ := hS K.P.R ok.rank
  refine ⟨hD1, ?_, ?_, ?_⟩
  · intro u τ i hi1 hi2
    have hv := (ok.hc u).1
    have hcode := ok.code u τ (i.1 - 1) (by omega)
    have e : (⟨i.1 - 1 + 1, by omega⟩ : Fin K.P.R.k) = i := Fin.ext (by simp only; omega)
    rw [e, hv τ ⟨i.1 - 1, by omega⟩] at hcode
    have hcR := congrArg (Rat.cast (K := ℝ)) hcode
    rw [hcR]
    have hl1 : 1 ≤ K.P.R.k - 2 - (i.1 - 1) := by omega
    have hl2 : K.P.R.k - 2 - (i.1 - 1) ≤ K.P.R.k := by omega
    have c1 : (1 : ℝ) ≤ ((K.P.R.k - 2 - (i.1 - 1) : ℕ) : ℝ) := by exact_mod_cast hl1
    have c2 : ((K.P.R.k - 2 - (i.1 - 1) : ℕ) : ℝ) ≤ K.P.R.k := by exact_mod_cast hl2
    have hD0 : (0 : ℝ) ≤ (Delv K.s K.cD : ℝ) := by linarith
    split_ifs <;> push_cast <;> constructor <;> nlinarith
  · intro u τ hk htop
    have h := (ok.hc u).2.1 τ hk htop
    constructor
    · have := congrArg (Rat.cast (K := ℝ)) h.1
      rw [this]; push_cast; ring
    · have := congrArg (Rat.cast (K := ℝ)) h.2
      rw [this]; push_cast; ring
  · intro u τ hm
    obtain ⟨b1, hb, htopb, hthick, hthin⟩ := (ok.hc u).2.2.1
    have hgap := (K.P.hcW u τ).gap_be ⟨0, hm⟩
    have hb0 := (hb τ ⟨0, hm⟩).1
    simp only [Nat.cast_zero, zero_mul, add_zero] at hb0
    rw [hb0] at hgap
    have hgapR : ((K.P.R.t : ℝ) + 3) / 2 ≤ (((K.P.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ) - (b1 τ : ℝ) := by
      have h' := (Rat.cast_le (K := ℝ)).2 hgap
      push_cast at h'
      linarith
    have hwb : K.s.w'' K.P.R.n ≤ (b1 τ : ℝ) + 1 := by
      by_cases ht : (τ : K.P.R.GG) ∈ K.P.H.topPlaces
      · obtain ⟨t, htT, hte⟩ := Finset.mem_image.1 ht
        have e1 := htopb τ ⟨t, htT⟩ hte.symm
        have hwin := (ok.win t htT).2.1
        rw [e1]
        push_cast
        have hfl := Int.sub_one_lt_floor (K.s.b' / K.s.x)
        have hb'0 : 0 ≤ K.s.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
        have hn1 : (1 : ℝ) ≤ K.P.R.n := by exact_mod_cast (Formalism.HC.Frame.ord_pos _ : 1 ≤ K.P.R.n)
        have hw'' : K.s.w'' K.P.R.n ≤ K.s.b' / K.s.x := by
          unfold Scale.w''
          rw [div_le_div_iff₀ (by positivity) hx0]
          have : K.s.b' * K.s.x ≤ K.s.b' * (K.s.x * K.P.R.n) := by
            apply mul_le_mul_of_nonneg_left _ hb'0; nlinarith
          linarith
        have hbt : K.s.b' ≤ ((K.b t : ℤ) : ℝ) := hwin
        nlinarith
      · by_cases hth : (τ : K.P.R.GG) ∈ K.P.H.thickPlaces
        · have h1 := (hthick τ hth).1
          have hc : K.s.b ≤ (⌈K.s.b⌉ : ℝ) := Int.le_ceil _
          have h2 : ((⌈K.s.b⌉ : ℤ) : ℝ) ≤ ((b1 τ : ℤ) : ℝ) := by exact_mod_cast h1
          linarith
        · have := hthin τ ⟨τ.2, ht, hth⟩
          rw [this]
          have := Int.le_ceil (K.s.w'' K.P.R.n)
          linarith
    have hk0 : (0 : ℝ) ≤ K.P.R.k := Nat.cast_nonneg _
    linarith

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl.CloudRec

theorem cloudBound_of (D : D7) (Δ : ℕ) (hD1 : 1 ≤ Δ)
    (hmid : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
      3 * (Δ : ℝ) - 1 / 2 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ 4 * (D.R.k : ℝ) * Δ)
    (hoff : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (hk : 0 < D.R.k),
      ((D.eTau τ : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces →
      (((D.hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ) = ((D.R.k - 2 : ℕ) : ℝ) * (4 * (Δ : ℝ)) + (D.R.k : ℝ) * (4 * (Δ : ℝ)) + 1 / 2 ∧
      (((D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) = -1 / 2)
    (hfill : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (hm : 0 < D.R.m),
      16 * (D.R.k : ℝ) * Δ + ((D.R.k : ℝ) + D.R.t + 1) / 2 + 1 ≤ (((D.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ))
    (u : D.what₂.Word) : Formalism.L2.G.CloudBound D u (16 * D.R.k * Δ) := by
  have hD1R : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hD1
  have hk5 : 5 ≤ D.R.k := by have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k; omega
  have hkR : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  have hc : (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) = 16 * (D.R.k : ℝ) * (Δ : ℝ) := by push_cast; ring
  have hmidL : ∀ (g : D.R.Psi) (i : Fin (D.R.k - 1 + 1)), 0 < i.val → i.val < D.R.k - 1 →
      |Formalism.L2.G.lamRec D u g i| ≤ ((16 * D.R.k * Δ : ℕ) : ℤ) := by
    intro g i h0 h1
    have hi : i.1 < D.R.k := by omega
    have h := Formalism.L2.G.lamRec_real D u g i hi
    have hb := hmid u (D.eTau.symm g) ⟨i.1, hi⟩ h0 (by show i.1 + 1 < D.R.k; omega)
    have hiR : (i.1 : ℝ) + 1 ≤ (D.R.k : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
    have h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) := by
      rw [h, hc, abs_le]
      constructor <;> nlinarith [hb.1, hb.2]
    exact_mod_cast h2
  refine ⟨fun g _ i h0 h1 => hmidL g i h0 h1, fun g hg i => ?_, fun g => ?_⟩
  · have hg' : ((D.eTau (D.eTau.symm g) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces := by
      rwa [Equiv.apply_symm_apply]
    have hk0 : 0 < D.R.k := by omega
    obtain ⟨e0, e1⟩ := hoff u (D.eTau.symm g) hk0 hg'
    by_cases h0 : i.val = 0
    · have hi : i.1 < D.R.k := by omega
      have h := Formalism.L2.G.lamRec_real D u g i hi
      have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨0, hk0⟩ := Fin.ext h0
      rw [e, e0, h0] at h
      have hk2 : ((D.R.k - 2 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast Nat.sub_le _ _
      have hk2' : (0 : ℝ) ≤ ((D.R.k - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) := by
        rw [h, hc, abs_le]
        push_cast
        constructor <;> nlinarith
      exact_mod_cast h2
    · by_cases h1 : i.val < D.R.k - 1
      · exact hmidL g i (Nat.pos_of_ne_zero h0) h1
      · have hi1 : i.val = D.R.k - 1 := by have := i.2; omega
        have hi : i.1 < D.R.k := by omega
        have h := Formalism.L2.G.lamRec_real D u g i hi
        have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext hi1
        have hkR1 : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [e, e1, hi1, hkR1] at h
        have h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) := by
          rw [h, hc, abs_le]
          constructor <;> nlinarith
        exact_mod_cast h2
  · have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
    have h1 : (1 : ℕ) ∈ SizeData₂.lifts D := Finset.mem_Icc.2 ⟨le_rfl, by have := D.R.two_le_m; omega⟩
    have hw := Formalism.L2.G.wRec_eq D u g 1 h1
    have hf := hfill u (D.eTau.symm g) hm
    have hfe : (((D.hcW u (D.eTau.symm g)).e ⟨0, hm⟩ : ℚ) : ℝ) = Formalism.BasicNotions.wj D 1 (D.eTau.symm g) := by
      unfold Formalism.BasicNotions.wj
      rw [dif_pos (by omega), D.hcW_e]
    rw [hfe] at hf
    have hka : Formalism.MainNotions.G.kaJ D 1 = ((D.R.k : ℝ) + D.R.t + 1) / 2 := by
      unfold Formalism.MainNotions.G.kaJ; push_cast; ring
    have h2 : (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) ≤ ((Formalism.L2.G.wRec D u g 1 : ℤ) : ℝ) := by
      rw [hw, hka, hc]; linarith
    exact_mod_cast h2

theorem cloudBound_rec {K : Ctx} (hS : ScaleOK K) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (hO : K.Over B.toPre) (Z : w.Lt) (u : (w.D Z).what₂.Word) :
    Formalism.L2.G.CloudBound (w.D Z) u (16 * (w.D Z).R.k * Delv K.s K.cD) := by
  obtain ⟨hD1, hmid, hoff, hfill⟩ := facts_pre hS hO
  exact cloudBound_of (w.D Z) (Delv K.s K.cD) (by exact_mod_cast hD1) (fun u τ i h1 h2 => hmid u τ i h1 h2)
    (fun u τ hk h => hoff u τ hk h) (fun u τ hm => hfill u τ hm) u

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl.CloudRec

theorem evG_scaleOK : EvG ScaleOK := by
  obtain ⟨ε0, hε0, H⟩ := evG_good
  refine ⟨ε0, hε0, fun eps C8 C5 c6 Cb he h1 h2 h3 => ?_⟩
  obtain ⟨K0, HK⟩ := H eps C8 C5 c6 Cb he h1 h2 h3
  refine ⟨K0, fun C hC h4 h5 => ?_⟩
  obtain ⟨c1, H1⟩ := HK C hC h4 h5
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, H2⟩ := H1 cD (le_trans (le_max_left _ _) hcD)
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, -⟩ := H2 ch hch
  obtain ⟨x1, hx1⟩ := scaleOK_large eps he h2 cD (le_trans (le_max_right _ _) hcD)
  exact ⟨max x0 x1, fun K _ e2 _ e4 e5 _ => hx1 K e4 e2 (le_trans (le_max_right _ _) e5)⟩

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl

theorem cloudBound_step : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧
    ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L :=
  Step.of_evG (CloudRec.evG_scaleOK.imp fun K _ _ _ _ hS B _ _ hO _ _ _ w _ Z =>
    ⟨16 * (w.D Z).R.k * Delv K.s K.cD, CloudRec.cloudBound_rec hS w hO Z, fun L hL hV => by
      unfold G.cG
      rw [L.Sc_eq, hV.Del_eq, hL]
      push_cast
      linarith⟩)

end GlobalTheory.Mem.Top.Bl
