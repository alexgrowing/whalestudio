import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylDimFormulaDualityBoundStatement
import Formalism.SharpRestriction.Divisibility.HookProducts.Compl3Record
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.DefSizes

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem r_sq_le {PP A : ℝ} (hH : HostNum D L PP A 1) : (D.R.r : ℝ) * D.R.r * L.sc.L ≤ L.sc.b := by
  obtain ⟨⟨-, hL, -, -⟩, hf, -, -, -, -, -, -, -, -, ⟨-, -, hpol⟩, hroom, -⟩ := hH
  rw [Real.rpow_one] at hroom
  have hf' : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hnV : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast (by unfold Ranks.nV; omega : D.R.r ≤ D.R.nV)
  have h0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : (D.R.r : ℝ) * D.R.r * L.sc.L ≤ D.R.f * D.R.r * D.R.nV * L.sc.L := by
    have : (D.R.r : ℝ) * D.R.r ≤ D.R.r * D.R.nV := mul_le_mul_of_nonneg_left hnV h0
    have h2 : (0 : ℝ) ≤ D.R.r * D.R.nV := by positivity
    have h3 : (D.R.r : ℝ) * D.R.r ≤ D.R.f * (D.R.r * D.R.nV) := by nlinarith
    have hL0 : (0 : ℝ) ≤ L.sc.L := by linarith
    nlinarith
  linarith

theorem spread_range_le {PP A : ℝ} (hW : WtNum p i PP) (hH : HostNum D L PP A 1) (hS : SizesAt L) (τ : Psi p.T.Q.H)
    (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) :
    ∑ n ∈ Finset.range D.R.r, |WtShape.entR D i t n - WtShape.entR D i t (D.R.k - 1 - 1)| ≤ 10 * D.R.m * L.sc.b := by
  have e3 : (dat p i).p + (dat p i).q = D.R.r := hW.sig.2.2
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [← Finset.sum_range_add_sum_Ico _ (show D.R.k - 1 ≤ D.R.r by omega)]
  have hL1 : 1 ≤ L.sc.L := by linarith [hH.big.2.1]
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  have hSc0 : 0 ≤ L.Sc := L.Sc_pos.le
  have hkS := Formalism.MainNotions.DIV.HookProducts.RBCompl3.kSc_le_b D L hS
  have hrr0 := r_sq_le hH
  have hrr : (D.R.r : ℝ) * D.R.r ≤ L.sc.b := by
    have : (D.R.r : ℝ) * D.R.r ≤ D.R.r * D.R.r * L.sc.L := le_mul_of_one_le_right (by positivity) hL1
    linarith
  have a1 : ∑ n ∈ Finset.range (D.R.k - 1), |WtShape.entR D i t n - WtShape.entR D i t (D.R.k - 1 - 1)| ≤
      ((D.R.k - 1 : ℕ) : ℝ) * (L.Sc + 2 * D.R.r) := by
    have := Finset.sum_le_card_nsmul (Finset.range (D.R.k - 1))
      (fun n => |WtShape.entR D i t n - WtShape.entR D i t (D.R.k - 1 - 1)|) (L.Sc + 2 * D.R.r) (fun n hn => by
        have hn' := Finset.mem_range.1 hn
        obtain ⟨c1, c2⟩ := WtShape.entR_cloud L i t n hn'
        obtain ⟨d1, d2⟩ := WtShape.entR_cloud L i t (D.R.k - 1 - 1) (by omega)
        rw [abs_le]; constructor <;> linarith)
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have a2 : ∑ n ∈ Finset.Ico (D.R.k - 1) D.R.r, |WtShape.entR D i t n - WtShape.entR D i t (D.R.k - 1 - 1)| ≤
      ((D.R.r - (D.R.k - 1) : ℕ) : ℝ) * (8 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul (Finset.Ico (D.R.k - 1) D.R.r)
      (fun n => |WtShape.entR D i t n - WtShape.entR D i t (D.R.k - 1 - 1)|) (8 * L.sc.b) (fun n hn => by
        have hn' := Finset.mem_Ico.1 hn
        have u1 := hW.up τ ⟨n, by omega⟩
        have u2 := hW.up τ ⟨D.R.k - 1 - 1, by omega⟩
        rw [WtShape.laOf_real p i τ t ht] at u1 u2
        have := abs_sub (WtShape.entR D i t n) (WtShape.entR D i t (D.R.k - 1 - 1))
        simp only at u1 u2 ⊢
        linarith)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this
  have e4 : ((D.R.r - (D.R.k - 1) : ℕ) : ℝ) = D.R.m := by rw [hr]; congr 1; omega
  have e5 : ((D.R.k - 1 : ℕ) : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k - 1 ≤ D.R.r)
  have e6 : ((D.R.k - 1 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.k - 1 ≤ D.R.k)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  rw [e4] at a2
  have h0 : (0 : ℝ) ≤ ((D.R.k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((D.R.k - 1 : ℕ) : ℝ) * L.Sc ≤ D.R.k * L.Sc := mul_le_mul_of_nonneg_right e6 hSc0
  have h2 : ((D.R.k - 1 : ℕ) : ℝ) * D.R.r ≤ D.R.r * D.R.r := mul_le_mul_of_nonneg_right e5 (Nat.cast_nonneg _)
  nlinarith

theorem spread_le {PP A : ℝ} (hW : WtNum p i PP) (hH : HostNum D L PP A 1) (hS : SizesAt L) (τ : Psi p.T.Q.H) :
    ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) - (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)| ≤
      10 * D.R.m * L.sc.b := by
  obtain ⟨t, ht⟩ := WtShape.exists_tau p τ
  have e3 : (dat p i).p + (dat p i).q = D.R.r := hW.sig.2.2
  have hsum : ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) -
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)| =
      ∑ n ∈ Finset.range ((dat p i).p + (dat p i).q),
        |WtShape.entR D i t n - WtShape.entR D i t (D.R.k - 1 - 1)| := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => |WtShape.entR D i t n - WtShape.entR D i t (D.R.k - 1 - 1)|)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [WtShape.laOf_real p i τ t ht, WtShape.anchor_real p i τ t ht]
  rw [hsum, e3]
  exact spread_range_le p i hW hH hS τ t ht

theorem logDim_le {PP A : ℝ} (hW : WtNum p i PP) (hH : HostNum D L PP A 1) (hS : SizesAt L)
    (hdim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ w : ℤ,
      (GlobalTheory.DualWeyl.dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2) (τ : Psi p.T.Q.H) :
    Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ) ≤ 3 * L.sc.b := by
  obtain ⟨t, ht⟩ := WtShape.exists_tau p τ
  have e3 : (dat p i).p + (dat p i).q = D.R.r := hW.sig.2.2
  have hmult : (dat p i).mult τ.1 = (dat p i).p := if_pos τ.2
  have hanti : Antitone (part (dat p i) (wtA (p.κ i)) τ.1) := fun a b hab => hW.dom.1 τ.1 hab
  set N := (dat p i).mult τ.1 with hN
  have hNr : N ≤ D.R.r := by omega
  set w : ℤ := anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ - (((p.κ i).n / 2 : ℕ) : ℤ) with hw
  have h1 := hdim N _ hanti w
  have hent : ∀ j : Fin N, |(((part (dat p i) (wtA (p.κ i)) τ.1 j : ℕ) : ℤ) : ℝ) - (w : ℝ)| =
      |WtShape.entR D i t j - WtShape.entR D i t (D.R.k - 1 - 1)| := by
    intro j
    have hj : (j : ℕ) < (dat p i).p := by have := j.2; omega
    have hl := WtShape.laOf_real p i τ t ht ⟨j, by omega⟩
    rw [← hl, ← WtShape.anchor_real p i τ t ht]
    congr 1
    simp only [hw, part, laOf, weightOf, if_pos hj]
    push_cast
    ring
  have hS1 : ∑ j : Fin N, |(((part (dat p i) (wtA (p.κ i)) τ.1 j : ℕ) : ℤ) : ℝ) - (w : ℝ)| ≤ 10 * D.R.m * L.sc.b := by
    rw [Finset.sum_congr rfl fun j _ => hent j,
      Fin.sum_univ_eq_sum_range (fun n => |WtShape.entR D i t n - WtShape.entR D i t (D.R.k - 1 - 1)|)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNr) fun _ _ _ => abs_nonneg _) ?_
    exact spread_range_le p i hW hH hS τ t ht
  set S := ∑ j : Fin N, |(((part (dat p i) (wtA (p.κ i)) τ.1 j : ℕ) : ℤ) : ℝ) - (w : ℝ)| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpos : (0 : ℝ) < GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) := by
    exact_mod_cast GlobalTheory.DualWeyl.dim_pos hanti
  have hL1 : 1 ≤ L.sc.L := by linarith [hH.big.2.1]
  have hb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : D.R.m ≤ D.R.r)
  have hm0 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hfr := hH.logfr.1
  have hlog11 : Real.log (11 * D.R.m) ≤ 1 + L.sc.L := by
    have c1 : (11 : ℝ) * D.R.m ≤ 2 * (D.R.f * D.R.r) := by nlinarith
    have c2 := Real.log_le_log (by positivity) c1
    have hfr0 : (D.R.f : ℝ) * D.R.r ≠ 0 := by
      have : (0 : ℝ) < D.R.f * D.R.r := mul_pos (by linarith) (by linarith)
      exact this.ne'
    rw [Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) hfr0] at c2
    linarith [Real.log_two_lt_d9]
  have hlogS : Real.log (S + 1) ≤ 1 + 2 * L.sc.L := by
    have c1 : S + 1 ≤ 11 * D.R.m * L.sc.b := by
      have : (1 : ℝ) ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
      nlinarith
    have c2 := Real.log_le_log (by positivity) c1
    rw [Real.log_mul (by positivity) hb0.ne', hb] at c2
    linarith
  have hc : ((N.choose 2 : ℕ) : ℝ) ≤ D.R.r * D.R.r := by
    have c1 : N.choose 2 ≤ N ^ 2 := Nat.choose_le_pow _ _
    have c2 : N ^ 2 ≤ D.R.r * D.R.r := by rw [sq]; exact Nat.mul_le_mul hNr hNr
    exact_mod_cast c1.trans c2
  have hlog1 : 0 ≤ Real.log (S + 1) := Real.log_nonneg (by linarith)
  calc Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)
      ≤ Real.log ((S + 1) ^ N.choose 2) := Real.log_le_log hpos h1
    _ = (N.choose 2 : ℕ) * Real.log (S + 1) := Real.log_pow _ _
    _ ≤ (D.R.r * D.R.r) * (1 + 2 * L.sc.L) := mul_le_mul hc hlogS hlog1 (by positivity)
    _ ≤ 3 * ((D.R.r : ℝ) * D.R.r * L.sc.L) := by nlinarith [sq_nonneg (D.R.r : ℝ)]
    _ ≤ 3 * L.sc.b := by linarith [r_sq_le hH]

end GlobalTheory.CovTop.DefSizes

namespace GlobalTheory.CovTop.DefSizes

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem abs_lrd_le {PP A : ℝ} (hH : HostNum D L PP A 1) : |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E| ≤ 2 * L.sc.L := by
  have hd : (1 : ℝ) ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
  have hdeg := hH.deg
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hdisc := hH.disc
  have e : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E =
      Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| / (2 * D.R.f) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd
    rw [NumberField.rootDiscr_def, Int.cast_abs, Real.log_rpow (by linarith), hdeg]
    push_cast
    field_simp
  have h0 : 0 ≤ Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| := Real.log_nonneg hd
  rw [e, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  nlinarith

theorem sizes_at {PP A : ℝ} (hW : WtNum p i PP) (hH : HostNum D L PP A 1) (hS : SizesAt L)
    (hdim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ w : ℤ,
      (GlobalTheory.DualWeyl.dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2) :
    |(ofRecord D L p.Del p.h0).logOm| * (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) -
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)|) +
      (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) +
      ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E| ≤
      35 * unitE p := by
  have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by
    rw [← Nat.card_eq_fintype_card, hW.card]
  have hL1 : 1 ≤ L.sc.L := by linarith [hH.big.2.1]
  have hLL := hH.big.2.2.2
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hm0 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hunit := hW.unit
  have hom := hW.om
  have t1 : ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) -
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)| ≤ D.R.f * (10 * D.R.m * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ _ _ fun τ _ => spread_le p i hW hH hS τ
    rwa [nsmul_eq_mul, Finset.card_univ, hcard] at this
  have t2 : ∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ) ≤
      D.R.f * (3 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ _ _ fun τ _ => logDim_le p i hW hH hS hdim τ
    rwa [nsmul_eq_mul, Finset.card_univ, hcard] at this
  have t3 : ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E| ≤
      2 * L.sc.b := by
    obtain ⟨-, -, hpol⟩ := hH.poly
    have hroom := hH.room
    rw [Real.rpow_one] at hroom
    have hp : ((dat p i).p : ℝ) ≤ D.R.r := by exact_mod_cast (by have := hW.sig.2.2; omega : (dat p i).p ≤ D.R.r)
    rw [hcard, hW.cols]
    have hl := abs_lrd_le hH
    have h0 : (0 : ℝ) ≤ (D.R.nV : ℝ) * D.R.f := by positivity
    calc (D.R.nV : ℝ) * D.R.f * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E|
        ≤ (D.R.nV : ℝ) * D.R.f * D.R.r * (2 * L.sc.L) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp h0) hl (abs_nonneg _) (by positivity)
      _ = 2 * (D.R.f * D.R.r * D.R.nV * L.sc.L) := by ring
      _ ≤ 2 * L.sc.b := by linarith
  have hsp : 0 ≤ ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) -
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have t1' := mul_le_mul hom t1 hsp (by positivity)
  have hU : D.R.f * D.R.m * L.sc.b * L.sc.L ≤ unitE p := by
    rw [hunit]
    have : (0 : ℝ) ≤ D.R.f * D.R.m * L.sc.b * L.sc.L := by positivity
    nlinarith
  have hfmb : (0 : ℝ) ≤ D.R.f * L.sc.b := by positivity
  have k1 : D.R.f * L.sc.b ≤ D.R.f * D.R.m * L.sc.b * L.sc.L := by
    have : (1 : ℝ) ≤ D.R.m * L.sc.L := by nlinarith
    nlinarith
  have k2 : L.sc.b ≤ D.R.f * L.sc.b := le_mul_of_one_le_left (by linarith) (by linarith)
  nlinarith

end GlobalTheory.CovTop.DefSizes

namespace GlobalTheory.CovTop.DefSizes

theorem sizes :
    Lifts fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → |(ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| *
      (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) -
        (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) τ : ℝ)|) +
      (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) +
      ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd (Fm.D x ι).host.E| ≤
      C * unitE p := by
  have hdim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ w : ℤ,
      (GlobalTheory.DualWeyl.dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := fun n la h => (GlobalTheory.T.dualWeyl_dim_formula_duality_bound n la h).2.2
  have H := Closed.and WtShape.wtN (Sizes.hostN 1)
  simp only [WtN, HostN, Lifts] at H
  unfold Lifts
  refine Closed.imp H ?_
  intro eps Fm CH _ h
  obtain ⟨⟨C1, -, hw⟩, ⟨A, -, hh⟩⟩ := h
  obtain ⟨x0, h⟩ := EvTied.and hw hh
  exact ⟨35, by norm_num, x0, fun x hx hle ι p hp i _ =>
    sizes_at p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i) (Fm.sizes x hx ι) hdim⟩

end GlobalTheory.CovTop.DefSizes

end
