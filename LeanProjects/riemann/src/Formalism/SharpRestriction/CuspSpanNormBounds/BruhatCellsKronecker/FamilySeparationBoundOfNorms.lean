import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyExponentOfFormalDegree
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaFactorisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmRingIdempotentUnitRatioIdentity
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset
open scoped nonZeroDivisors NumberField

theorem szf_alg (κ rd g C A N I : ℝ) (a e n : ℕ) (hκ : 0 < κ) (hrd : 0 < rd) (hg : 0 < g) (hI : 0 < I)
    (h : a + e = n) :
    C * (((κ * rd / g) ^ n)⁻¹ * A) * (C * (κ * rd / g) * N / I) ^ a * (rd ^ e * g) =
      C * (g ^ (n + 1) * ((κ ^ n)⁻¹ * A)) * (C * κ * N / (g * I)) ^ a := by
  subst h
  have e1 : C * (κ * rd / g) * N / I = (C * κ * N / (g * I)) * rd := by field_simp
  rw [e1, mul_pow]
  generalize (C * κ * N / (g * I)) ^ a = X
  have e2 : ((κ * rd / g) ^ (a + e))⁻¹ = g ^ (a + e) * (κ ^ (a + e))⁻¹ * (rd ^ a)⁻¹ * (rd ^ e)⁻¹ := by
    rw [div_pow, mul_pow, pow_add rd]
    field_simp
  rw [e2]
  have h1 : rd ^ a ≠ 0 := (pow_pos hrd a).ne'
  have h2 : rd ^ e ≠ 0 := (pow_pos hrd e).ne'
  field_simp
  ring

theorem szf_algP (κ rd g C A N I S : ℝ) (j e n : ℕ) (hκ : 0 < κ) (hrd : 0 < rd) (hg : 0 < g) (hI : 0 < I)
    (h : 2 * j + 1 + 2 * e = n) :
    (rd ^ e * g) ^ 2 * (C * (((κ * rd / g) ^ n)⁻¹ * A) * (κ * rd / g) ^ (2 * j + 1) * S * (C * N / I) ^ (2 * j)) =
      C * (g ^ (n + 1) * ((κ ^ n)⁻¹ * A)) * (g ^ (2 * j))⁻¹ * κ * (C * κ * N / I) ^ (2 * j) * S := by
  subst h
  have e1 : C * κ * N / I = (C * N / I) * κ := by ring
  rw [e1, mul_pow (C * N / I)]
  generalize (C * N / I) ^ (2 * j) = X
  have hk0 : 0 < κ * rd / g := by positivity
  have e2 : ((κ * rd / g) ^ (2 * j + 1 + 2 * e))⁻¹ * (κ * rd / g) ^ (2 * j + 1) = ((κ * rd / g) ^ (2 * e))⁻¹ := by
    rw [pow_add]
    have := (pow_pos hk0 (2 * j + 1)).ne'
    field_simp
  have e3 : C * (((κ * rd / g) ^ (2 * j + 1 + 2 * e))⁻¹ * A) * (κ * rd / g) ^ (2 * j + 1) =
      C * A * ((κ * rd / g) ^ (2 * e))⁻¹ := by rw [← e2]; ring
  rw [e3]
  have e4 : κ ^ (2 * j + 1 + 2 * e) = κ ^ (2 * j) * κ * κ ^ (2 * e) := by rw [pow_add, pow_succ]
  have e5 : g ^ (2 * j + 1 + 2 * e + 1) = g ^ (2 * j) * g ^ (2 * e) * g ^ 2 := by ring
  have e6 : (rd ^ e * g) ^ 2 = rd ^ (2 * e) * g ^ 2 := by ring
  rw [e6, div_pow, mul_pow κ rd, e4, e5]
  have h1 := (pow_pos hrd (2 * e)).ne'
  have h2 := (pow_pos hκ (2 * e)).ne'
  have h3 := (pow_pos hκ (2 * j)).ne'
  have h4 := (pow_pos hg (2 * j)).ne'
  have h5 := (pow_pos hg (2 * e)).ne'
  field_simp

theorem szf_zpow (κ : ℝ) (r : ℕ) : κ ^ (-(1 + 2 * (r : ℤ))) = (κ ^ (2 * r + 1))⁻¹ := by
  rw [zpow_neg, show (1 + 2 * (r : ℤ)) = ((2 * r + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

theorem szf_supBe (D : D7) (κ T T' : ℝ) (x : LocalDataRealPlace D) (J : Set ℝ) (hκ : 0 < κ) :
    supBe D κ T T' x J = (κ ^ (2 * D.R.rS + 1))⁻¹ * supBe D 1 T T' x J := by
  unfold supBe
  have hfun : beS κ D.R.rS x.lam T T' x.u x.u' =
      fun Y => (κ ^ (2 * D.R.rS + 1))⁻¹ • beS 1 D.R.rS x.lam T T' x.u x.u' Y := by
    funext Y
    simp only [beS, szf_zpow, one_pow, inv_one, one_mul, smul_eq_mul]
  rw [hfun, ← Set.image_image (fun y => (κ ^ (2 * D.R.rS + 1))⁻¹ • y), Set.image_smul,
    Real.sSup_smul_of_nonneg (by positivity), smul_eq_mul]

theorem szf_beS_cast (R : Ranks) (P : HCParam R) {k : ℕ} (κ T T' : ℝ) (u u' : Fin k → ℝ) (Y : ℝ) :
    beS κ R.rS (lamSH R P) T T' u u' Y = beS κ R.rS (lamS R P) T T' u u' Y := by
  have hc : ∀ Z : ℂ, Formalism.QuantumDeterminants.capP (fun s => (lamSH R P s : ℂ)) Z = Formalism.QuantumDeterminants.capP (fun s => (lamS R P s : ℂ)) Z := by
    intro Z
    unfold Formalism.QuantumDeterminants.capP lamSH
    exact Fintype.prod_equiv (finCongr (dimS_eq R)) _ _ (fun s => rfl)
  unfold beS
  rw [hc, hc]

def SzfNormDD (D : D7) : Prop :=
  ((FractionalIdeal.absNorm (ddE D) : ℚ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2

def SzfNormG (D : D7) : Prop :=
  ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D)) : ℚ) : ℝ) = (gg D ^ D.R.f) ^ 2

theorem szf_gg_pos (D : D7) : 0 < gg D := by
  unfold gg
  have h0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have h1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  positivity

theorem szf_nrm (D : D7) (hdd : SzfNormDD D) (hgn : SzfNormG D) (e : ℕ) :
    nrmHalf D (ddE D ^ (-(e : ℤ)) * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹) =
      ((D.host.rdE ^ e * gg D) ^ D.R.f)⁻¹ := by
  have hrd := rdE_pos D
  have hg := szf_gg_pos D
  unfold nrmHalf
  rw [map_mul, map_zpow₀, map_inv₀]
  push_cast
  rw [hdd, hgn]
  have : ((D.host.rdE ^ D.R.f) ^ 2) ^ (-(e : ℤ)) * ((gg D ^ D.R.f) ^ 2)⁻¹ =
      (((D.host.rdE ^ e * gg D) ^ D.R.f)⁻¹) ^ 2 := by
    rw [zpow_neg, zpow_natCast, ← mul_inv, inv_pow]
    congr 1
    ring
  rw [this, Real.sqrt_sq (by positivity)]

theorem szf_card_Tau (D : D7) : Fintype.card D.what₂.Tau = D.R.f := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr D.eTau]
  exact (factCardPsi D.R D.host).1

theorem szf_kaV (D : D7) (v : D.what₂.Tau) : kaV D (gE D) v = D.host.ka * D.host.rdE / gg D := by
  have hrd := rdE_pos D
  unfold kaV gE gg
  rw [map_natCast, Complex.norm_natCast, ka_eq]
  push_cast
  field_simp

theorem szf_prodAbs {D : D7} {large₂ : SizeData₂ D} {C' Cl Cu C0 : ℝ} (F : TfFacts D large₂ C' Cl Cu C0)
    (hA : UnitaryVolumeMass.cTvA D) (u : D.what₂.Word) : ∏ τ, |Tcrit D u τ / Tr D u| ≤ C0 * Real.exp 9 := by
  have hk1 : 1 ≤ D.R.k := le_trans (by norm_num) (five_le_k D)
  have hC0 := F.hC0
  by_contra hlt
  have hlt := not_le.1 hlt
  have hpos : 0 ≤ C0 * Real.exp 9 := by positivity
  have h1 : (C0 * Real.exp 9) ^ D.R.k < (∏ τ, |Tcrit D u τ / Tr D u|) ^ D.R.k :=
    pow_lt_pow_left₀ hlt hpos (by omega)
  have h2 : (∏ τ, |Tcrit D u τ / Tr D u|) ^ D.R.k = ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun τ _ => D.R.k_even.pow_abs _)
  have h3 := (hA u).1
  have h4 := F.ratio_le u
  have h5 := F.Gam_le u
  have h6 := F.E_le
  set E := (D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k) with hE
  set Pk := ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k with hPk
  have h7 : Pk ≤ Real.exp E * (C0 * Real.exp ((D.R.k : ℝ) / 4)) := by
    have : Real.exp (-E) * Pk ≤ C0 * Real.exp ((D.R.k : ℝ) / 4) := by
      refine le_trans h3 (le_trans h4 ?_)
      exact mul_le_mul_of_nonneg_left h5 (by linarith)
    have h8 : Pk = Real.exp E * (Real.exp (-E) * Pk) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [h8]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  have h9 : Real.exp E * (C0 * Real.exp ((D.R.k : ℝ) / 4)) ≤ (C0 * Real.exp 9) ^ D.R.k := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have a1 : C0 ≤ C0 ^ D.R.k := le_self_pow₀ hC0 (by omega)
    have a2 : Real.exp E * Real.exp ((D.R.k : ℝ) / 4) ≤ Real.exp ((D.R.k : ℝ) * 9) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast hk1
      linarith
    calc Real.exp E * (C0 * Real.exp ((D.R.k : ℝ) / 4)) = C0 * (Real.exp E * Real.exp ((D.R.k : ℝ) / 4)) := by ring
      _ ≤ C0 ^ D.R.k * Real.exp ((D.R.k : ℝ) * 9) :=
        mul_le_mul a1 a2 (by positivity) (by positivity)
  rw [h2] at h1
  linarith

theorem product_local_ratios_le {D : D7} {large₂ : SizeData₂ D} {C' Cl Cu C0 : ℝ} (F : TfFacts D large₂ C' Cl Cu C0)
    (hA : UnitaryVolumeMass.cTvA D) (u u' : D.what₂.Word) : ∏ τ, tV D u u' τ ≤ C0 * Real.exp 9 := by
  have h1 := szf_prodAbs F hA u
  have h2 := szf_prodAbs F hA u'
  have hle : ∀ τ, tV D u u' τ ≤ Real.sqrt |Tcrit D u τ / Tr D u| * Real.sqrt |Tcrit D u' τ / Tr D u'| := by
    intro τ
    unfold tV
    rw [← Real.sqrt_mul (abs_nonneg _), ← abs_mul]
    refine Real.sqrt_le_sqrt ?_
    have : Tcrit D u τ * Tcrit D u' τ / (Tr D u * Tr D u') = Tcrit D u τ / Tr D u * (Tcrit D u' τ / Tr D u') := by
      rw [div_mul_div_comm]
    rw [this]
    exact le_abs_self _
  calc ∏ τ, tV D u u' τ ≤ ∏ τ, (Real.sqrt |Tcrit D u τ / Tr D u| * Real.sqrt |Tcrit D u' τ / Tr D u'|) :=
        Finset.prod_le_prod (fun τ _ => Real.sqrt_nonneg _) (fun τ _ => hle τ)
    _ = Real.sqrt (∏ τ, |Tcrit D u τ / Tr D u|) * Real.sqrt (∏ τ, |Tcrit D u' τ / Tr D u'|) := by
        rw [Finset.prod_mul_distrib]
        congr 1 <;>
        · rw [Real.sqrt_eq_rpow, ← Real.finsetProd_rpow _ _ (fun τ _ => abs_nonneg _)]
          exact Finset.prod_congr rfl (fun τ _ => by rw [Real.sqrt_eq_rpow])
    _ ≤ Real.sqrt (C0 * Real.exp 9) * Real.sqrt (C0 * Real.exp 9) :=
        mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = C0 * Real.exp 9 := Real.mul_self_sqrt (by have := F.hC0; positivity)

theorem szf_elem (D : D7) (hka : 0 < D.host.ka) (CA N T T' I : ℝ) (hI : 0 < I) (x : LocalDataRealPlace D) (J : Set ℝ) (a e : ℕ)
    (hae : a + e = 2 * D.R.rS + 1) :
    CA * supBe D (D.host.ka * D.host.rdE / gg D) T T' x J * (CA * (D.host.ka * D.host.rdE / gg D) * N / I) ^ a *
        (D.host.rdE ^ e * gg D) =
      CA * (gg D ^ D.R.m * supBe D D.host.ka T T' x J) * (CA * D.host.ka * N / (gg D * I)) ^ a := by
  have hrd := rdE_pos D
  have hg := szf_gg_pos D
  rw [szf_supBe D _ T T' x J (by positivity), szf_supBe D _ T T' x J hka, m_eq D]
  exact szf_alg _ _ _ CA _ N I a e _ hka hrd hg hI hae

theorem szf_aaV (D : D7) (L : LatticeDataWithDual D) (hL : IsLatGLOB D L) (i s e : ℕ) (he : e + 2 * i + s = 2 * D.R.rS + 4) :
    L.aaV i s = ddE D ^ (-((e : ℕ) : ℤ)) * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹ := by
  rw [(hL i s).1]
  congr 2
  omega

theorem szf_aaP (D : D7) (L : LatticeDataWithDual D) (hL : IsLatGLOB D L) (i s e : ℕ) (he : e + 2 * i + s = 2 * D.R.rS + 3) :
    L.aaP i s = ddE D ^ (-((e : ℕ) : ℤ)) * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹ := by
  rw [(hL i s).2.1]
  congr 2
  omega

theorem szf_div_prod (D : D7) (F : D.what₂.Tau → ℝ) (c : ℝ) :
    (∏ v, F v) / (c ^ D.R.f)⁻¹ = ∏ v, F v * c := by
  rw [div_inv_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, szf_card_Tau]

theorem product_formula_first (D : D7) (hdd : SzfNormDD D) (hgn : SzfNormG D) (hka : 0 < D.host.ka) (CA N T T' I : ℝ) (hI : 0 < I)
    (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (hL : IsLatGLOB D L) (hba : ∀ v, (x v).b - (x v).a = I)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ D.R.rS + 1) :
    (∏ v, xSz D CA CA N (kaV D (gE D) v) T T' (x v) i) / nrmHalf D (L.aaV i 1) =
      ∏ v, Sz.xHat i CA D.host.ka N I (gg D) (gg D ^ D.R.m * supBe D D.host.ka T T' (x v)
        (if i = 1 then Set.Icc (x v).a1 (x v).b1 else Set.Icc (x v).a (x v).b)) := by
  obtain ⟨e, he⟩ : ∃ e, e + 2 * i + 1 = 2 * D.R.rS + 4 := ⟨2 * D.R.rS + 3 - 2 * i, by omega⟩
  rw [szf_aaV D L hL i 1 e he, szf_nrm D hdd hgn e, szf_div_prod]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  unfold xSz Sz.xHat
  rw [szf_kaV, hba v]
  exact szf_elem D hka CA N T T' I hI (x v) _ (2 * i - 2) e (by omega)

theorem product_formula_second (D : D7) (hdd : SzfNormDD D) (hgn : SzfNormG D) (hka : 0 < D.host.ka) (CA N T T' I : ℝ) (hI : 0 < I)
    (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (hL : IsLatGLOB D L) (hba : ∀ v, (x v).b - (x v).a = I)
    (i s : ℕ) (hi1 : 1 ≤ i) (hs : 2 ≤ s) (his : i - 1 + s ≤ D.R.rS + 1) :
    (∏ v, LamSz D CA CA N (kaV D (gE D) v) T T' (x v) i s) /
        min (nrmHalf D (L.aaV i s)) (nrmHalf D (L.aaP i (s - 1))) =
      ∏ v, Sz.lamHat i s CA D.host.ka N I (gg D) (gg D ^ D.R.m * supBe D D.host.ka T T' (x v)
        (Set.Icc (x v).a (x v).b)) := by
  obtain ⟨e, he⟩ : ∃ e, e + 2 * i + s = 2 * D.R.rS + 4 := ⟨2 * D.R.rS + 4 - 2 * i - s, by omega⟩
  rw [szf_aaV D L hL i s e he, szf_aaP D L hL i (s - 1) e (by omega), min_self, szf_nrm D hdd hgn e, szf_div_prod]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  unfold LamSz Sz.lamHat
  rw [szf_kaV, hba v]
  exact szf_elem D hka CA N T T' I hI (x v) _ (2 * (i - 1) + s - 1) e (by omega)

theorem product_formula_third (D : D7) (hdd : SzfNormDD D) (hgn : SzfNormG D) (hka : 0 < D.host.ka) (CA N T T' I : ℝ) (hI : 0 < I)
    (hTT : 0 < T * T')
    (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (hL : IsLatGLOB D L) (hba : ∀ v, (x v).b - (x v).a = I)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ D.R.rS) :
    (∏ v, LamPSz D CA CA N (kaV D (gE D) v) T T' (x v) i) / nrmHalf D (L.aaP i (D.R.rS + 2 - i)) =
      ∏ v, Sz.lamPrimeHat i CA D.host.ka N I (gg D) (gg D ^ D.R.m * supBe D D.host.ka T T' (x v)
        (Set.Icc (x v).a (x v).b)) (T * T') := by
  have hrd := rdE_pos D
  have hg := szf_gg_pos D
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, e + j + 1 = D.R.rS + 1 := ⟨D.R.rS - j, by omega⟩
  rw [szf_aaP D L hL (j + 1) (D.R.rS + 2 - (j + 1)) e (by omega), szf_nrm D hdd hgn e, szf_div_prod]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  unfold LamPSz Sz.lamPrimeHat
  rw [szf_kaV, hba v, show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1 - 1) = 2 * j by omega,
    show 2 * (j + 1) - 2 = 2 * j by omega, mul_comm (Real.sqrt _),
    ← Real.sqrt_sq (show 0 ≤ D.host.rdE ^ e * gg D by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [szf_supBe D _ T T' (x v) _ (show 0 < D.host.ka * D.host.rdE / gg D by positivity),
    szf_supBe D _ T T' (x v) _ hka, m_eq D,
    show (Real.sqrt (T * T'))⁻¹ = (T * T') ^ (-(1 / 2 : ℝ)) by rw [Real.sqrt_eq_rpow, Real.rpow_neg hTT.le]]
  exact szf_algP _ _ _ CA _ N I _ j e _ hka hrd hg hI (by omega)

theorem szf_sup {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT C4 : ℝ}
    (hh : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT) (h2e : LocalBesselAndTopKernel.BesselBoundOneSlotDifference D C4)
    (u u' : D.what₂.Word) (l : ℕ) (hl1 : 1 ≤ l) (hl2 : l ≤ D.R.k - 2) (τ : D.what₂.Tau)
    (hne : uOne D u τ (l + 1) ≠ uOne D u' τ (l + 1))
    (x : LocalDataRealPlace D) (hlam : x.lam = lamSH D.R (D.hc τ)) (hu : x.u = uS D u τ) (hu' : x.u' = uS D u' τ)
    (dmax : ℝ) (hd1 : 5 / 2 ≤ dmax) (hd2 : dmax ≤ (D.s.Del : ℝ) / 2) :
    0 < gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') x (Set.Icc (5 / 2 - vOne D τ l) (dmax - vOne D τ l)) ∧
    gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') x (Set.Icc (5 / 2 - vOne D τ l) (dmax - vOne D τ l)) ≤
      tV D u u' τ * (D.R.k : ℝ) ^ C4 * Real.sqrt (dmax / D.s.Del) := by
  obtain ⟨h5, hv, hg25⟩ := sze_facts hh
  have hg := szf_gg_pos D
  have hgm : 0 < gg D ^ D.R.m := pow_pos hg _
  have hka := ka_pos_of hv
  have hk5 := five_le_k D
  have hDel : (0 : ℝ) < D.s.Del := by exact_mod_cast D.s.Del_pos
  have hfun : ∀ Y, beS D.host.ka D.R.rS x.lam (Tr D u) (Tr D u') x.u x.u' Y = beUU D D.host.ka u u' τ Y := by
    intro Y
    rw [hlam, hu, hu', szf_beS_cast]
    rfl
  set Bd := tV D u u' τ * (D.R.k : ℝ) ^ C4 * Real.sqrt (dmax / D.s.Del) with hBd
  have hval : ∀ Y ∈ Set.Icc (5 / 2 - vOne D τ l) (dmax - vOne D τ l), gg D ^ D.R.m * beUU D D.host.ka u u' τ Y ≤ Bd := by
    intro Y hY
    have e : Y = (Y + vOne D τ l) - vOne D τ l := by ring
    have h := h2e u u' τ l hl1 hl2 hne (Y + vOne D τ l) (by linarith [hY.1]) (by linarith [hY.2])
    rw [← e] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
    exact div_le_div_of_nonneg_right (by linarith [hY.2]) hDel.le
  have hbdd : BddAbove (beS D.host.ka D.R.rS x.lam (Tr D u) (Tr D u') x.u x.u' ''
      Set.Icc (5 / 2 - vOne D τ l) (dmax - vOne D τ l)) := by
    refine ⟨Bd / gg D ^ D.R.m, ?_⟩
    rintro _ ⟨Y, hY, rfl⟩
    rw [hfun, le_div_iff₀ hgm, mul_comm]
    exact hval Y hY
  have hY0 : (5 / 2 - vOne D τ l) ∈ Set.Icc (5 / 2 - vOne D τ l) (dmax - vOne D τ l) := ⟨le_rfl, by linarith⟩
  constructor
  · refine mul_pos hgm (lt_of_lt_of_le ?_ (le_csSup hbdd ⟨_, hY0, rfl⟩))
    rw [hfun, beUU_eq D u u' τ (fun w => h5 τ w)]
    have hm := mem_cutI D τ l hl1 hl2 (5 / 2) le_rfl (by linarith)
    obtain ⟨q0, p0, p1, -⟩ := Formalism.FourierDecayAlt.P.betaFactorisation (cfgOf D τ) (deOf D u) (deOf D u') D.host.ka (Tr D u)
      (Tr D u') (5 / 2 - vOne D τ l) l (cfg_ok hh.1 hh.2.1 τ) (isWord_deOf D u) (isWord_deOf D u') (Tr_pos D u)
      (Tr_pos D u') hl1 (by show l + 2 ≤ D.R.k; omega) (deOf_ne D u u' τ (fun w => h5 τ w) l hl1 hl2 hne) hm.2
    unfold Sz.Cfg.be Sz.Cfg.core
    refine mul_pos (inv_pos.2 (pow_pos hka _)) (Real.sqrt_pos.2 (abs_pos.2 ?_))
    exact div_ne_zero (mul_ne_zero p0 p1) q0
  · unfold supBe
    rw [← le_div_iff₀' hgm]
    refine csSup_le ⟨_, _, hY0, rfl⟩ ?_
    rintro _ ⟨Y, hY, rfl⟩
    rw [hfun, le_div_iff₀' hgm]
    exact hval Y hY

theorem szf_num (k Δ TTs Ct C N X4 LinearSubstitution : ℝ) (hk : 1 ≤ k) (hC : 1 ≤ C) (hCt : 1 ≤ Ct) (hN0 : 0 < N) (hN : N ≤ 10 * k)
    (hX4 : 1 ≤ X4) (hX5 : 1 ≤ LinearSubstitution) (hK : 4000 * Ct ^ 2 * C ^ 2 ≤ k)
    (hΔ : X4 ^ 2 * LinearSubstitution ^ 2 * k ^ 4 ≤ Δ) (hT : X4 * LinearSubstitution ^ 2 * k ≤ TTs) :
    0 < Δ / 2 - 5 / 2 ∧ N ^ 3 ≤ Δ / 2 ∧ C * Real.pi * N / (Δ / 2 - 5 / 2) ≤ 1 ∧
    LinearSubstitution ≤ Real.sqrt (Δ / (X4 ^ 2 * N ^ 3)) / (Ct * C * 1) ∧
    LinearSubstitution ≤ (Δ / 2 - 5 / 2) / (Real.pi * Ct * C ^ 2 * 1 * X4 * N) ∧
    LinearSubstitution ≤ Real.sqrt (TTs / (Real.pi * Ct * C * 1 * X4)) := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  have hCt2 : Ct ≤ Ct ^ 2 := le_self_pow₀ hCt (by norm_num)
  have hC2 : C ≤ C ^ 2 := le_self_pow₀ hC (by norm_num)
  have h1C2 : 1 ≤ C ^ 2 := one_le_pow₀ hC
  have h1Ct2 : 1 ≤ Ct ^ 2 := one_le_pow₀ hCt
  set Q := Ct ^ 2 * C ^ 2 with hQ
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le h1Ct2 h1C2
  have hQk : Q ≤ k / 4000 := by
    rw [le_div_iff₀ (by norm_num)]
    have : 4000 * Ct ^ 2 * C ^ 2 = Q * 4000 := by rw [hQ]; ring
    linarith
  have hk4000 : 4000 ≤ k := by
    have := le_trans hQ1 hQk
    rw [le_div_iff₀ (by norm_num)] at this
    linarith
  set W := X4 ^ 2 * LinearSubstitution ^ 2 with hW
  have hW1 : 1 ≤ W := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hX4) (one_le_pow₀ hX5)
  have hk0 : 0 < k := by linarith
  have hk24 : k ^ 2 ≤ k ^ 4 := pow_le_pow_right₀ hk (by norm_num)
  have hk14 : k ≤ k ^ 4 := le_self_pow₀ hk (by norm_num)
  have hk4 : k ^ 4 ≤ W * k ^ 4 := le_mul_of_one_le_left (by positivity) hW1
  have hWk2 : W * k ^ 2 ≤ W * k ^ 4 := mul_le_mul_of_nonneg_left hk24 (by linarith)
  have hI4 : W * k ^ 4 / 4 ≤ Δ / 2 - 5 / 2 := by linarith
  have hI : 0 < Δ / 2 - 5 / 2 := by linarith
  have hN3 : N ^ 3 ≤ 1000 * k ^ 3 := by
    have := pow_le_pow_left₀ hN0.le hN 3
    calc N ^ 3 ≤ (10 * k) ^ 3 := this
      _ = 1000 * k ^ 3 := by ring
  have hk34 : 4000 * k ^ 3 ≤ k ^ 4 := by
    have : k ^ 4 = k * k ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hk4000 (by positivity)
  have q2 : LinearSubstitution * (Real.pi * Ct * C ^ 2 * 1 * X4 * N) ≤ Δ / 2 - 5 / 2 := by
    have hXX : X4 * LinearSubstitution ≤ W := mul_le_mul (le_self_pow₀ hX4 (by norm_num)) (le_self_pow₀ hX5 (by norm_num))
      (by linarith) (by positivity)
    have hCC : Ct * C ^ 2 ≤ k / 4000 := le_trans (mul_le_mul_of_nonneg_right hCt2 (by positivity)) hQk
    have hin : Real.pi * (Ct * C ^ 2) * N ≤ 4 * (k / 4000) * (10 * k) :=
      mul_le_mul (mul_le_mul hpi4 hCC (by positivity) (by norm_num)) hN hN0.le (by positivity)
    calc LinearSubstitution * (Real.pi * Ct * C ^ 2 * 1 * X4 * N) = (X4 * LinearSubstitution) * (Real.pi * (Ct * C ^ 2) * N) := by ring
      _ ≤ W * (4 * (k / 4000) * (10 * k)) := mul_le_mul hXX hin (by positivity) (by linarith)
      _ = W * k ^ 2 / 100 := by ring
      _ ≤ Δ / 2 - 5 / 2 := by
        have : 0 ≤ W * k ^ 2 := by positivity
        linarith
  refine ⟨hI, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [div_le_one hI]
    refine le_trans ?_ q2
    have h1 : C * Real.pi * N = 1 * (Real.pi * 1 * C * 1 * 1 * N) := by ring
    rw [h1]
    have : Real.pi * 1 * C * 1 * 1 * N ≤ Real.pi * Ct * C ^ 2 * 1 * X4 * N := by gcongr
    exact mul_le_mul hX5 this (by positivity) (by linarith)
  · rw [le_div_iff₀ (by positivity)]
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ (by positivity)]
    calc (LinearSubstitution * (Ct * C * 1)) ^ 2 * (X4 ^ 2 * N ^ 3) = W * (Q * N ^ 3) := by rw [hW, hQ]; ring
      _ ≤ W * ((k / 4000) * (1000 * k ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hQk hN3 (by positivity) (by positivity)) (by linarith)
      _ = W * k ^ 4 / 4 := by ring
      _ ≤ Δ := by
        have : 0 ≤ W * k ^ 4 := by positivity
        linarith
  · rw [le_div_iff₀ (by positivity)]
    exact q2
  · apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ (by positivity)]
    have hCC : Ct * C ≤ k / 4000 := le_trans (mul_le_mul hCt2 hC2 (by linarith) (by positivity)) hQk
    calc LinearSubstitution ^ 2 * (Real.pi * Ct * C * 1 * X4) = (X4 * LinearSubstitution ^ 2) * (Real.pi * (Ct * C)) := by ring
      _ ≤ (X4 * LinearSubstitution ^ 2) * (4 * (k / 4000)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hpi4 hCC (by positivity) (by norm_num)) (by positivity)
      _ ≤ X4 * LinearSubstitution ^ 2 * k := by
        have : 0 ≤ X4 * LinearSubstitution ^ 2 := by positivity
        nlinarith
      _ ≤ TTs := hT

theorem szf_sizes {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (n4 n5 : ℕ) (hcT : 0 < cT) (hCl1 : (2 * n4 + 2 * n5 + 4 : ℝ) ≤ Cl) (hCl2 : (n4 + 2 * n5 + 1 : ℝ) ≤ Cl * cT)
    (u u' : D.what₂.Word) :
    ((D.R.k : ℝ) ^ n4) ^ 2 * ((D.R.k : ℝ) ^ n5) ^ 2 * (D.R.k : ℝ) ^ 4 ≤ (D.s.Del : ℝ) ∧
    (D.R.k : ℝ) ^ n4 * ((D.R.k : ℝ) ^ n5) ^ 2 * (D.R.k : ℝ) ≤ Real.sqrt (Tr D u * Tr D u') := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a16, -, -, -, a20, -, -, a23, -, a25⟩ := hH
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast five_le_k D
  have hk1 : (1 : ℝ) ≤ D.R.k := by linarith
  have hk0 : (0 : ℝ) ≤ D.R.k := by linarith
  have hT := Tr_pos D u
  have hL1 := one_le_L large₂
  have hf1 := one_le_f D
  have hb1 := one_lt_b large₂
  have hb0 : (0 : ℝ) ≤ large₂.sc.b := by linarith
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  constructor
  · have e1 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by
      have : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * D.R.f := le_mul_of_one_le_right hk0 hf1
      exact le_trans this (le_mul_of_one_le_right (by positivity) hL1)
    have e2 : (D.R.k : ℝ) ^ Cl ≤ ((D.R.k : ℝ) * D.R.f * large₂.sc.L) ^ Cl := Real.rpow_le_rpow hk0 e1 a25.le
    have e3 : (D.R.k : ℝ) ^ (((2 * n4 + 2 * n5 + 4 : ℕ) : ℝ)) ≤ (D.R.k : ℝ) ^ Cl :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by push_cast; exact hCl1)
    rw [Real.rpow_natCast] at e3
    calc ((D.R.k : ℝ) ^ n4) ^ 2 * ((D.R.k : ℝ) ^ n5) ^ 2 * (D.R.k : ℝ) ^ 4 = (D.R.k : ℝ) ^ (2 * n4 + 2 * n5 + 4) := by ring
      _ ≤ (D.s.Del : ℝ) := le_trans e3 (le_trans e2 a20)
  · have hne0 : Nonempty D.what₂.Tau := by
      rw [← Fintype.card_pos_iff, szf_card_Tau]
      exact_mod_cast (lt_of_lt_of_le one_pos hf1 : (0 : ℝ) < D.R.f)
    obtain ⟨τ0⟩ := hne0
    have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
    have hbk : (D.R.k : ℝ) ^ (Cl / 2) ≤ large₂.sc.b := by
      have e1 : (D.R.k : ℝ) ^ Cl ≤ large₂.sc.b ^ (2 : ℝ) :=
        le_trans (le_trans (le_max_left _ _) (a16 τ0 1 le_rfl hm1).1) (a16 τ0 1 le_rfl hm1).2
      have e2 := Real.rpow_le_rpow (by positivity) e1 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      rw [← Real.rpow_mul hk0, ← Real.rpow_mul hb0] at e2
      have e3 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
      rw [e3, Real.rpow_one, show Cl * (1 / 2) = Cl / 2 by ring] at e2
      exact e2
    have hbT : (D.R.k : ℝ) ^ n4 * ((D.R.k : ℝ) ^ n5) ^ 2 * (D.R.k : ℝ) ≤ large₂.sc.b ^ (cT * (D.R.m : ℝ)) := by
      have e1 : ((D.R.k : ℝ) ^ (Cl / 2)) ^ (cT * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (cT * (D.R.m : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hbk (by positivity)
      rw [← Real.rpow_mul hk0] at e1
      have e2 : (D.R.k : ℝ) ^ (((n4 + 2 * n5 + 1 : ℕ) : ℝ)) ≤ (D.R.k : ℝ) ^ (Cl / 2 * (cT * (D.R.m : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le hk1 ?_
        push_cast
        have hp : 0 ≤ Cl * cT := by positivity
        have h1 : Cl * cT * 1 ≤ Cl * cT * ((D.R.m : ℝ) / 2) := mul_le_mul_of_nonneg_left (by linarith) hp
        have h2 : Cl / 2 * (cT * (D.R.m : ℝ)) = Cl * cT * ((D.R.m : ℝ) / 2) := by ring
        rw [h2]
        linarith
      rw [Real.rpow_natCast] at e2
      calc (D.R.k : ℝ) ^ n4 * ((D.R.k : ℝ) ^ n5) ^ 2 * (D.R.k : ℝ) = (D.R.k : ℝ) ^ (n4 + 2 * n5 + 1) := by ring
        _ ≤ _ := le_trans e2 e1
    refine le_trans hbT (Real.le_sqrt_of_sq_le ?_)
    rw [sq]
    exact mul_le_mul (a23 u).1 (a23 u').1 (by positivity) hT.le

theorem szf_BB {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT C4 : ℝ}
    (hh : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT) (h2e : LocalBesselAndTopKernel.BesselBoundOneSlotDifference D C4)
    (u u' : D.what₂.Word) (l : ℕ) (hl1 : 1 ≤ l) (hl2 : l ≤ D.R.k - 2)
    (hne : ∀ τ, uOne D u τ (l + 1) ≠ uOne D u' τ (l + 1)) (x : D.what₂.Tau → LocalDataRealPlace D) (hx : IsLocC D u u' l x)
    (n4 : ℕ) (hn4 : C4 ≤ n4) (hI : 5 / 2 ≤ (D.s.Del : ℝ) / 2) (hN3' : 5 / 2 ≤ NA D ^ 3)
    (hN3 : NA D ^ 3 ≤ (D.s.Del : ℝ) / 2) :
    (∀ τ, 0 < gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a (x τ).b) ∧
      gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a (x τ).b) ≤
        1 * tV D u u' τ * Real.sqrt ((D.R.k ^ (2 * n4) : ℕ) : ℝ)) ∧
    (∀ τ, 0 < gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a1 (x τ).b1) ∧
      gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a1 (x τ).b1) ≤
        1 * tV D u u' τ * Real.sqrt ((D.R.k ^ (2 * n4) : ℕ) : ℝ) * Real.sqrt (NA D ^ 3 / D.s.Del)) := by
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast five_le_k D
  have hk1 : (1 : ℝ) ≤ D.R.k := by linarith
  have hDel0 : (0 : ℝ) < D.s.Del := by exact_mod_cast D.s.Del_pos
  have hX4 : (0 : ℝ) ≤ (D.R.k : ℝ) ^ n4 := by positivity
  have hcast : ((D.R.k ^ (2 * n4) : ℕ) : ℝ) = ((D.R.k : ℝ) ^ n4) ^ 2 := by push_cast; ring
  have hsq : Real.sqrt ((D.R.k ^ (2 * n4) : ℕ) : ℝ) = (D.R.k : ℝ) ^ n4 := by
    rw [hcast, Real.sqrt_sq hX4]
  have hkC4 : (D.R.k : ℝ) ^ C4 ≤ (D.R.k : ℝ) ^ n4 := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hk1 hn4
  have ht0 : ∀ τ, 0 ≤ tV D u u' τ := fun τ => Real.sqrt_nonneg _
  constructor
  · intro τ
    have h := szf_sup hh h2e u u' l hl1 hl2 τ (hne τ) (x τ) (hx.1 τ).1 (hx.1 τ).2.1 (hx.1 τ).2.2
      ((D.s.Del : ℝ) / 2) hI le_rfl
    rw [← (hx.2 τ).1, ← (hx.2 τ).2.1] at h
    refine ⟨h.1, le_trans h.2 ?_⟩
    rw [hsq, one_mul]
    have e1 : Real.sqrt ((D.s.Del : ℝ) / 2 / D.s.Del) ≤ 1 := by
      rw [Real.sqrt_le_one, div_le_one hDel0]; linarith
    calc tV D u u' τ * (D.R.k : ℝ) ^ C4 * Real.sqrt ((D.s.Del : ℝ) / 2 / D.s.Del)
        ≤ tV D u u' τ * (D.R.k : ℝ) ^ n4 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hkC4 (ht0 τ)) e1 (Real.sqrt_nonneg _) (mul_nonneg (ht0 τ) hX4)
      _ = _ := by ring
  · intro τ
    have h := szf_sup hh h2e u u' l hl1 hl2 τ (hne τ) (x τ) (hx.1 τ).1 (hx.1 τ).2.1 (hx.1 τ).2.2
      (NA D ^ 3) hN3' hN3
    rw [← (hx.2 τ).2.2.1, ← (hx.2 τ).2.2.2] at h
    refine ⟨h.1, le_trans h.2 ?_⟩
    rw [hsq, one_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkC4 (ht0 τ)) (Real.sqrt_nonneg _)

theorem szf_Vbound (D : D7) (hdd : SzfNormDD D) (hgn : SzfNormG D) (u u' : D.what₂.Word) (CA Ct I : ℝ) (K : ℕ)
    (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (hL : IsLatGLOB D L) (hI : 0 < I)
    (hba : ∀ v, (x v).b - (x v).a = I) (hCA : 1 ≤ CA) (hCt : 0 < Ct) (hka : 0 < D.host.ka)
    (hkapi : D.host.ka ≤ Real.pi) (hg1 : 1 ≤ gg D) (hN0 : 0 < NA D) (hCpi : CA * Real.pi * NA D / I ≤ 1)
    (hprod : ∏ τ, tV D u u' τ ≤ Ct)
    (hB : ∀ τ, 0 < gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a (x τ).b) ∧
      gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a (x τ).b) ≤
        1 * tV D u u' τ * Real.sqrt (K : ℝ))
    (hB1 : ∀ τ, 0 < gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a1 (x τ).b1) ∧
      gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a1 (x τ).b1) ≤
        1 * tV D u u' τ * Real.sqrt (K : ℝ) * Real.sqrt (NA D ^ 3 / D.s.Del)) :
    0 < ThInvF D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L ∧
    (ThInvF D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L ≤
        Ct * (CA * 1) ^ D.R.f * (Real.sqrt ((K : ℝ) * NA D ^ 3 / (D.s.Del : ℝ))) ^ D.R.f ∨
      ThInvF D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L ≤
        Ct * (CA * 1 * Real.sqrt (K : ℝ)) ^ D.R.f * (CA * Real.pi * NA D / I) ^ (2 * D.R.f) ∨
      ThInvF D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L ≤
        Ct * (CA * 1 * Real.sqrt (K : ℝ)) ^ D.R.f * (CA * Real.pi * NA D / I) ^ D.R.f ∨
      ThInvF D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L ≤
        Real.sqrt Ct * (Real.sqrt (Real.pi * CA * 1 * Real.sqrt (K : ℝ) / Real.sqrt (Tr D u * Tr D u'))) ^ D.R.f) := by
  have hTT : 0 < Tr D u * Tr D u' := mul_pos (Tr_pos D u) (Tr_pos D u')
  have hDel0 : (0 : ℝ) < D.s.Del := by exact_mod_cast D.s.Del_pos
  have ht0 : ∀ τ, 0 ≤ tV D u u' τ := fun τ => Real.sqrt_nonneg _
  have TP := fun (i s : ℕ) (hi : 1 ≤ i) => Formalism.FourierDecayAlt.P.threshold_products D.what₂.Tau (tV D u u')
    (fun τ => gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a1 (x τ).b1))
    (fun τ => gg D ^ D.R.m * supBe D D.host.ka (Tr D u) (Tr D u') (x τ) (Set.Icc (x τ).a (x τ).b))
    K CA 1 Ct D.host.ka (NA D) I (gg D) (D.s.Del : ℝ) (Tr D u * Tr D u') i s
    hCA one_pos hCt hka hkapi hN0 hI hg1 hDel0 hTT hCpi ht0 hprod
    (fun τ => ⟨(hB1 τ).1.le, (hB1 τ).2⟩) (fun τ => ⟨(hB τ).1.le, (hB τ).2⟩) hi
  simp only [szf_card_Tau] at TP
  generalize hM1 : Ct * (CA * 1) ^ D.R.f * (Real.sqrt ((K : ℝ) * NA D ^ 3 / (D.s.Del : ℝ))) ^ D.R.f = M1 at TP ⊢
  generalize hM2 : Ct * (CA * 1 * Real.sqrt (K : ℝ)) ^ D.R.f * (CA * Real.pi * NA D / I) ^ (2 * D.R.f) = M2 at TP ⊢
  generalize hM3 : Ct * (CA * 1 * Real.sqrt (K : ℝ)) ^ D.R.f * (CA * Real.pi * NA D / I) ^ D.R.f = M3 at TP ⊢
  generalize hM4 : Real.sqrt Ct *
    (Real.sqrt (Real.pi * CA * 1 * Real.sqrt (K : ℝ) / Real.sqrt (Tr D u * Tr D u'))) ^ D.R.f = M4 at TP ⊢
  have hE1 := product_formula_first D hdd hgn hka CA (NA D) (Tr D u) (Tr D u') I hI x L hL hba
  have hE2 := product_formula_second D hdd hgn hka CA (NA D) (Tr D u) (Tr D u') I hI x L hL hba
  have hE3 := product_formula_third D hdd hgn hka CA (NA D) (Tr D u) (Tr D u') I hI hTT x L hL hba
  have hy1 := hE1 1 le_rfl (by omega)
  simp only [↓reduceIte] at hy1
  unfold ThInvF
  generalize hS : ({y | ∃ i, 1 ≤ i ∧ i ≤ D.R.rS + 1 ∧
          y = (∏ v, xSz D CA CA (NA D) (kaV D (gE D) v) (Tr D u) (Tr D u') (x v) i) / nrmHalf D (L.aaV i 1)} ∪
        {y | ∃ i s, 1 ≤ i ∧ 2 ≤ s ∧ i - 1 + s ≤ D.R.rS + 1 ∧
          y = (∏ v, LamSz D CA CA (NA D) (kaV D (gE D) v) (Tr D u) (Tr D u') (x v) i s) /
            min (nrmHalf D (L.aaV i s)) (nrmHalf D (L.aaP i (s - 1)))} ∪
        {y | ∃ i, 1 ≤ i ∧ i ≤ D.R.rS ∧
          y = (∏ v, LamPSz D CA CA (NA D) (kaV D (gE D) v) (Tr D u) (Tr D u') (x v) i) /
            nrmHalf D (L.aaP i (D.R.rS + 2 - i))} : Set ℝ) = S
  have hall : ∀ y ∈ S, y ≤ max (max M1 M2) (max M3 M4) := by
    rw [← hS]
    rintro y ((⟨i, hi1, hi2, rfl⟩ | ⟨i, s, hi1, hs2, his, rfl⟩) | ⟨i, hi1, hi2, rfl⟩)
    · by_cases h1 : i = 1
      · subst h1
        rw [hy1]
        exact le_trans (TP 1 2 le_rfl).1 (le_trans (le_max_left _ _) (le_max_left _ _))
      · have e := hE1 i hi1 hi2
        simp only [if_neg h1] at e
        rw [e]
        exact le_trans ((TP i 2 hi1).2.1 (by omega)) (le_trans (le_max_right _ _) (le_max_left _ _))
    · rw [hE2 i s hi1 hs2 his]
      exact le_trans ((TP i s hi1).2.2.1 hs2) (le_trans (le_max_left _ _) (le_max_right _ _))
    · rw [hE3 i hi1 hi2]
      exact le_trans (TP i 2 hi1).2.2.2 (le_trans (le_max_right _ _) (le_max_right _ _))
  have hmem : (∏ v, xSz D CA CA (NA D) (kaV D (gE D) v) (Tr D u) (Tr D u') (x v) 1) / nrmHalf D (L.aaV 1 1) ∈ S := by
    rw [← hS]
    exact Or.inl (Or.inl ⟨1, le_rfl, by omega, rfl⟩)
  constructor
  · refine lt_of_lt_of_le ?_ (le_csSup ⟨_, hall⟩ hmem)
    rw [hy1]
    refine Finset.prod_pos (fun v _ => ?_)
    simp only [Sz.xHat, show 2 * 1 - 2 = 0 from rfl, pow_zero, mul_one]
    exact mul_pos (lt_of_lt_of_le one_pos hCA) (hB1 v).1
  · have hVle : sSup S ≤ max (max M1 M2) (max M3 M4) := csSup_le ⟨_, hmem⟩ hall
    rcases le_max_iff.1 hVle with h | h
    · rcases le_max_iff.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases le_max_iff.1 h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))

theorem separation_bound_of_norms (CA c5 C4 C0 cT : ℝ) (hCA : 1 ≤ CA) (hcT : 0 < cT) :
    ∃ K0 Cl0 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu CT : ℝ), SzfNormDD D → SzfNormG D →
      K0 ≤ D.R.k → Cl0 ≤ Cl → LocalBesselAndTopKernel.MassRatioTheoremTwo D large₂ C0 C' Cl Cg cb Cu cT CT C4 c5 CA := by
  obtain ⟨n4, hn4⟩ : ∃ n4 : ℕ, C4 ≤ n4 := ⟨⌈C4⌉₊, Nat.le_ceil C4⟩
  obtain ⟨n5, hn5, hn51⟩ : ∃ n5 : ℕ, c5 ≤ n5 ∧ 1 ≤ n5 :=
    ⟨⌈c5⌉₊ + 1, by push_cast; linarith [Nat.le_ceil c5], by omega⟩
  have hn5R : (1 : ℝ) ≤ n5 := by exact_mod_cast hn51
  obtain ⟨k0, hk0⟩ := Formalism.FourierDecayAlt.P.final_smallness CA (n5 : ℝ) hCA (by linarith)
  refine ⟨max k0 (4000 * (C0 * Real.exp 9) ^ 2 * CA ^ 2),
    max (max (2 * n4 + 2 * n5 + 4) ((n4 + 2 * n5 + 1) / cT)) 16, ?_⟩
  intro D large₂ C' Cl Cg cb Cu CT hdd hgn hK hCl hh h2a h2e u u' l hl1 hl2 hne x L hx hL
  have hKa : k0 ≤ D.R.k := by exact_mod_cast le_trans (le_max_left _ _) hK
  have hKb := le_trans (le_max_right _ _) hK
  have hCl1 : (2 * n4 + 2 * n5 + 4 : ℝ) ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl
  have hCl2 : (n4 + 2 * n5 + 1 : ℝ) ≤ Cl * cT := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl
    rwa [div_le_iff₀ hcT] at this
  have hCl3 : (16 : ℝ) ≤ Cl := le_trans (le_max_right _ _) hCl
  obtain ⟨-, hv, hg25⟩ := sze_facts hh
  have F := tfFacts_of (⟨hh.2.1, hh.1, hh.2.2⟩ : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
  have a6 : Cl * large₂.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k := hh.2.1.2.2.2.2.2.1
  have hC0 := hh.2.2
  obtain ⟨hka, hkapi⟩ := tf_ka D hv
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast five_le_k D
  have hk1 : (1 : ℝ) ≤ D.R.k := by linarith
  have hCt : 1 ≤ C0 * Real.exp 9 := one_le_mul_of_one_le_of_one_le hC0 (Real.one_le_exp (by norm_num))
  have hTT : 0 < Tr D u * Tr D u' := mul_pos (Tr_pos D u) (Tr_pos D u')
  have hDel0 : (0 : ℝ) < D.s.Del := by exact_mod_cast D.s.Del_pos
  have hf1 := one_le_f D
  have hb1 := one_lt_b large₂
  have hmR : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast m_eq D
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hX4 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ n4 := one_le_pow₀ hk1
  have hX5 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ n5 := one_le_pow₀ hk1
  obtain ⟨hΔ, hsT⟩ := szf_sizes hh.2.1 n4 n5 hcT hCl1 hCl2 u u'
  have hNeq : NA D = 10 * (D.R.m : ℝ) := by unfold NA; rw [hmR]; ring
  have hN0 : 0 < NA D := by rw [hNeq]; linarith
  have hN20 : 20 ≤ NA D := by rw [hNeq]; linarith
  have hN : NA D ≤ 10 * (D.R.k : ℝ) := by rw [hNeq]; linarith [m_le_k D]
  obtain ⟨hI, hN3, hCpi, q1, q2, q3⟩ := szf_num (D.R.k : ℝ) (D.s.Del : ℝ) (Real.sqrt (Tr D u * Tr D u'))
    (C0 * Real.exp 9) CA (NA D) ((D.R.k : ℝ) ^ n4) ((D.R.k : ℝ) ^ n5) hk1 hCA hCt hN0 hN hX4 hX5 hKb hΔ hsT
  have hcast : ((D.R.k ^ (2 * n4) : ℕ) : ℝ) = ((D.R.k : ℝ) ^ n4) ^ 2 := by push_cast; ring
  have hsq : Real.sqrt ((D.R.k ^ (2 * n4) : ℕ) : ℝ) = (D.R.k : ℝ) ^ n4 := by
    rw [hcast, Real.sqrt_sq (by linarith)]
  have hba : ∀ v, (x v).b - (x v).a = (D.s.Del : ℝ) / 2 - 5 / 2 := by
    intro v
    rw [(hx.2 v).1, (hx.2 v).2.1]; ring
  have hN3' : 5 / 2 ≤ NA D ^ 3 := by
    have : NA D ≤ NA D ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  obtain ⟨hB, hB1⟩ := szf_BB hh h2e u u' l hl1 hl2 hne x hx n4 hn4 (by linarith) hN3' hN3
  obtain ⟨hV0, hor⟩ := szf_Vbound D hdd hgn u u' CA (C0 * Real.exp 9) ((D.s.Del : ℝ) / 2 - 5 / 2) (D.R.k ^ (2 * n4))
    x L hL hI hba hCA (by linarith) hka hkapi (by linarith) hN0 hCpi (product_local_ratios_le F h2a u u') hB hB1
  have hThdef : ThA D CA u u' x L =
      ThInvF D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L ^ (-(1 / (D.R.f : ℝ))) := rfl
  rw [hThdef]
  generalize ThInvF D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L = V at hV0 hor ⊢
  have hTh0 : 0 < V ^ (-(1 / (D.R.f : ℝ))) := Real.rpow_pos_of_pos hV0 _
  have hThf : ((V ^ (-(1 / (D.R.f : ℝ)))) ^ D.R.f)⁻¹ = V := by
    have hf0 : (D.R.f : ℝ) ≠ 0 := by linarith
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV0.le,
      show -(1 / (D.R.f : ℝ)) * (D.R.f : ℝ) = -1 by field_simp, Real.rpow_neg_one, inv_inv]
  generalize V ^ (-(1 / (D.R.f : ℝ))) = Th at hTh0 hThf ⊢
  rw [← hThf] at hor
  have hf1' : 1 ≤ D.R.f := by exact_mod_cast hf1
  have TL := Formalism.FourierDecayAlt.P.theta_lower_bound D.R.f (D.R.k ^ (2 * n4)) CA 1 (C0 * Real.exp 9) (NA D)
    ((D.s.Del : ℝ) / 2 - 5 / 2) (D.s.Del : ℝ)
    (Tr D u * Tr D u') Th hf1' (Nat.one_le_pow _ _ (by have := five_le_k D; omega)) hCA one_pos hCt hN0 hI hDel0 hTT
    hTh0 hCpi hor
  rw [hsq, hcast] at TL
  have hkTh : (D.R.k : ℝ) ^ n5 ≤ Th := le_trans (le_min (le_min q1 q2) q3) TL
  refine ⟨le_trans ?_ hkTh, ?_⟩
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hk1 hn5
  · have hmf : 2 * D.R.rS + 2 ≤ D.R.f := by
      rw [← m_eq D]
      have := D.R.m_le_f
      simpa [Ranks.f, Ranks.n] using this
    have h16 : (16 : ℝ) ≤ (n5 : ℝ) * Cl := by
      have : (1 : ℝ) * Cl ≤ (n5 : ℝ) * Cl := mul_le_mul_of_nonneg_right hn5R (by linarith)
      linarith
    have FS := (hk0 D.R.k D.R.rS D.R.f large₂.sc.b Cl Th hKa hmf hb1.le h16
      (by rw [log_b]; exact a6) (by rw [Real.rpow_natCast]; exact hkTh)).2
    rw [Real.rpow_natCast, Real.rpow_neg (by linarith), show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    refine le_trans ?_ FS
    have hp : 0 ≤ ((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f := by positivity
    calc ((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f = 1 * (((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f) := by ring
      _ ≤ CA * (((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f) := mul_le_mul_of_nonneg_right hCA hp
      _ = _ := by ring

theorem family_separation_bound_of_norms (CA c5 C4 C0 cT : ℝ) (hCA : 1 ≤ CA) (hcT : 0 < cT) :
    ∃ Cl0 : ℝ, ∀ {eps : ℝ} (Fm : FamP eps) (Cg cb Cu CT : ℝ), Cl0 ≤ sCl Fm →
      (∀ x (i : Fm.Ix x), SzfNormDD (Fm.D x i) ∧ SzfNormG (Fm.D x i)) →
      LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT → LocalBesselAndTopKernel.SchurOrthogonalityRealPlace Fm C0 Cg cb Cu cT CT C4 →
      LocalBesselAndTopKernel.FamilyLocalBesselBoundWithCharacter Fm C0 Cg cb Cu cT CT c5 CA := by
  obtain ⟨K0, Cl0, H⟩ := separation_bound_of_norms CA c5 C4 C0 cT hCA hcT
  refine ⟨Cl0, ?_⟩
  intro eps Fm Cg cb Cu CT hCl hn h2a h2e
  obtain ⟨x1, H1⟩ := h2a
  obtain ⟨x2, H2⟩ := h2e
  obtain ⟨x3, -, H3⟩ := ev_k Fm K0
  refine ⟨max x1 (max x2 x3), fun x hx i hh => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  exact H _ _ _ _ _ _ _ _ (hn x i).1 (hn x i).2 (H3 x hx3 i) hCl hh (H1 x hx1 i hh) (H2 x hx2 i hh)

end Formalism.MainNotions.BridgeLemma

end
