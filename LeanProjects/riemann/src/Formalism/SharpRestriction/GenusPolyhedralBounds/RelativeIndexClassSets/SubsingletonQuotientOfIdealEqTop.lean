import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Inh

section Lem

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem hypC_large {large₂ : SizeData₂ D} {X : PJ D B P j} {H : KHyp} {C2 A2 CR CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (h : HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus) :
    large₂.sc.x ≤ (D.R.f : ℝ) * D.R.r ∧ (1000 : ℝ) ^ 20 ≤ (D.R.f : ℝ) * D.R.r * large₂.sc.x ^ large₂.sc.eps := by
  obtain ⟨hpa, hsc, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdom⟩ := hsc
  obtain ⟨h1, h2, -⟩ := hdom
  refine ⟨hpa.1, ?_⟩
  have h3 : (1000 : ℝ) ^ 20 ≤ H.C1 ^ 20 := pow_le_pow_left₀ (by norm_num) h1 20
  have h4 : Zb D large₂ = (D.R.f : ℝ) * D.R.r * large₂.sc.x ^ large₂.sc.eps := rfl
  linarith

theorem not_hypC_of_le {large₂ : SizeData₂ D} {X : PJ D B P j} {H : KHyp} {C2 A2 CR CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hfr : (D.R.f : ℝ) * D.R.r ≤ 72) : ¬ HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus := by
  intro h
  obtain ⟨hx, hZ⟩ := hypC_large h
  have hx1 : 1 ≤ large₂.sc.x := large₂.sc.one_lt_alt.le
  have he : large₂.sc.eps ≤ 1 := by linarith [large₂.sc.eps_lt]
  have hxe : large₂.sc.x ^ large₂.sc.eps ≤ large₂.sc.x := by
    calc large₂.sc.x ^ large₂.sc.eps ≤ large₂.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 he
      _ = large₂.sc.x := Real.rpow_one _
  have hfr0 : 0 ≤ (D.R.f : ℝ) * D.R.r := by positivity
  have : (D.R.f : ℝ) * D.R.r * large₂.sc.x ^ large₂.sc.eps ≤ 72 * 72 := by
    calc (D.R.f : ℝ) * D.R.r * large₂.sc.x ^ large₂.sc.eps ≤ 72 * large₂.sc.x :=
          mul_le_mul hfr hxe (by positivity) (by norm_num)
      _ ≤ 72 * 72 := by linarith
  norm_num at hZ
  linarith

theorem not_hypC_Rt (s : ℕ) (hR : D.R = Formalism.MainNotions.Inhab.Rt s) {large₂ : SizeData₂ D} {X : PJ D B P j} {H : KHyp}
    {C2 A2 CR CT : ℝ} {S : Scal B} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} : ¬ HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus := by
  apply not_hypC_of_le
  have h1 : D.R.f = 8 := by rw [hR]; rfl
  have h2 : D.R.r = 9 := by rw [hR]; rfl
  rw [h1, h2]; norm_num

theorem shares_force (d rq rz del R Dm T : ℕ) (hcount : d ≤ rq + R * del + rz)
    (hrz : (rz : ℝ) ≤ 22 * (Dm : ℝ) ^ 2 * d / T) (hrq : (rq : ℝ) ≤ 22 * (Dm : ℝ) ^ 2 * d / T)
    (hT : 44 * Dm ^ 2 < T) :
    (1 ≤ d → 1 ≤ del) ∧ (1 - 44 * (Dm : ℝ) ^ 2 / T) * d ≤ R * del := by
  have hT' : (44 * (Dm : ℝ) ^ 2) < T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := lt_of_le_of_lt (by positivity) hT'
  have hc : ((rq + R * del + rz : ℕ) : ℝ) = rq + R * del + rz := by push_cast; ring
  have hcount' : (d : ℝ) ≤ rq + R * del + rz := by rw [← hc]; exact_mod_cast hcount
  have hsum : (rq : ℝ) + rz ≤ 44 * (Dm : ℝ) ^ 2 / T * d := by
    have : 22 * (Dm : ℝ) ^ 2 * d / T + 22 * (Dm : ℝ) ^ 2 * d / T = 44 * (Dm : ℝ) ^ 2 / T * d := by ring
    linarith
  refine ⟨fun hd => ?_, ?_⟩
  · by_contra hdel
    have h0 : del = 0 := by omega
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hlt : 44 * (Dm : ℝ) ^ 2 / T < 1 := by rw [div_lt_one hT0]; exact hT'
    have : 44 * (Dm : ℝ) ^ 2 / T * d < d := by nlinarith
    rw [h0] at hcount'
    simp at hcount'
    linarith
  · have : (1 - 44 * (Dm : ℝ) ^ 2 / T) * d = d - 44 * (Dm : ℝ) ^ 2 / T * d := by ring
    rw [this]
    linarith

theorem rk_le_rq_add {large₂ : SizeData₂ D} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) {S : Scal B}
    {CRm : ℝ} {T : ℕ} {c Ch Ah : ℝ} (hLat : LatAt B j ka) (hQ : G.TiedQ large₂ S CRm T c Ch Ah) :
    X.rk ka (B.Mlat j ka) ≤ G.rq + finrank B.KO (WeightFamilies.MggK B CRm T c j ka) := by
  have hsp : Submodule.span B.KO ((B.Mlat j ka : Set (B.Cusp j ka))) = ⊤ := hLat.span_eq_top
  have hrk : X.rk ka (B.Mlat j ka) = finrank B.KO (B.Cusp j ka) := by
    unfold PJ.rk; rw [hsp, finrank_top]
  have hsup := hQ.2.2.1
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka))) (WeightFamilies.MggK B CRm T c j ka)
  rw [hsup, finrank_top] at h1
  have h2 : finrank B.KO (Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka))) ≤ G.rq := by
    have := finrank_range_le_card (R := B.KO) (b := fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka))
    simpa [Set.finrank] using this
  rw [hrk]
  omega

end Lem

section Loc

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

section One

variable (X) (la : HeightOneSpectrum (𝓞 B.KO))

theorem Tv_ne_zero {N : ℕ} (p : Idx D j N) : algebraMap (Op X la N) (Kp X la N) (Tv X la N p) ≠ 0 := by
  have hinjK : Function.Injective (algebraMap (Op X la N) (Kp X la N)) := IsFractionRing.injective _ _
  have hinjP : Function.Injective (algebraMap (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  intro h
  rw [← map_zero (algebraMap (Op X la N) (Kp X la N))] at h
  have h1 := hinjK h
  unfold Tv at h1
  rw [← map_zero (algebraMap (Pol X la N) (Op X la N))] at h1
  exact MvPolynomial.X_ne_zero p (hinjP h1)

theorem jid_top_one (w : Fin 1 → B.Cusp j wL) (hD : 0 < WeightFamilies.dimY D j) : Jid X la w = ⊤ := by
  set c : Fin (WeightFamilies.dimY D j + 1) → Kp X la 1 := fun i => algebraMap (Op X la 1) (Kp X la 1) (Tv X la 1 (i, 0)) with hc
  have hsec : ∀ i, sec X la w i = c i • emb X la 1 (X.inc wL (w 0)) := fun i => by
    simp only [sec, Fin.sum_univ_one, hc]
  have hc0 : c 0 ≠ 0 := Tv_ne_zero X la _
  let i0 : Fin (WeightFamilies.dimY D j) := ⟨0, hD⟩
  have hci : c i0.succ ≠ 0 := Tv_ne_zero X la _
  have hs : sec X la w i0.succ = (c i0.succ / c 0) • sec X la w 0 := by
    rw [hsec, hsec, smul_smul, div_mul_cancel₀ _ hc0]
  have hfr : (sfr X la w i0.succ : Lw X la w) = algebraMap (Kp X la 1) (Lw X la w) (c i0.succ / c 0) := by
    rw [coe_sfr, hs, map_smul, frac_apply, pow_one, section_mul_inverse_eq_one, Algebra.algebraMap_eq_smul_one]
  have hu : IsUnit (sfr X la w i0.succ) := by
    have : sfr X la w i0.succ = algebraMap (Kp X la 1) ↥(Frac0 X la w) (c i0.succ / c 0) := Subtype.ext hfr
    rw [this]
    exact (IsUnit.mk0 _ (div_ne_zero hci hc0)).map _
  exact Ideal.eq_top_of_isUnit_mem _ (sfr_succ_mem_Jid X la w i0) hu

end One

section Sub

variable {la : HeightOneSpectrum (𝓞 B.KO)} {N : ℕ} {w : Fin N → B.Cusp j wL}

theorem osK_sub (h : Jid X la w = ⊤) : Subsingleton (OsK X la w) :=
  Ideal.Quotient.subsingleton_iff.2 h

theorem quot_top_sub {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] : Subsingleton (M ⧸ (⊤ : Submodule R M)) :=
  ⟨fun a b => by
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      induction b using Submodule.Quotient.induction_on with
      | H y => exact (Submodule.Quotient.eq _).2 Submodule.mem_top⟩

theorem subsingleton_quotient_of_ideal_eq_top (h : Jid X la w = ⊤) (u : WeightFamilies.Wt D j) : Subsingleton (SectionSheafQuotient X la w u) := by
  unfold SectionSheafQuotient
  rw [h, Submodule.top_smul]
  exact quot_top_sub

theorem wK_sub (h : Jid X la w = ⊤) (u : WeightFamilies.Wt D j) (a : ℕ) : Subsingleton (WK X la w u a) := by
  unfold WK
  rw [h, Ideal.top_pow, Submodule.top_smul]
  exact quot_top_sub

theorem pts_empty (G : GlobalFamilyData X ka wL wF) (h : Jid X la G.w = ⊤) : IsEmpty (PtsG G la) := by
  have := osK_sub h
  refine ⟨fun ζ => ?_⟩
  have h1 : ζ.asIdeal = ⊤ := (Ideal.eq_top_iff_one _).2 (by
    rw [Subsingleton.elim (1 : ↥(As (Op X la G.N) (OsK X la G.w))) 0]; exact zero_mem _)
  exact ζ.isMaximal.ne_top h1

end Sub

section Named

variable {la : HeightOneSpectrum (𝓞 B.KO)} (G : GlobalFamilyData X ka wL wF)

theorem inBasis_of (h : Jid X la G.w = ⊤) (hdel : G.del = 0) : InBasis G la := by
  have : IsEmpty (Fin G.del) := by rw [hdel]; infer_instance
  have := subsingleton_quotient_of_ideal_eq_top h wF
  refine ⟨linearIndependent_empty_type, ?_⟩
  refine Submodule.eq_top_iff'.2 fun x => ?_
  rw [Subsingleton.elim x 0]; exact zero_mem _

variable {G}

theorem inCurve_of (Q : LocalPointData G la) (h : Jid X la G.w = ⊤) : Q.InCurve := by
  have := osK_sub h
  have := subsingleton_quotient_of_ideal_eq_top h wF
  refine ⟨?_, ⟨fun x _ => Subsingleton.elim x 0⟩, ?_⟩
  · refine ⟨?_⟩
    rw [show (⊤ : Submodule (Kp X la G.N) (OsK X la G.w)) = ⊥ from Subsingleton.elim _ _]
    exact Submodule.fg_bot
  · exact ⟨fun a b _ => Subsingleton.elim a b, fun v => ⟨0, Subsingleton.elim _ _⟩⟩

theorem inTie_of (Q : LocalPointData G la) (h : Jid X la G.w = ⊤) (S : Scal B) : Q.InTie S := by
  have := pts_empty G h
  intro ζ; exact isEmptyElim ζ

theorem inLift_of (Q : LocalPointData G la) (h : Jid X la G.w = ⊤) (T : ℕ) : Q.InLift T := by
  have := subsingleton_quotient_of_ideal_eq_top h wF
  intro a _
  exact ⟨0, Subsingleton.elim _ _, by rw [map_zero]; exact zero_mem _⟩

theorem ila_of (Q : LocalPointData G la) (h : Jid X la G.w = ⊤) : Q.Ila = 0 := by
  have := subsingleton_quotient_of_ideal_eq_top h wF
  unfold LocalPointData.Ila
  exact Module.length_eq_zero

theorem net_of (Q : LocalPointData G la) (h : Jid X la G.w = ⊤) : Q.Net = 0 := by
  have := pts_empty G h
  unfold LocalPointData.Net
  exact finsum_of_isEmpty _

end Named

theorem heights_of (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (h : ∀ la, Jid X la G.w = ⊤) (hdel : G.del = 0)
    (Gc PH Prw Pet : ℝ) : Heights Qf Gc PH Prw Pet := by
  have : IsEmpty (Fin G.del) := by rw [hdel]; infer_instance
  have hI : ∀ la, (Qf la).Ila = 0 := fun la => ila_of (Qf la) (h la)
  have hN : ∀ la, (Qf la).Net = 0 := fun la => net_of (Qf la) (h la)
  have hd : (G.del : ℝ) = 0 := by exact_mod_cast hdel
  refine ⟨fun la => by rw [hI la]; exact ENat.zero_ne_top, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩
  · simp only [hI, ENat.toNat_zero, Nat.cast_zero, zero_mul]; exact summable_zero
  · simp only [hI, ENat.toNat_zero, Nat.cast_zero, zero_mul, tsum_zero, mul_zero, hd, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero, le_refl]
  · simp only [hN, zero_mul]; exact summable_zero
  · simp only [hN, zero_mul, tsum_zero, zero_div, hd, mul_zero, zero_mul, add_zero, le_refl]

theorem inContainZ_of (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (T : ℕ)
    (h0 : Subsingleton (B.Cusp j (X.wF0 wL wF))) : InContainZ G la S T := by
  refine Submodule.span_le.2 ?_
  rintro v ⟨al, θ, -, -, rfl⟩
  rw [Subsingleton.elim θ 0, map_zero, map_zero, mul_zero]
  exact zero_mem _

theorem inContainM_of (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (CRm : ℝ) (T : ℕ) (c : ℝ)
    (hk : Subsingleton (B.Cusp j ka)) : InContainM G la CRm T c := by
  refine Submodule.span_le.2 ?_
  rintro v ⟨F, -, rfl⟩
  show emb X la G.N (X.inc ka F) ∈ _
  rw [Subsingleton.elim F 0, map_zero, map_zero]
  exact zero_mem _

end Loc

section Mod

section Wt

variable {D : D7} {j : ℕ}

theorem wt_ext {w w' : WeightFamilies.Wt D j} (hP : w.aP = w'.aP) (hM : w.aM = w'.aM) (hn : w.n = w'.n) : w = w' := by
  cases w; cases w'; simp only at hP hM hn; subst hP hM hn; rfl

instance wtAdd (D : D7) (j : ℕ) : Add (WeightFamilies.Wt D j) := ⟨wadd⟩

instance wtZero (D : D7) (j : ℕ) : Zero (WeightFamilies.Wt D j) := ⟨wt0 D j⟩

instance wtACM (D : D7) (j : ℕ) : AddCommMonoid (WeightFamilies.Wt D j) where
  add_assoc a b c := wt_ext (by funext τ i; exact Nat.add_assoc _ _ _) (by funext τ i; exact Nat.add_assoc _ _ _)
    (Nat.add_assoc _ _ _)
  zero_add a := wt_ext (by funext τ i; exact Nat.zero_add _) (by funext τ i; exact Nat.zero_add _) (Nat.zero_add _)
  add_zero a := wt_ext (by funext τ i; exact Nat.add_zero _) (by funext τ i; exact Nat.add_zero _) (Nat.add_zero _)
  add_comm a b := wt_ext (by funext τ i; exact Nat.add_comm _ _) (by funext τ i; exact Nat.add_comm _ _) (Nat.add_comm _ _)
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

theorem wt_add_def (w w' : WeightFamilies.Wt D j) : w + w' = wadd w w' := rfl

end Wt

section Val

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_mulS (la : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd la (x * y) = vAdd la x + vAdd la y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  ring

theorem vAdd_oneS (la : HeightOneSpectrum (𝓞 K)) : vAdd la (1 : K) = 0 := by
  unfold vAdd; simp

theorem vAdd_nonneg_iffS (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    0 ≤ vAdd la x ↔ la.valuation K x ≤ 1 := by
  unfold vAdd
  by_cases h0 : la.valuation K x = 0
  · rw [h0]; simp
  · rw [neg_nonneg, ← WithZero.log_le_log h0 one_ne_zero]; simp

theorem vAdd_addS (la : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vAdd la x) (vAdd la y) ≤ vAdd la (x + y) := by
  unfold vAdd
  have h := Valuation.map_add (la.valuation K) x y
  have hx' : la.valuation K x ≠ 0 := (map_ne_zero _).2 hx
  have hy' : la.valuation K y ≠ 0 := (map_ne_zero _).2 hy
  have hxy' : la.valuation K (x + y) ≠ 0 := (map_ne_zero _).2 hxy
  rcases le_total (la.valuation K x) (la.valuation K y) with hle | hle
  · rw [max_eq_right hle] at h
    have := (WithZero.log_le_log hxy' hy').2 h
    exact min_le_of_right_le (by linarith)
  · rw [max_eq_left hle] at h
    have := (WithZero.log_le_log hxy' hx').2 h
    exact min_le_of_left_le (by linarith)

def vE (la : HeightOneSpectrum (𝓞 K)) (x : K) : EReal :=
  open Classical in if x = 0 then ⊤ else (((vAdd la x : ℤ) : ℝ) : EReal)

theorem vE_zero (la : HeightOneSpectrum (𝓞 K)) : vE la (0 : K) = ⊤ := by simp [vE]

theorem vE_of_ne (la : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    vE la x = (((vAdd la x : ℤ) : ℝ) : EReal) := by simp [vE, hx]

theorem vE_ne_bot (la : HeightOneSpectrum (𝓞 K)) (x : K) : vE la x ≠ ⊥ := by
  unfold vE; split_ifs
  · exact top_ne_bot
  · exact EReal.coe_ne_bot _

theorem vE_one (la : HeightOneSpectrum (𝓞 K)) : vE la (1 : K) = 0 := by
  rw [vE_of_ne la one_ne_zero, vAdd_oneS]; simp

theorem vE_mul (la : HeightOneSpectrum (𝓞 K)) (x y : K) : vE la (x * y) = vE la x + vE la y := by
  by_cases hx : x = 0
  · subst hx; rw [zero_mul, vE_zero, EReal.top_add_of_ne_bot (vE_ne_bot la y)]
  by_cases hy : y = 0
  · subst hy; rw [mul_zero, vE_zero, EReal.add_top_of_ne_bot (vE_ne_bot la x)]
  rw [vE_of_ne la (mul_ne_zero hx hy), vE_of_ne la hx, vE_of_ne la hy, vAdd_mulS la hx hy]
  push_cast; rfl

theorem vE_add (la : HeightOneSpectrum (𝓞 K)) (x y : K) : min (vE la x) (vE la y) ≤ vE la (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, vE_zero]; exact le_top
  by_cases hx : x = 0
  · subst hx; rw [zero_add]; exact min_le_right _ _
  by_cases hy : y = 0
  · subst hy; rw [add_zero]; exact min_le_left _ _
  rw [vE_of_ne la hx, vE_of_ne la hy, vE_of_ne la hxy]
  rcases min_le_iff.1 (vAdd_addS la hx hy hxy) with h | h
  · exact min_le_of_left_le (by exact_mod_cast h)
  · exact min_le_of_right_le (by exact_mod_cast h)

theorem vE_nonneg_iff (la : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    0 ≤ vE la x ↔ la.valuation K x ≤ 1 := by
  rw [vE_of_ne la hx, ← vAdd_nonneg_iffS]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

end Val

section Model

variable (D : D7) (K : Type) [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O)
  (Sg : ∀ j, WeightFamilies.Wt D j → Prop)

def cuspS (p : Prop) : Submodule K K := open Classical in if p then ⊤ else ⊥

def mlatS (p : Prop) : Submodule (𝓞 K) ↥(cuspS K p) :=
  (LinearMap.range (Algebra.linearMap (𝓞 K) K)).comap ((cuspS K p).subtype.restrictScalars (𝓞 K))

theorem mem_mlatS {p : Prop} (F : ↥(cuspS K p)) : F ∈ mlatS K p ↔ ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (F : K) := by
  simp [mlatS]

abbrev provS : WeightFamilies.Prov D where
  KO := K
  eO := e
  Cusp := fun j w => ↥(cuspS K (Sg j w))
  Mlat := fun j w => mlatS K (Sg j w)
  supN := fun _ _ σ F => ‖σ (F : K)‖
  supN_nonneg := fun _ _ _ _ => norm_nonneg _
  supN_eq_zero := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  supN_smul := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  supN_add := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2NormAlt := fun _ _ σ F => ‖σ (F : K)‖
  l2Norm_nonneg_bis := fun _ _ _ _ => norm_nonneg _
  l2Norm_eq_zero_iff := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  l2Norm_smul_alt := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  l2Norm_add_le' := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2Norm_le_supNorm_alt := fun _ _ _ _ => le_rfl
  Cu := fun _ => Empty
  Xc := fun _ c => c.elim
  Xc_lat := fun _ c => c.elim
  FJt := fun _ _ _ _ => PUnit
  sg := fun _ _ _ _ => 0

variable {D K Sg}

theorem provS_sub {j : ℕ} {w : WeightFamilies.Wt D j} (h : ¬ Sg j w) : Subsingleton ((provS D K e Sg).Cusp j w) :=
  ⟨fun a b => Subtype.ext (by
    have ha := a.2; have hb := b.2
    simp only [cuspS, h, if_false, Submodule.mem_bot] at ha hb
    rw [ha, hb])⟩

def oneS {j : ℕ} {w : WeightFamilies.Wt D j} (h : Sg j w) : (provS D K e Sg).Cusp j w :=
  ⟨1, by simp [cuspS, h]⟩

theorem coe_oneS {j : ℕ} {w : WeightFamilies.Wt D j} (h : Sg j w) : ((oneS e h : (provS D K e Sg).Cusp j w) : K) = 1 := rfl

theorem oneS_mem {j : ℕ} {w : WeightFamilies.Wt D j} (h : Sg j w) : oneS e h ∈ (provS D K e Sg).Mlat j w :=
  (mem_mlatS K _).2 ⟨1, by rw [map_one]; rfl⟩

theorem mlat_eq_span {j : ℕ} {w : WeightFamilies.Wt D j} (h : Sg j w) :
    (provS D K e Sg).Mlat j w = Submodule.span (𝓞 K) {oneS e h} := by
  refine le_antisymm (fun F hF => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (oneS_mem e h))
  obtain ⟨r, hr⟩ := (mem_mlatS K F).1 hF
  refine Submodule.mem_span_singleton.2 ⟨r, Subtype.ext ?_⟩
  change (r • (1 : K)) = (F : K)
  rw [← hr, Algebra.smul_def, mul_one]

theorem supN_oneS {j : ℕ} {w : WeightFamilies.Wt D j} (h : Sg j w) (σ : K →+* ℂ) :
    (provS D K e Sg).supN j w σ (oneS e h) = 1 := by
  show ‖σ (1 : K)‖ = 1
  rw [map_one, norm_one]

variable (K) in

def sWS {j : ℕ} (w : WeightFamilies.Wt D j) : 𝓞 K := ((qq D ^ DF w : ℕ) : 𝓞 K)

theorem qq_pos' (D : D7) : 0 < qq D :=
  lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem sWS_ne {j : ℕ} (w : WeightFamilies.Wt D j) : sWS K w ≠ 0 := by
  unfold sWS
  exact_mod_cast (pow_pos (qq_pos' D) _).ne'

theorem log_sWS {j : ℕ} (w : WeightFamilies.Wt D j) (σ : K →+* ℂ) :
    Real.log ‖σ ((sWS K w : 𝓞 K) : K)‖ = (DF w : ℝ) * Real.log (qq D) := by
  have h : ((sWS K w : 𝓞 K) : K) = ((qq D ^ DF w : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [h, map_natCast, Complex.norm_natCast, Nat.cast_pow, Real.log_pow]

theorem smul_surjS {j : ℕ} (w : WeightFamilies.Wt D j) {s : 𝓞 K} (hs : s ≠ 0) :
    Function.Surjective (s • (LinearMap.id : (provS D K e Sg).Cusp j w →ₗ[𝓞 K] (provS D K e Sg).Cusp j w)) := by
  intro F
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hs
  refine ⟨(algebraMap (𝓞 K) K s)⁻¹ • F, Subtype.ext ?_⟩
  change s • ((algebraMap (𝓞 K) K s)⁻¹ • (F : K)) = (F : K)
  rw [Algebra.smul_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs', one_mul]

def evS (j : ℕ) : AddMonoidAlgebra K (WeightFamilies.Wt D j) →ₐ[K] K := AddMonoidAlgebra.lift K K (WeightFamilies.Wt D j) 1

theorem evS_single (j : ℕ) (w : WeightFamilies.Wt D j) (a : K) : evS (D := D) (K := K) j (AddMonoidAlgebra.single w a) = a := by
  rw [evS, AddMonoidAlgebra.lift_single]; simp

def incS (j : ℕ) (w : WeightFamilies.Wt D j) : (provS D K e Sg).Cusp j w →ₗ[K] AddMonoidAlgebra K (WeightFamilies.Wt D j) where
  toFun F := AddMonoidAlgebra.single w (F : K)
  map_add' F G := by rw [Submodule.coe_add, AddMonoidAlgebra.single_add]
  map_smul' c F := by rw [Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, AddMonoidAlgebra.smul_single']

theorem incS_apply (j : ℕ) (w : WeightFamilies.Wt D j) (F : (provS D K e Sg).Cusp j w) :
    incS e j w F = AddMonoidAlgebra.single w (F : K) := rfl

theorem evS_incS (j : ℕ) (w : WeightFamilies.Wt D j) (F : (provS D K e Sg).Cusp j w) :
    evS (D := D) (K := K) j (incS e j w F) = (F : K) := evS_single j w _

def coefS (j : ℕ) (w : WeightFamilies.Wt D j) : AddMonoidAlgebra K (WeightFamilies.Wt D j) →ₗ[K] K where
  toFun F := F.coeff w
  map_add' F G := by rw [AddMonoidAlgebra.coeff_add]; rfl
  map_smul' c F := by rw [AddMonoidAlgebra.coeff_smul]; rfl

open Classical in
theorem coefS_single (j : ℕ) (w w' : WeightFamilies.Wt D j) (a : K) :
    coefS (D := D) (K := K) j w (AddMonoidAlgebra.single w' a) = if w' = w then a else 0 := by
  classical
  show (AddMonoidAlgebra.single w' a).coeff w = _
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

variable (Sg)

def pjS (hadd : ∀ j w w', Sg j w → Sg j w' → Sg j (wadd w w')) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (dat : P.Dat)
    (h1 : j < D.R.m → P.rk dat = D.R.r) (h2 : j < D.R.m → P.jj dat = (D.R.sigW j).1)
    (hPt : ∀ p, Nonempty ((P.loc dat p).Pt (P.loc dat p).YY)) : PJ D (provS D K e Sg) P j where
  Forms := AddMonoidAlgebra K (WeightFamilies.Wt D j)
  rF := inferInstance
  aF := (inferInstance : Algebra K (AddMonoidAlgebra K (WeightFamilies.Wt D j)))
  aFO := (inferInstance : Algebra (𝓞 K) (AddMonoidAlgebra K (WeightFamilies.Wt D j)))
  stF := IsScalarTower.of_algebraMap_eq fun x => rfl
  inc := fun w => incS e j w
  inc_inj := fun w F G h => Subtype.ext (by
    have := congrArg (evS (D := D) (K := K) j) h
    rwa [evS_incS, evS_incS] at this)
  inc_indep := by
    classical
    rw [iSupIndep_def]
    intro w
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨F, rfl⟩ := LinearMap.mem_range.1 hx
    have hle : (⨆ w' ≠ w, LinearMap.range (incS (Sg := Sg) e j w')) ≤ LinearMap.ker (coefS (D := D) (K := K) j w) := by
      refine iSup₂_le fun w' hw' => ?_
      rintro _ ⟨G, rfl⟩
      rw [LinearMap.mem_ker, incS_apply, coefS_single, if_neg hw']
    have h0 := hle hx'
    rw [LinearMap.mem_ker, incS_apply, coefS_single, if_pos rfl] at h0
    rw [incS_apply, h0, AddMonoidAlgebra.single_zero]
  inc_mul := fun w w' F G => by
    refine ⟨⟨(F : K) * (G : K), ?_⟩, ?_⟩
    · by_cases hF : Sg j w
      · by_cases hG : Sg j w'
        · simp [cuspS, hadd j w w' hF hG]
        · have := G.2; simp only [cuspS, hG, if_false, Submodule.mem_bot] at this
          rw [this, mul_zero]; exact Submodule.zero_mem _
      · have := F.2; simp only [cuspS, hF, if_false, Submodule.mem_bot] at this
        rw [this, zero_mul]; exact Submodule.zero_mem _
    · show AddMonoidAlgebra.single w (F : K) * AddMonoidAlgebra.single w' (G : K) =
        AddMonoidAlgebra.single (wadd w w') ((F : K) * (G : K))
      rw [AddMonoidAlgebra.single_mul_single]; rfl
  dat := dat
  dat_rk := h1
  dat_jj := h2
  Pt := fun la => (P.loc dat (resCh la)).Pt (P.loc dat (resCh la)).YY
  pt66 := fun _ y => y
  vAt := fun la _ F => vE la (evS (D := D) (K := K) j F)
  vAt_zero := fun la _ => by rw [map_zero, vE_zero]
  vAt_ne_bot := fun la _ F => vE_ne_bot la _
  vAt_add := fun la _ F G => by rw [map_add]; exact vE_add la _ _
  vAt_smul := fun la _ a F ha => by
    rw [map_smul, smul_eq_mul, vE_mul, vE_of_ne la ha]
  vAt_mul := fun la _ w w' F G => by rw [map_mul, vE_mul]
  Mlat_eq := fun w F => by
    rw [show F ∈ (provS D K e Sg).Mlat j w ↔ _ from mem_mlatS K F]
    constructor
    · rintro ⟨r, hr⟩ la y
      show 0 ≤ vE la (evS (D := D) (K := K) j (incS e j w F))
      rw [evS_incS]
      by_cases h0 : (F : K) = 0
      · rw [h0, vE_zero]; exact le_top
      · rw [vE_nonneg_iff la h0, ← hr]; exact la.valuation_le_one r
    · intro h
      by_cases h0 : (F : K) = 0
      · exact ⟨0, by rw [map_zero, h0]⟩
      · have hv : ∀ la : HeightOneSpectrum (𝓞 K), la.valuation K (F : K) ≤ 1 := fun la => by
          obtain ⟨y⟩ := hPt (resCh la)
          have := h la y
          change 0 ≤ vE la (evS (D := D) (K := K) j (incS e j w F)) at this
          rw [evS_incS] at this
          exact (vE_nonneg_iff la h0).1 this
        obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (F : K) hv
        exact ⟨r, hr⟩
  thAll := fun w => ((provS D K e Sg).Mlat j w).comap (sWS K w • LinearMap.id)
  shortTh := fun w => (provS D K e Sg).Mlat j w

end Model

section Lemmas

variable {D : D7} {K : Type} [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O) {Sg : ∀ j, WeightFamilies.Wt D j → Prop}
  (hadd : ∀ j w w', Sg j w → Sg j w' → Sg j (wadd w w')) (P : ModuliIntegralCharts.Prov D) {j : ℕ} (dat : P.Dat)
  (h1 : j < D.R.m → P.rk dat = D.R.r) (h2 : j < D.R.m → P.jj dat = (D.R.sigW j).1)
  (hPt : ∀ p, Nonempty ((P.loc dat p).Pt (P.loc dat p).YY))

theorem pjS_inc (w : WeightFamilies.Wt D j) (F : (provS D K e Sg).Cusp j w) :
    (pjS e Sg hadd P j dat h1 h2 hPt).inc w F = AddMonoidAlgebra.single w (F : K) := rfl

theorem pjS_vAt (la : HeightOneSpectrum (𝓞 K)) (y : (pjS e Sg hadd P j dat h1 h2 hPt).Pt la)
    (F : (pjS e Sg hadd P j dat h1 h2 hPt).Forms) :
    (pjS e Sg hadd P j dat h1 h2 hPt).vAt la y F = vE la (evS (D := D) (K := K) j F) := rfl

theorem vAt_inc_oneS {w : WeightFamilies.Wt D j} (h : Sg j w) (la : HeightOneSpectrum (𝓞 K))
    (y : (pjS e Sg hadd P j dat h1 h2 hPt).Pt la) :
    (pjS e Sg hadd P j dat h1 h2 hPt).vAt la y ((pjS e Sg hadd P j dat h1 h2 hPt).inc w (oneS e h)) = 0 := by
  show vE la (evS (D := D) (K := K) j (incS e j w (oneS e h))) = 0
  rw [evS_incS, coe_oneS, vE_one]

theorem nonZeroComp_oneS {w : WeightFamilies.Wt D j} (h : Sg j w) :
    (pjS e Sg hadd P j dat h1 h2 hPt).NonZeroComp w (oneS e h) := by
  intro w' G hG
  have := congrArg (evS (D := D) (K := K) j) hG
  change evS (D := D) (K := K) j (incS e j w (oneS e h) * incS e j w' G) = evS (D := D) (K := K) j 0 at this
  rw [map_mul, map_zero, evS_incS, evS_incS, coe_oneS, one_mul] at this
  exact Subtype.ext this

theorem subMulS : Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul (pjS e Sg hadd P j dat h1 h2 hPt) := by
  intro σ w w' F G H hH
  have := congrArg (evS (D := D) (K := K) j) hH
  change evS (D := D) (K := K) j (incS e j _ H) = evS (D := D) (K := K) j (incS e j w F * incS e j w' G) at this
  rw [map_mul, evS_incS, evS_incS, evS_incS] at this
  show ‖σ (H : K)‖ ≤ ‖σ (F : K)‖ * ‖σ (G : K)‖
  rw [this, map_mul, norm_mul]

theorem wwc_sWS (w : WeightFamilies.Wt D j) :
    (pjS e Sg hadd P j dat h1 h2 hPt).WWc (sWS K w) w = (provS D K e Sg).Mlat j w := by
  show (((provS D K e Sg).Mlat j w).comap (sWS K w • LinearMap.id)).map (sWS K w • LinearMap.id) = _
  exact Submodule.map_comap_eq_of_surjective (smul_surjS e w (sWS_ne w)) _

theorem wwc_oneS {w : WeightFamilies.Wt D j} (h : Sg j w) :
    (pjS e Sg hadd P j dat h1 h2 hPt).WWc (sWS K w) w = Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => oneS e h) := by
  rw [Set.range_const, wwc_sWS, mlat_eq_span]

theorem depth_le_zeroS {w : WeightFamilies.Wt D j} (h : Sg j w) (la : HeightOneSpectrum (𝓞 K))
    (y : (pjS e Sg hadd P j dat h1 h2 hPt).Pt la) :
    (pjS e Sg hadd P j dat h1 h2 hPt).depth (sWS K w) w la y ≤ 0 := by
  have hm : oneS e h ∈ (pjS e Sg hadd P j dat h1 h2 hPt).WWc (sWS K w) w := by
    rw [wwc_oneS e hadd P dat h1 h2 hPt h]; exact Submodule.subset_span ⟨0, rfl⟩
  calc (pjS e Sg hadd P j dat h1 h2 hPt).depth (sWS K w) w la y
      ≤ (pjS e Sg hadd P j dat h1 h2 hPt).vAt la y ((pjS e Sg hadd P j dat h1 h2 hPt).inc w (oneS e h)) :=
        iInf₂_le (oneS e h) hm
    _ = 0 := vAt_inc_oneS e hadd P dat h1 h2 hPt h la y

end Lemmas

end Mod

section Asm

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

def CombHyps (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (Qf : ∀ la, LocalPointData G la) : Prop :=
  HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ∧
  LatAt B j ka ∧ SupBoundByL2AtWeight large₂ B j ka K.CG K.AG ∧ LAMwAt large₂ B j ka K.CL K.AL ∧
  (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) ∧
  G.TiedW S Gc Prw ∧ G.TiedTh S Gc ∧ G.TiedZ S T Gc ∧
  G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah ∧ G.TiedEt large₂ K.Cf K.Af ∧
  DeepHerm (X j h1 h2) ka ∧ DeepSubMul (X j h1 h2) ∧ DeepLogD (X j h1 h2) ka Pd ∧
  PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd ∧
  ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) ∧
  ShareRho (D := D) (j := j) T G.rz ((X j h1 h2).rk ka (B.Mlat j ka)) ∧
  ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) ∧
  PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ∧
  (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
  (∀ la, InContainZ G la S T) ∧ (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) ∧
  CombBound G S (cc D large₂ C2 A2 CR wL) nus ∧
  Heights Qf Gc PH Prw Pet

theorem concl_of_combHyps (hP : Conclusion1OfComb (D := D) (B := B) (P := P)) {large₂ : SizeData₂ D} {X : Prov D B P} {K : KAdm}
    {H : KHyp} {Ch Ah Cq Aq C2 A2 CR CT : ℝ} {j : ℕ} {h1 : 1 ≤ j} {h2 : j ≤ D.R.m} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    {G : GlobalFamilyData (X j h1 h2) ka wL wF} {Gc PH Prw Pet Pd : ℝ} {Qf : ∀ la, LocalPointData G la}
    (h : CombHyps large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus G Gc PH Prw Pet Pd Qf) :
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26⟩ := h
  exact hP large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus a1 a2 a3 a4 a5 G Gc PH Prw Pet Pd Qf
    a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26

def lastP (D : D7) (j : ℕ) : Fin (D.R.sigW j).1 :=
  ⟨D.R.k + j - 1 - 1, by have := D.R.m_add_three_le_k; simp only [Ranks.sigW]; omega⟩

def SetCn (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) {j : ℕ} (CK C1 : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ)
    (h0 : ℝ) : Prop :=
  ka.n = D.R.nV ∧
  (∀ τ i, i.1 + 1 < (D.R.sigW j).1 →
    ((Tp D j T * (Tp D j T + 2 * D.R.r) : ℕ) : ℤ) ≤ gapZ (ka.aP τ) i + 2) ∧
  (∀ τ i, i.1 + 1 < (D.R.sigW j).2 →
    ((Tp D j T * (Tp D j T + 2 * D.R.r) : ℕ) : ℤ) ≤ gapZ (ka.aM τ) i + 2) ∧
  4 * (T : ℝ) ^ 2 + D.R.t + 1 ≤ h0 ∧
  (∀ τ, h0 / 4 - D.R.t ≤ (ncAt ka τ : ℝ)) ∧
  (∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
    h0 / 2 - ((D.R.t : ℝ) + 1) / 2 ≤ (ka.aP τ i : ℝ)) ∧
  (∀ τ (i : Fin (D.R.sigW j).2), i.1 + 1 = (D.R.sigW j).2 →
    h0 / 2 - ((D.R.t : ℝ) + 1) / 2 ≤ (ka.aM τ i : ℝ)) ∧
  ka.size ≤ CK * D.R.k * D.R.f * large₂.sc.b ∧
  Even nP ∧ 8 * D.R.f * D.R.r + 4 ≤ nP ∧ nP ≤ nW ∧ (nW : ℝ) ≤ sizeConstantAtParamsWeight D nW ∧
  D.R.f * D.R.r * (D.R.r + 1) ≤ nW ∧ D.R.nV = nP + T * nW ∧
  IsL D ka wL T nW ∧ IsF' ka wL wF T nP ∧
  wL.size ≤ CK * D.R.k * D.R.f * large₂.sc.b / T ∧
  0 < T ∧ WeightFamilies.dimY D j ≤ T ∧ 40 * (WeightFamilies.dimY D j + 2) ≤ T ∧
  (WeightFamilies.dimY D j + 2) * nW + 2 * D.R.r ≤ T ∧
  40 ≤ nW ∧ n0 D j ≤ T ∧ 11 * WeightFamilies.dimY D j ^ 2 ≤ T ∧
  OPO large₂ B ∧
  DomAt D large₂ j nW C1

theorem setC_of_setCn {large₂ : SizeData₂ D} {j : ℕ} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ}
    {h0 : ℝ} (h : SetCn large₂ B CK C1 ka wL wF T nP nW h0) : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0 := h

theorem L_nonneg' (large₂ : SizeData₂ D) : 0 ≤ large₂.sc.L := Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _

theorem Zb_nonneg' (large₂ : SizeData₂ D) : 0 ≤ Zb D large₂ := by
  unfold Zb; have := L_nonneg' large₂; positivity

theorem lamStar_nonneg' (D : D7) : 0 ≤ lamStar D := by
  unfold lamStar
  have hg : ∀ i, (1 : ℝ) ≤ D.host.g i := fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hf : (2 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.n := D.R.toFrame.ord_pos
    have : 2 ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ (D.host.g 0 : ℝ) * D.host.g 1 := one_le_mul_of_one_le_of_one_le (hg 0) (hg 1)
  have ha : (1 : ℝ) ≤ ((D.R.f : ℝ) / 2) ^ 2 := one_le_pow₀ (by linarith)
  have h2 : (1 : ℝ) ≤ 4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) ha) hq) hd
  exact add_nonneg (Real.log_nonneg h1) (Real.log_nonneg h2)

theorem lam_nonneg' (D : D7) : 0 ≤ lamStar D + 2 * Real.log D.host.pde := by
  have : (1 : ℝ) ≤ D.host.pde := by exact_mod_cast D.host.pde_prime.one_lt.le
  have := Real.log_nonneg this
  have := lamStar_nonneg' D
  linarith

theorem log_qq_le' (D : D7) : 0 ≤ Real.log (qq D : ℝ) ∧ Real.log (qq D : ℝ) ≤ lamStar D := by
  have hg : ∀ i, (1 : ℝ) ≤ D.host.g i := fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le
  have hq1 : (1 : ℝ) ≤ (qq D : ℝ) := by exact_mod_cast qq_pos' D
  have hq0 : (qq D : ℝ) ≤ D.host.g 0 := by exact_mod_cast (min_le_left _ _ : qq D ≤ D.host.g 0)
  have hle : (qq D : ℝ) ≤ (D.host.g 0 : ℝ) * D.host.g 1 := by nlinarith [hg 0, hg 1]
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hf : (2 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.n := D.R.toFrame.ord_pos
    have : 2 ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have ha : (1 : ℝ) ≤ ((D.R.f : ℝ) / 2) ^ 2 := one_le_pow₀ (by linarith)
  have h2 : (1 : ℝ) ≤ 4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) ha) hq) hd
  have h3 := Real.log_le_log (by linarith) hle
  have h4 := Real.log_nonneg h2
  unfold lamStar
  exact ⟨Real.log_nonneg hq1, by linarith⟩

theorem dF_le_size' {j : ℕ} (w : WeightFamilies.Wt D j) : (DF w : ℝ) ≤ w.size := by
  have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  have h3 : (DF w : ℝ) = ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ)) := by
    simp only [DF, degP, Nat.cast_sum, Nat.cast_add]
  unfold WeightFamilies.Wt.size
  rw [h3]
  linarith

theorem sW_sizes' {j : ℕ} (w : WeightFamilies.Wt D j) :
    0 ≤ (DF w : ℝ) * Real.log (qq D) ∧ (DF w : ℝ) / 2 * Real.log (qq D) ≤ (DF w : ℝ) * Real.log (qq D) ∧
      (DF w : ℝ) * Real.log (qq D) ≤ (lamStar D + 2 * Real.log D.host.pde) * w.size := by
  obtain ⟨h0, h1⟩ := log_qq_le' D
  have hD : (0 : ℝ) ≤ DF w := Nat.cast_nonneg _
  have hp : 0 ≤ Real.log (D.host.pde : ℝ) := Real.log_nonneg (by exact_mod_cast D.host.pde_prime.one_lt.le)
  have hm : 0 ≤ (DF w : ℝ) * Real.log (qq D) := mul_nonneg hD h0
  refine ⟨hm, by linarith, ?_⟩
  calc (DF w : ℝ) * Real.log (qq D) ≤ w.size * (lamStar D + 2 * Real.log D.host.pde) :=
        mul_le_mul (dF_le_size' w) (by linarith) h0 (by linarith [WeightFamilies.Wt.one_le_size w])
    _ = _ := mul_comm _ _

theorem pN_nonneg' (large₂ : SizeData₂ D) {j : ℕ} (wL : WeightFamilies.Wt D j) : 0 ≤ PN D large₂ * wL.size := by
  unfold PN
  have := L_nonneg' large₂; have := lamStar_nonneg' D; have := WeightFamilies.Wt.one_le_size wL
  exact mul_nonneg (by linarith) (by linarith)

theorem rescaled_dimension_product_nonneg (large₂ : SizeData₂ D) {j : ℕ} (wL : WeightFamilies.Wt D j) :
    0 ≤ PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) * WeightFamilies.dimY D j * wL.size := by
  unfold PI4
  have := Zb_nonneg' large₂; have := lamStar_nonneg' D; have := WeightFamilies.Wt.one_le_size wL
  have h : 0 ≤ 5 * (1009 * Zb D large₂ + lamStar D) + 2 * (81 * Zb D large₂ ^ 2) / (WeightFamilies.dimY D j : ℝ) := by positivity
  exact mul_nonneg (mul_nonneg h (Nat.cast_nonneg _)) (by linarith)

theorem growth_constant_nonneg (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) : 0 ≤ Formalism.MainNotions.WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) D.host.pde := by
  unfold Formalism.MainNotions.WeightAlgebra.Gc
  have hZ := Zb_nonneg' large₂; have hL := L_nonneg' large₂; have hl := lam_nonneg' D
  have hn : (1 : ℝ) ≤ (Module.finrank ℚ B.KO : ℝ) := by exact_mod_cast Module.finrank_pos
  have hdisc : (1 : ℝ) ≤ |((NumberField.discr B.KO : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero B.KO)
  have hA : 0 ≤ Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO :=
    add_nonneg (Real.log_nonneg hn) (div_nonneg (Real.log_nonneg hdisc) (by linarith))
  have hM := le_max_of_le_left (c := Real.log (Module.finrank ℚ D.host.E) +
    Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| / Module.finrank ℚ D.host.E) hA
  have hfr : 0 ≤ 2 * (D.R.f : ℝ) * D.R.r := by positivity
  have := mul_nonneg hfr hl
  nlinarith

structure NumRun (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT G0 PH Prw Pet Pd : ℝ)
    {j : ℕ} (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (τ0 : D.what₂.Tau) : Prop where
  parA : ParA large₂ H.CA
  setC : SetCn large₂ B H.CK H.C1 ka wL wF T nP nW h0
  h3 : H3 large₂ H C2 A2 CR 0 wL T
  h4 : large₂.sc.b ≤ ka.size ∧ (T : ℝ) * wL.size ≤ 2 * ka.size ∧
    wF.size ≤ ((WeightFamilies.dimY D j : ℝ) + 2) * wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T ∧
    WeightFamilies.PPv D large₂ C2 A2 ^ 3 * (T : ℝ) ^ 2 ≤ large₂.sc.b ∧ WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ≤ large₂.sc.b ∧
    (∀ i, 2 * DF ka + 2 < D.host.g i)
  g2 : ∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2
  Tx : (T : ℝ) ≤ large₂.sc.x ^ CT
  poly : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq G0 PH Prw Pet Pd ka
  page : WeightFamilies.PPv D large₂ K.CG K.AG * (1 + Real.log ka.size) ≤ Pd
  pd : 0 ≤ Pd

def SgOf (τ0 : D.what₂.Tau) (c1 c2 : ℕ) : ∀ j, WeightFamilies.Wt D j → Prop :=
  fun j w => (c2 : ℤ) * w.aP τ0 (lastP D j) ≤ (c1 : ℤ) * w.n

theorem sgOf_add (τ0 : D.what₂.Tau) (c1 c2 : ℕ) (j : ℕ) (w w' : WeightFamilies.Wt D j) (h : SgOf τ0 c1 c2 j w)
    (h' : SgOf τ0 c1 c2 j w') : SgOf τ0 c1 c2 j (wadd w w') := by
  unfold SgOf at *
  simp only [wadd]
  push_cast
  linarith

section Sep

variable {j : ℕ} (τ0 : D.what₂.Tau) {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ}

theorem sg_wL : SgOf τ0 (wL.aP τ0 (lastP D j)) wL.n j wL := by
  unfold SgOf; rw [mul_comm]

theorem not_sg_wF (hs : (wL.aP τ0 (lastP D j) : ℤ) * wF.n < (wL.n : ℤ) * wF.aP τ0 (lastP D j)) :
    ¬ SgOf τ0 (wL.aP τ0 (lastP D j)) wL.n j wF := by
  unfold SgOf; push_neg; linarith

theorem not_signCondition_baseFormWeight (X : PJ D B P j)
    (hs : (wL.aP τ0 (lastP D j) : ℤ) * wF.n < (wL.n : ℤ) * wF.aP τ0 (lastP D j)) :
    ¬ SgOf τ0 (wL.aP τ0 (lastP D j)) wL.n j (X.wF0 wL wF) := by
  unfold SgOf PJ.wF0; simp only [wadd, wsmul]; push_cast; push_neg
  nlinarith

theorem not_sg_ka (hn : ka.n = nP + T * nW) (hL : wL.n = nW) (hF : wF.n = nP)
    (haP : (wF.aP τ0 (lastP D j) : ℤ) = ka.aP τ0 (lastP D j) - T * wL.aP τ0 (lastP D j))
    (hs : (wL.aP τ0 (lastP D j) : ℤ) * wF.n < (wL.n : ℤ) * wF.aP τ0 (lastP D j)) :
    ¬ SgOf τ0 (wL.aP τ0 (lastP D j)) wL.n j ka := by
  unfold SgOf; push_neg
  rw [hn]; rw [hL, hF] at hs; rw [hL]; push_cast
  have : (ka.aP τ0 (lastP D j) : ℤ) = wF.aP τ0 (lastP D j) + T * wL.aP τ0 (lastP D j) := by linarith
  rw [this]; nlinarith

theorem signCondition_of_secondWeight {w2 : WeightFamilies.Wt D j} (hg : IsG2 wL wF w2)
    (hs : (wL.aP τ0 (lastP D j) : ℤ) * wF.n < (wL.n : ℤ) * wF.aP τ0 (lastP D j)) :
    SgOf τ0 (wL.aP τ0 (lastP D j)) wL.n j w2 := by
  unfold SgOf
  obtain ⟨h1, h2, -⟩ := hg
  have a := h2 τ0 (lastP D j)
  have a' : (w2.aP τ0 (lastP D j) : ℤ) + wF.aP τ0 (lastP D j) = (WeightFamilies.dimY D j + 4) * wL.aP τ0 (lastP D j) := by
    exact_mod_cast a
  have b' : (w2.n : ℤ) + wF.n = (WeightFamilies.dimY D j + 4) * wL.n := by exact_mod_cast h1
  have e1 : (w2.aP τ0 (lastP D j) : ℤ) = (WeightFamilies.dimY D j + 4) * wL.aP τ0 (lastP D j) - wF.aP τ0 (lastP D j) := by linarith
  have e2 : (w2.n : ℤ) = (WeightFamilies.dimY D j + 4) * wL.n - wF.n := by linarith
  rw [e1, e2]; nlinarith

end Sep

theorem dimY_pos' (D : D7) {j : ℕ} (h1 : 1 ≤ j) : 0 < WeightFamilies.dimY D j := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.n := D.R.toFrame.ord_pos
    unfold Ranks.f; omega
  have hp : 3 ≤ (D.R.sigW j).1 := by
    show 3 ≤ D.R.k + j - 1
    omega
  have h2 : 1 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul (by omega) (by omega)
  unfold WeightFamilies.dimY
  exact Nat.mul_pos hf (by omega)

theorem sep_of_setCn {large₂ : SizeData₂ D} {j : ℕ} (τ0 : D.what₂.Tau) {CK C1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ}
    {h0 : ℝ} (h : SetCn large₂ B CK C1 ka wL wF T nP nW h0) :
    (wL.aP τ0 (lastP D j) : ℤ) * wF.n < (wL.n : ℤ) * wF.aP τ0 (lastP D j) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hPW, -, -, -, hL, hF, -, -, -, -, -, h40, -⟩ := h
  have hlast : ¬ ((lastP D j).1 + 1 < (D.R.sigW j).1) := by
    have := D.R.m_add_three_le_k
    simp only [lastP, Ranks.sigW]; omega
  have g := hL.2.1 τ0 (lastP D j)
  rw [if_neg hlast] at g
  unfold gapZ at g
  rw [dif_neg hlast] at g
  have f := hF.2.1 τ0 (lastP D j)
  rw [hL.1, hF.1]
  have hT' : (0 : ℤ) < (Tp D j T : ℤ) := by unfold Tp; positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hT'.le] at g
  have hq := Int.ediv_mul_le ((ka.aP τ0 (lastP D j) : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) hT'.ne'
  rw [← g] at hq
  unfold Tp at hq
  push_cast at hq
  have hL0 : (0 : ℤ) ≤ (wL.aP τ0 (lastP D j) : ℤ) := Int.natCast_nonneg _
  have hPW' : (nP : ℤ) ≤ nW := by exact_mod_cast hPW
  have h40' : (40 : ℤ) ≤ nW := by exact_mod_cast h40
  have hD0 : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) := Int.natCast_nonneg _
  have hr0 : (0 : ℤ) ≤ (D.R.r : ℤ) := Int.natCast_nonneg _
  generalize (wL.aP τ0 (lastP D j) : ℤ) = L at hq f hL0 ⊢
  generalize (wF.aP τ0 (lastP D j) : ℤ) = F at hq f ⊢
  generalize (ka.aP τ0 (lastP D j) : ℤ) = k at hq f ⊢
  generalize (WeightFamilies.dimY D j : ℤ) = Dz at hq hD0
  generalize (nP : ℤ) = p at hPW' ⊢
  generalize (nW : ℤ) = w at hPW' h40' hq ⊢
  have hF : L * (Dz + 2) + (Dz + 2) * w + 2 * (D.R.r : ℤ) ≤ F := by nlinarith
  have a1 : L * p ≤ L * w := mul_le_mul_of_nonneg_left hPW' hL0
  have a2 : 0 ≤ w * (F - (L * (Dz + 2) + (Dz + 2) * w + 2 * (D.R.r : ℤ))) := mul_nonneg (by linarith) (by linarith)
  have a3 : 0 ≤ w * L * Dz := mul_nonneg (mul_nonneg (by linarith) hL0) hD0
  have a4 : 0 ≤ w * w * Dz := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hD0
  have a5 : 0 ≤ w * (D.R.r : ℤ) := mul_nonneg (by linarith) hr0
  have a6 : 0 < w * w := mul_pos (by linarith) (by linarith)
  have a7 : 0 ≤ w * L := mul_nonneg (by linarith) hL0
  nlinarith

theorem subm_top {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Subsingleton M] (N : Submodule R M) : N = ⊤ :=
  eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact N.zero_mem

theorem subm_le {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Subsingleton M] (N N' : Submodule R M) : N ≤ N' :=
  fun x _ => by rw [Subsingleton.elim x 0]; exact N'.zero_mem

theorem h1m (D : D7) : 1 ≤ D.R.m := by have := D.R.two_le_m; omega

open Formalism.MainNotions.DIV.Inh in

theorem combHyps_inhabited (K : Type) [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O) (P : ModuliIntegralCharts.Prov D)
    (hP : ∀ j, 1 ≤ j → j ≤ D.R.m → HasDat P j)
    (hPt : ∀ (d : P.Dat) (p : ℕ), Nonempty ((P.loc d p).Pt (P.loc d p).YY))
    (τ0 : D.what₂.Tau) (large₂ : SizeData₂ D) (Kc : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT G0 PH Prw Pet Pd h0 : ℝ)
    (ka wL wF : WeightFamilies.Wt D D.R.m) (T nP nW : ℕ)
    (hN : NumRun large₂ (provS D K e (SgOf τ0 (wL.aP τ0 (lastP D D.R.m)) wL.n)) Kc H Ch Ah Cq Aq C2 A2 CR CT G0 PH Prw Pet Pd
      ka wL wF T nP nW h0 τ0) :
    ∃ (X : Prov D (provS D K e (SgOf τ0 (wL.aP τ0 (lastP D D.R.m)) wL.n)) P)
      (S : Scal (provS D K e (SgOf τ0 (wL.aP τ0 (lastP D D.R.m)) wL.n)))
      (G : GlobalFamilyData (X D.R.m (h1m D) le_rfl) ka wL wF) (Qf : ∀ la, LocalPointData G la),
      CombHyps large₂ X Kc H Ch Ah Cq Aq C2 A2 CR CT D.R.m (h1m D) le_rfl S ka wL wF T nP nW h0 0 G G0 PH Prw Pet Pd Qf := by
  classical
  set Sg := SgOf τ0 (wL.aP τ0 (lastP D D.R.m)) wL.n with hSg
  have hadd : ∀ j w w', Sg j w → Sg j w' → Sg j (wadd w w') := sgOf_add τ0 _ _
  set B := provS D K e Sg with hB
  let X : Prov D B P := fun j h1 h2 =>
    pjS e Sg hadd P j (hP j h1 h2).choose (hP j h1 h2).choose_spec.1 (hP j h1 h2).choose_spec.2
      (hPt (hP j h1 h2).choose)
  have hd1 := (hP D.R.m (h1m D) le_rfl).choose_spec.1
  have hd2 := (hP D.R.m (h1m D) le_rfl).choose_spec.2
  have hpt := hPt (hP D.R.m (h1m D) le_rfl).choose
  set Xm := X D.R.m (h1m D) le_rfl with hXm
  have hXd : Xm = pjS e Sg hadd P D.R.m (hP D.R.m (h1m D) le_rfl).choose hd1 hd2 hpt := rfl
  have hm : ¬ D.R.m < D.R.m := lt_irrefl _
  obtain ⟨c1, -, -, -, -, -, -, -, -, -, -, -, -, c14, c15, c16, -⟩ := hN.setC
  have hL : Sg D.R.m wL := sg_wL τ0
  have hs := sep_of_setCn τ0 hN.setC
  haveI hka : Subsingleton (B.Cusp D.R.m ka) :=
    provS_sub e (not_sg_ka τ0 (c1.trans c14) c15.1 c16.1 (c16.2.1 τ0 (lastP D D.R.m)) hs)
  haveI hwF : Subsingleton (B.Cusp D.R.m wF) := provS_sub e (not_sg_wF τ0 hs)
  haveI hwF0 : Subsingleton (B.Cusp D.R.m (Xm.wF0 wL wF)) := provS_sub e (not_signCondition_baseFormWeight τ0 Xm hs)
  have hww : Xm.WWc (sWS K wL) wL = B.Mlat D.R.m wL := wwc_sWS e hadd P _ hd1 hd2 hpt wL
  let G : GlobalFamilyData Xm ka wL wF :=
    { N := 1, w := fun _ => oneS e hL, del := 0, th' := Fin.elim0, rz := 0, alz := Fin.elim0, th0 := Fin.elim0,
      zc := Fin.elim0, rq := 0, th := Fin.elim0, iet := 1, et := 0, mx := fun _ => 0 }
  have hJ : ∀ la, Jid Xm la G.w = ⊤ := fun la => jid_top_one Xm la G.w (dimY_pos' D (h1m D))
  let Qf : ∀ la, LocalPointData G la := fun la =>
    { y := fun ζ => ((pts_empty G (hJ la)).false ζ).elim, g0 := 0, c := fun _ => 0 }
  have hsz : ∀ w : WeightFamilies.Wt D D.R.m, 0 ≤ w.size := fun w => by linarith [WeightFamilies.Wt.one_le_size w]
  have hPoly := hN.poly
  obtain ⟨-, -, hG0, hPrw, -⟩ := hPoly
  refine ⟨X, ⟨sWS K wL, 1, 1, 1⟩, G, Qf, ?_⟩
  unfold CombHyps
  refine ⟨?_, ?_, ?_, ?_, fun h => absurd h hm, ?_, fun i => i.elim0, ?_, ?_, fun h => absurd h hm, ?_, ?_, ?_, hN.page,
    by simp [ShareRd], ?_, ?_, hN.poly, fun la => inBasis_of G (hJ la) rfl, fun la => inCurve_of _ (hJ la),
    fun la => inTie_of _ (hJ la) _, fun la _ _ _ => inLift_of _ (hJ la) _, ?_, ?_, ?_, heights_of G Qf hJ rfl _ _ _ _⟩
  ·
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hN.h4
    obtain ⟨w2, hw2⟩ := hN.g2
    have hW2 : Sg D.R.m w2 := signCondition_of_secondWeight τ0 hw2 hs
    refine ⟨hN.parA, hN.setC, ?_, ?_, ?_, hN.h3, ?_, hN.Tx⟩
    · obtain ⟨s1, s2, s3⟩ := sW_sizes' wL
      refine ⟨sWS_ne wL, one_ne_zero, one_ne_zero, one_ne_zero,
        fun σ => ⟨(log_sWS wL σ).symm ▸ s1, (log_sWS wL σ).symm ▸ s2⟩, D.host.pde, Set.mem_insert _ _, fun σ => ?_,
        1009 * Zb D large₂, le_rfl, ?_⟩
      · have e1 : Real.log ‖σ (((1 : 𝓞 K) : K))‖ = 0 := by simp
        refine ⟨(log_sWS wL σ).symm ▸ s3, ?_, ?_, ?_⟩ <;> (try rw [e1]) <;> [exact mul_nonneg (lam_nonneg' D) (hsz _);
          exact mul_nonneg (mul_nonneg zero_le_two (lam_nonneg' D)) (hsz _); exact mul_nonneg (mul_nonneg zero_le_two (lam_nonneg' D)) (hsz _)]
      · refine ⟨⟨{oneS e hL}, ?_, fun _ => 0, ?_, ?_⟩, ⟨∅, by simp, subm_top _, by simp⟩, ⟨∅, by simp, subm_top _, by simp⟩,
          ⟨∅, by simp, subm_top _, by simp⟩⟩
        · rw [Finset.coe_singleton, hww, mlat_eq_span e hL]
        · intro σ g hg
          rw [Finset.mem_singleton] at hg
          rw [hg, supN_oneS, Real.log_one]
        · simp only [Finset.sum_const_zero, zero_div]
          exact mul_nonneg (growth_constant_nonneg large₂ B) (hsz _)
    · refine ⟨fun _ => le_rfl, by simp, ?_⟩
      simpa using (pN_nonneg' large₂ wL)
    · exact ⟨le_of_eq hww, subm_le _ _, subm_le _ _, subm_le _ _⟩
    · refine ⟨a1, a2, a3, a4, a5, a6, 1009 * Zb D large₂, 81 * Zb D large₂ ^ 2, le_rfl, le_rfl, fun h => absurd h hm, w2, hw2,
        oneS e hW2, oneS_mem e hW2, nonZeroComp_oneS e hadd P _ hd1 hd2 hpt hW2, fun σ => ?_⟩
      rw [supN_oneS e _, Real.log_one]
      exact (rescaled_dimension_product_nonneg large₂ wL)
  ·
    exact ⟨by rw [show B.Mlat D.R.m ka = ⊥ from Subsingleton.elim _ _]; exact Submodule.fg_bot, subm_top _⟩
  ·
    intro F σ
    rw [Subsingleton.elim F 0, (B.supN_eq_zero _ _ _ _).2 rfl, (B.l2Norm_eq_zero_iff _ _ _ _).2 rfl]
    simp
  ·
    intro F _ hF
    exact absurd (Subsingleton.elim F 0) hF
  ·
    refine ⟨?_, fun _ => oneS_mem e hL, ?_, fun σ k => by rw [supN_oneS e _, Real.log_one], ?_⟩
    · rw [Set.range_const, hww, mlat_eq_span e hL]
    · show Real.log ((1 : ℕ) : ℝ) ≤ _
      simp only [Nat.cast_one, Real.log_one]
      exact mul_nonneg hPrw (by linarith [WeightFamilies.Wt.one_le_size wL])
    · show (∑ _σ : K →+* ℂ, (0 : ℝ)) / _ ≤ _
      simp only [Finset.sum_const_zero, zero_div]
      exact mul_nonneg hG0 (hsz _)
  ·
    refine ⟨fun k => k.elim0, fun k => k.elim0, Fin.elim0, ?_⟩
    simp [Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly]
  ·
    refine ⟨?_, fun i => i.elim0, subm_top _, fun i => i.elim0⟩
    unfold WeightFamilies.rhoP
    haveI : Subsingleton (B.Mlat D.R.m ka) := inferInstance
    exact (Module.finrank_zero_of_subsingleton).symm
  ·
    refine ⟨0, ⟨fun _ => 0, fun σ f => ?_⟩, ?_⟩
    · rw [Subsingleton.elim f 0, (B.l2Norm_eq_zero_iff _ _ _ _).2 rfl]; simp
    · intro σ f g; simp
  ·
    exact subMulS e hadd P _ hd1 hd2 hpt
  ·
    show Real.log (finrank B.KO (B.Cusp D.R.m ka) : ℝ) ≤ Pd
    rw [Module.finrank_zero_of_subsingleton]; simpa using hN.pd
  · unfold ShareRho; simp only [CharP.cast_eq_zero]; positivity
  · unfold ShareRhoP; simp only [CharP.cast_eq_zero]; positivity
  ·
    intro la
    refine Submodule.span_le.2 ?_
    rintro v ⟨al, θ, -, -, rfl⟩
    rw [Subsingleton.elim θ 0, map_zero, map_zero, mul_zero]
    exact Submodule.zero_mem _
  ·
    intro la
    refine Submodule.span_le.2 ?_
    rintro v ⟨F, -, rfl⟩
    simp only [Subsingleton.elim F 0, map_zero]
    exact Submodule.zero_mem _
  ·
    intro la y
    refine ⟨fun h => absurd h hm, fun _ => ?_⟩
    have h1 : Xm.depth (sWS K wL) wL la y ≤ 0 := depth_le_zeroS e hadd P _ hd1 hd2 hpt hL la y
    show Xm.depth (sWS K wL) wL la y ≤ (((0 : HeightOneSpectrum (𝓞 B.KO) → ℝ) la : ℝ) : EReal)
    simpa using h1

end Asm

section P66Model

open Formalism.MainNotions.DIV.Inh Formalism.MainNotions.DIV.Inh.LocalProvisionModel in

theorem exists_moduli_model_nonempty_points (D : D7) : ∃ P : ModuliIntegralCharts.Prov D, (∀ j, 1 ≤ j → j ≤ D.R.m → HasDat P j) ∧
    ∀ (d : P.Dat) (p : ℕ), Nonempty ((P.loc d p).Pt (P.loc d p).YY) := by
  let P : ModuliIntegralCharts.Prov D := provDegenerate D {x : ℕ × ℕ // 1 ≤ x.2 ∧ x.2 + 1 ≤ x.1} (fun x => x.1.1) (fun x => x.1.2) (fun x => x.2)
      (fun _ p => mpTrivialAb D p (nonempty_coefficient_field p).some)
  have hfull : ∀ r j, 1 ≤ j → j + 1 ≤ r → ∃ w : P.Dat, P.rk w = r ∧ P.jj w = j :=
    fun r j h1 h2 => ⟨⟨(r, j), h1, h2⟩, rfl, rfl⟩
  exact ⟨P, fun j h1 _ => HasDat_of_full P hfull j h1, fun _ _ => ⟨()⟩⟩

theorem combHyps_inhabited_of_num {D : D7} (K : Type) [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O)
    (τ0 : D.what₂.Tau) (large₂ : SizeData₂ D) (Kc : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT G0 PH Prw Pet Pd h0 : ℝ)
    (ka wL wF : WeightFamilies.Wt D D.R.m) (T nP nW : ℕ)
    (hN : NumRun large₂ (provS D K e (SgOf τ0 (wL.aP τ0 (lastP D D.R.m)) wL.n)) Kc H Ch Ah Cq Aq C2 A2 CR CT G0 PH Prw Pet Pd
      ka wL wF T nP nW h0 τ0) :
    ∃ (P : ModuliIntegralCharts.Prov D) (X : Prov D (provS D K e (SgOf τ0 (wL.aP τ0 (lastP D D.R.m)) wL.n)) P)
      (S : Scal (provS D K e (SgOf τ0 (wL.aP τ0 (lastP D D.R.m)) wL.n)))
      (G : GlobalFamilyData (X D.R.m (h1m D) le_rfl) ka wL wF) (Qf : ∀ la, LocalPointData G la),
      CombHyps large₂ X Kc H Ch Ah Cq Aq C2 A2 CR CT D.R.m (h1m D) le_rfl S ka wL wF T nP nW h0 0 G G0 PH Prw Pet Pd Qf := by
  obtain ⟨P, hP, hPt⟩ := exists_moduli_model_nonempty_points D
  exact ⟨P, combHyps_inhabited K e P hP hPt τ0 large₂ Kc H Ch Ah Cq Aq C2 A2 CR CT G0 PH Prw Pet Pd h0 ka wL wF T nP nW hN⟩

end P66Model

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Inh

end
