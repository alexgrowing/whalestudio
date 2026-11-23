import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLatOfOfLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRule
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MemberLatFull

section Abstract

open NumberField IsDedekindDomain Formalism.L2.Pj

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]

theorem val_smul_nonneg {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : IsVal la v) (a : 𝓞 K) {f : R}
    (h : 0 ≤ v f) : 0 ≤ v ((a : K) • f) := by
  by_cases ha : (a : K) = 0
  · rw [ha, zero_smul, hv.zero]; exact le_top
  · rw [hv.smul _ _ ha]
    refine add_nonneg ?_ h
    exact_mod_cast vAdd_int_nonneg la ha

theorem val_nonneg_of_pow {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : IsVal la v) {f : R} (k : ℕ)
    (h : 0 ≤ v (f ^ (k + 1))) : 0 ≤ v f := by
  by_contra h0
  rw [not_le] at h0
  refine absurd h (not_le.2 ?_)
  clear h
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    rw [pow_succ, hv.mul]
    calc v (f ^ (k + 1)) + v f ≤ v (f ^ (k + 1)) + 0 := add_le_add le_rfl h0.le
      _ < 0 := by simpa using ih

variable (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))

def Den (P : HeightOneSpectrum (𝓞 K) → Prop) (f : R) : Prop :=
  ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ la, P la → ∀ v ∈ Vs la, 0 ≤ v ((t : K) • f)

variable {Vs} (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) {P P' : HeightOneSpectrum (𝓞 K) → Prop}

theorem Den.mono {f : R} (h : Den Vs P f) (hP : ∀ la, P' la → P la) : Den Vs P' f :=
  let ⟨t, h0, h1⟩ := h
  ⟨t, h0, fun la hl => h1 la (hP la hl)⟩

include hV

theorem den_of_smul {f : R} {t : K} (ht : t ≠ 0) (h : Den Vs P (t • f)) : Den Vs P f := by
  obtain ⟨s, hs, h1⟩ := h
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) t
  have hb0 : (b : K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have ha : a ≠ 0 := by
    rintro rfl
    simp at ht
  refine ⟨s * a, mul_ne_zero hs ha, fun la hl v hv => ?_⟩
  have := val_smul_nonneg (hV la v hv) b (h1 la hl v hv)
  rw [smul_smul, smul_smul] at this
  convert this using 3
  change algebraMap (𝓞 K) K (s * a) = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K s * _
  have hb1 : algebraMap (𝓞 K) K b ≠ 0 := hb0
  rw [map_mul]
  field_simp

theorem den_zero : Den Vs P (0 : R) :=
  ⟨1, one_ne_zero, fun la _ v hv => by rw [smul_zero, (hV la v hv).zero]; exact le_top⟩

theorem Den.add {f g : R} (hf : Den Vs P f) (hg : Den Vs P g) : Den Vs P (f + g) := by
  obtain ⟨s, hs, h1⟩ := hf
  obtain ⟨t, ht, h2⟩ := hg
  refine ⟨s * t, mul_ne_zero hs ht, fun la hl v hv => ?_⟩
  have a1 := val_smul_nonneg (hV la v hv) t (h1 la hl v hv)
  have a2 := val_smul_nonneg (hV la v hv) s (h2 la hl v hv)
  rw [smul_smul] at a1 a2
  rw [smul_add, show ((s * t : 𝓞 K) : K) = (s : K) * (t : K) from map_mul (algebraMap (𝓞 K) K) s t]
  rw [mul_comm] at a1
  exact (le_min a1 a2).trans ((hV la v hv).add _ _)

theorem Den.smul {f : R} (hf : Den Vs P f) (a : K) : Den Vs P (a • f) := by
  by_cases ha : a = 0
  · rw [ha, zero_smul]; exact den_zero hV
  · refine den_of_smul hV (inv_ne_zero ha) ?_
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem den_of_span {S : Set R} (hS : ∀ g ∈ S, Den Vs P g) {f : R} (hf : f ∈ Submodule.span K S) : Den Vs P f := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact den_zero hV
  | add x y _ _ hx hy => exact hx.add hV hy
  | smul a x _ hx => exact hx.smul hV a

theorem exists_den_of_span {S : Set R}
    (hS : ∀ g ∈ S, ∃ N : ℕ, N ≠ 0 ∧ Den Vs (fun la => (N : 𝓞 K) ∉ la.asIdeal) g) {f : R}
    (hf : f ∈ Submodule.span K S) : ∃ N : ℕ, N ≠ 0 ∧ Den Vs (fun la => (N : 𝓞 K) ∉ la.asIdeal) f := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨1, one_ne_zero, den_zero hV⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M * N, mul_ne_zero hM hN, (hx.mono fun la hl h => hl (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)).add hV
      (hy.mono fun la hl h => hl (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h))⟩
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    exact ⟨N, hN, hx.smul hV a⟩

theorem Den.union {f : R} (h : Den Vs P f) (h' : Den Vs (fun la => ¬ P la) f) : Den Vs (fun _ => True) f := by
  obtain ⟨s, hs, h1⟩ := h
  obtain ⟨t, ht, h2⟩ := h'
  refine ⟨s * t, mul_ne_zero hs ht, fun la _ v hv => ?_⟩
  rw [show ((s * t : 𝓞 K) : K) = (s : K) * (t : K) from map_mul (algebraMap (𝓞 K) K) s t]
  by_cases hl : P la
  · rw [mul_comm, mul_smul]
    exact val_smul_nonneg (hV la v hv) t (h1 la hl v hv)
  · rw [mul_smul]
    exact val_smul_nonneg (hV la v hv) s (h2 la hl v hv)

theorem Den.of_pow {f : R} {k : ℕ} (h : Den Vs P (f ^ (k + 1))) : Den Vs P f := by
  obtain ⟨t, ht, h1⟩ := h
  refine ⟨t, ht, fun la hl v hv => val_nonneg_of_pow (hV la v hv) k ?_⟩
  have := val_smul_nonneg (hV la v hv) (t ^ k) (h1 la hl v hv)
  rw [smul_smul, show ((t ^ k : 𝓞 K) : K) = (t : K) ^ k from map_pow (algebraMap (𝓞 K) K) t k] at this
  rwa [smul_pow, pow_succ (t : K)]

theorem span_latOf_eq_top [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] (C : Submodule K R)
    (h : ∀ f ∈ C, Den Vs (fun _ => True) f) : Submodule.span K (latOf C Vs hV : Set C) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨t, ht, h1⟩ := h f.1 f.2
  have ht0 : (t : K) ≠ 0 := by exact_mod_cast ht
  have h2 : (t : K) • f ∈ Submodule.span K (latOf C Vs hV : Set C) :=
    Submodule.subset_span fun la v hv => h1 la trivial v hv
  have h3 := Submodule.smul_mem _ (t : K)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ ht0, one_smul] at h3

theorem fullLat_of [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] (C : Submodule K R) [FiniteDimensional K C]
    (N : (K →+* ℂ) → R → ℝ) (hN : ∀ σ, IsNormOn C σ (N σ)) (B : ℝ)
    (hB : ∀ F ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v F) → F ≠ 0 → -B ≤ ∑ σ : K →+* ℂ, Real.log (N σ F))
    (h : ∀ f ∈ C, Den Vs (fun _ => True) f) : Formalism.IndefR.FWT.FullLat C Vs hV :=
  ⟨GlobalTheory.IntCuspLat.fg_latOf_of_lowerBound C Vs hV N hN B hB, span_latOf_eq_top hV C h⟩

omit hV in
theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (h0 : N ≠ 0) (h : (N : 𝓞 K) ∈ la.asIdeal) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ N ∧ (ℓ : 𝓞 K) ∈ la.asIdeal := by
  induction N using induction_on_primes with
  | zero => exact absurd rfl h0
  | one => exact absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) la.isPrime.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases la.isPrime.mem_or_mem h with h | h
    · exact ⟨p, hp, dvd_mul_right _ _, h⟩
    · obtain ⟨ℓ, h1, h2, h3⟩ := ih (right_ne_zero_of_mul h0) h
      exact ⟨ℓ, h1, h2.mul_left _, h3⟩

omit hV in
theorem isIntegral_zpow_of_pow_eq_one {x : K} {m : ℕ} (hm : 0 < m) (h : x ^ m = 1) (e : ℕ) (z : ℤ) :
    IsIntegral ℤ ((x ^ e) ^ z) := by
  refine IsIntegral.of_pow hm ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, mul_comm, pow_mul, h, one_pow, one_zpow]
  exact isIntegral_one

end Abstract

section Lat

open NumberField Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem trivAt_of_coprime {Λ : GenLat E n} {N M ℓ : ℕ} (hU : Λ.Unimod) (hL : Λ.LevOK N M) (h : N.Coprime ℓ) :
    Λ.TrivAt ℓ := by
  classical
  refine ⟨N, h, Submodule.smul_le.2 fun r hr v hv => ?_, hL.2.2.trans inf_le_left⟩
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  rw [mul_smul]
  refine Submodule.smul_mem _ _ fun i _ => ?_
  have h1 : (Pi.single i 1 : Fin n → E) ∈ stdLat E n := fun j _ => by
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne hj]
      exact Submodule.zero_mem _
  have h2 : (N : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Λ.La :=
    (hL.2.2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) h1)).1
  obtain ⟨y, hy⟩ := (hU v).1 hv _ h2
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at hy
  have h3 : IsIntegral ℤ (IsCMField.complexConj E (algebraMap (𝓞 E) E y)) :=
    map_isIntegral_int (IsCMField.complexConj E : E →+* E) (RingOfIntegers.isIntegral_coe y)
  refine Submodule.mem_one.2 ⟨⟨_, h3⟩, ?_⟩
  change IsCMField.complexConj E (algebraMap (𝓞 E) E y) = _
  rw [hy]
  simp [Algebra.smul_def, mul_comm]

end Lat

section Span

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Dict

theorem isIntegral_w {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hI : d.I = ⊤)
    {ph : (Fin n → LaJ Xo c d) → c.F} {ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ} {x₀ : Fin n → LaJ Xo c d}
    (h : d.PhiPin ph ψ x₀) (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂) : _root_.IsIntegral ℤ (d.w x0 q) := by
  have hz : ∀ (l : Geo.Tor.Level H) (c : Coeff l), 0 < l.M' ∧ (⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ l.M' = 1 := fun l c => by
    have h0 : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
    have h1 : zeta l.M' ^ l.M' = 1 := (Complex.isPrimitiveRoot_exp l.M' h0.ne').pow_eq_one
    exact ⟨h0, Subtype.ext (by simpa using h1)⟩
  haveI : Subsingleton (LaJ Xo c d) := by
    rw [Submodule.Quotient.subsingleton_iff, hI, Ideal.map_top, Submodule.top_smul]
  obtain ⟨-, -, -, h1, -, h2⟩ := h
  have h3 := h2 q
  rw [finsum_eq_single _ x₀ (fun x hx => absurd (Subsingleton.elim x x₀) hx), h1, map_one, one_mul] at h3
  unfold DeltaDat.w
  rw [map_mul, h3]
  refine _root_.IsIntegral.mul ?_ (isIntegral_zpow_of_pow_eq_one (hz _ d.c₂).1 (hz _ d.c₂).2 _ _)
  exact map_isIntegral_int (d.eF : c.F →+* d.c₂.F) (isIntegral_zpow_of_pow_eq_one (hz _ c).1 (hz _ c).2 _ _)

set_option maxHeartbeats 1000000 in

theorem den_of_large (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (n : ℕ) (hdom : Dom a n) (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n) (f : T.toCore.R j)
    (hf : f ∈ T.toCore.cuspA j a n) : Den (T.toCore.Vs j) (fun _ => True) f := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hU := h.unf j hj T.toCore.σ₀ T.toCore.good_σ₀
  have hrk : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := hU.1
  have hr : 1 ≤ D.R.r := by
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have h1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n := by
    have h0 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have : D.R.r ≤ Module.finrank ℚ D.host.E * D.R.r := Nat.le_mul_of_pos_left _ h0
    omega
  have hd : ∃ d : DeltaDat (T.Q.Xo j) T.Q.c n, d.IsLev ∧
      (∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧
      d.pd = 1 ∧ d.I = ⊤ ∧ d.l₂.A = T.Q.l.A ∧ d.l₂.M = T.Q.l.M ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, e0, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c h1 n 1 ⊤ T.Q.l (T.Q.Xo j) T.Q.c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨g, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character _ _ _ _ _ _ n d hlev hnr 1
    exact ⟨{ d with φδ := g }, hlev, hnab, hδ, e1, e0, congrArg (·.A) e2, congrArg (·.M) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hI, hAe, hMe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL _ _ (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  have hone : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (z : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ z = 1 :=
    fun k _ _ z => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
  have hunit : UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : T.Q.c.Fˣ) : T.Q.c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [hone K y, hone K y']
    simp
  have hsf : Squarefree d.l₂.M := by
    rw [hMe, h.pins.2.1.1, Nat.squarefree_mul ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)]
    exact ⟨(D.host.g_prime 0).squarefree, (D.host.g_prime 1).squarefree⟩
  have hspan : ∀ bad : ℕ, 0 < bad → f ∈ Submodule.span T.Q.c.F (shortGen (T.Q.Xo j) T.Q.c nab bad 0 a n d) := by
    intro bad hbad
    have htot : ShortValTot (T.Q.Xo j) T.Q.c nab bad 0 a n d :=
      GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ _ _ n d (GlobalTheory.levelMaps_closed hL _ _ _ h1)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.1
        (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ (T.Q.Xo j) T.Q.c)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
        nab bad 0 a
    obtain ⟨hr0, hm⟩ := h.modelW j hj T.toCore.σ₀ T.toCore.good_σ₀
    have hsp := GlobalTheory.Dict.holSub0_le_span_shortGen hC _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d T.toCore.σ₀ D.R.r
      (Formalism.L2.PjFree.Unf.ofPj (T.U j T.toCore.σ₀)) T.toCore.good_σ₀ hU hr h.pins.2.1.2
      (fun k k' => ⟨(hm k).1.trans (hm k').1.symm, (hm k).2.trans (hm k').2.symm⟩)
      (fun k ga hga hv => GlobalTheory.RunIn.gamAt_of_lawsM D T.toCore h.toLawsM j hj _ T.toCore.good_σ₀ k ga hga fun x hx => by
        obtain ⟨u, hu, he⟩ := hv x hx
        refine ⟨u, hu, ?_⟩
        rw [he, Nat.cast_smul_eq_nsmul]
        exact add_sub_cancel_left _ _)
      hlev hnab hunit h3 (fun _ => ⟨ph, 1, x₀, hpin⟩) nab bad 0 a hbad hdom hn
      (fun k => h.chiTriv j hj _ T.toCore.good_σ₀ _ _ hdom k) htot
    have hf' := (Formalism.L2.Pj.mem_cusp _ _ _ a n f).1 hf
    have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c
      T.toCore.σ₀ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j T.toCore.σ₀)) hU a n).1
    refine mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj (T.U j T.toCore.σ₀)))
      (sec (T.Q.Xo j) T.Q.c a n) hind _ (fun g hg => hg.1) hf'.1 (hsp ?_)
    exact ⟨hf'.2 _ T.toCore.good_σ₀, fun k x hx => dif_neg hx⟩
  obtain ⟨st, hnab⟩ := hnab
  have hV : ∀ la, ∀ v ∈ T.toCore.Vs j la, IsVal la v := fun la => isVal_valSet la
  have key : ∀ bad : ℕ, ∀ g ∈ shortGen (T.Q.Xo j) T.Q.c nab bad 0 a n d, ∃ (Λ : GenLat D.host.E n) (N : ℕ),
      Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.LevOK N d.l₂.M ∧
      Den (T.toCore.Vs j) (fun la => ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 T.Q.c.F) ∈ la.asIdeal ∧ Λ.TrivAt ℓ) g := by
    rintro bad g ⟨hsec, Λ, N, x0, P, a1, a2, a3, a4, -, a6, a7⟩
    obtain ⟨t, ht, hb⟩ := GlobalTheory.IntCuspLat.exists_smul_nonneg_of_shortRule D _ _ _ _ _ n d hlev hnab
      (fun k _ _ z => by rw [hone k z, one_pow]) (isIntegral_w d hI hpin) hsf Λ N a1 a3 a4 a P a6 x0 g hsec a7
    refine ⟨Λ, N, a1, a2, a4, den_of_smul hV ht ⟨1, one_ne_zero, ?_⟩⟩
    rintro la ⟨ℓ, b1, b2, b3⟩ v hv
    exact val_smul_nonneg (hV la v hv) 1 (hb la ℓ b1 b2 b3 v hv)
  obtain ⟨N, hN, hden⟩ := exists_den_of_span hV (fun g hg => by
    obtain ⟨Λ, N, a1, -, a4, hg⟩ := key 1 g hg
    refine ⟨N, a4.1.pos.ne', hg.mono fun la hl => ?_⟩
    obtain ⟨ℓ, b1, -, b3⟩ := exists_prime_mem la (N := Ideal.absNorm la.asIdeal)
      (fun h0 => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)) (Ideal.absNorm_mem _)
    refine ⟨ℓ, b1, b3, trivAt_of_coprime a1 a4 ((Nat.Prime.coprime_iff_not_dvd b1).2 ?_).symm⟩
    rintro ⟨m, rfl⟩
    exact hl (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ b3)) (hspan 1 Nat.one_pos)
  refine hden.union hV (den_of_span hV (fun g hg => ?_) (hspan N (Nat.pos_of_ne_zero hN)))
  obtain ⟨Λ, N', -, ⟨k, a2, a3⟩, -, hg⟩ := key N g hg
  refine hg.mono fun la hl => ?_
  obtain ⟨ℓ, b1, b2, b3⟩ := exists_prime_mem la hN (not_not.1 hl)
  exact ⟨ℓ, b1, b3, k, a2.coprime_dvd_right b2, a3⟩

theorem pow_mem_cusp (D : D7) (T : Core D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n)
    (f : T.R j) (hf : f ∈ T.cuspA j a n) (k : ℕ) :
    ∃ a', Dom a' ((k + 1) * n) ∧ f ^ (k + 1) ∈ T.cuspA j a' ((k + 1) * n) := by
  induction k with
  | zero => exact ⟨a, by simpa using hdom, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨a', h1, h2⟩ := ih
    have hm : CuspMul (T.Q.Xo j) T.Q.c (T.U j) :=
      (Formalism.L2.PjFree.cuspMul_ofPj (T.U j)).1 (GlobalTheory.CuspProduct.cuspMul_holds _ _ _ _ _ _ _ _)
    refine ⟨a' + a, ?_, ?_⟩
    · rw [Nat.succ_mul]
      exact ⟨fun τ => (h1.1 τ).add (hdom.1 τ), h1.2.add hdom.2⟩
    · rw [Nat.succ_mul, pow_succ]
      exact hm a' a _ n _ f h1 hdom h2 hf

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem isLattice_latOf (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (hw : 0 < w.n) :
    Formalism.IndefR.FWT.FullLat (T.toCore.C j w) (T.toCore.Vs j) fun la => isVal_valSet la := by
  haveI : FiniteDimensional T.Q.c.F (T.toCore.C j w) := h.cuspFD j hj _ _ (dom_wtA w)
  obtain ⟨B, hB⟩ := GlobalTheory.IntCuspLat.exists_lowerBound D T.toCore h.toLawsM j hj w
  refine fullLat_of _ _ (T.toCore.Ns j w)
    (fun σ => (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf) B hB fun f hf => ?_
  obtain ⟨a', h1, h2⟩ := pow_mem_cusp D T.toCore j _ _ (dom_wtA w) f hf (4 * (Module.finrank ℚ D.host.E * D.R.r) + 3)
  exact (den_of_large D T h j hj a' _ h1 (Nat.le_mul_of_pos_right _ hw) _ h2).of_pow fun la => isVal_valSet la

end Span

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latFull_of_tieIn : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → LatFull T κ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ _ _ ht _ i
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity)
  refine isLattice_latOf D T ht.laws _ (inR i) (κ i) ?_
  rw [(ht.kap i τ).2.2]
  have := D.R.rank_add_five_le
  unfold Ranks.nV
  omega

end GlobalTheory.MemberLatFull
