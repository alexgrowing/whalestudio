import Mathlib
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsExtAllModelsUniformised
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueTranslatedProductValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumSupportCMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsThetaValData
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfCastDvd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionFieldStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EmbEqOfInPsi
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.ThetaBound

theorem exists_resChar (T : CDVR) (h : T.FinRes) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ∀ n : ℕ, Nat.Coprime n ℓ → IsUnit (n : T.V) := by
  have : Finite (ResidueField T.V) := h
  refine ⟨ringChar (ResidueField T.V), CharP.char_is_prime (ResidueField T.V) _, fun n hn => ?_⟩
  rw [← residue_ne_zero_iff_isUnit, map_natCast]
  intro h0
  have hd := (ringChar.spec _ n).1 h0
  exact (CharP.char_is_prime (ResidueField T.V) (ringChar (ResidueField T.V))).ne_one
    (Nat.Coprime.eq_one_of_dvd hn.symm hd)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem nrm_mul (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α β : 𝓞 E) :
    nrm Dw c a (α * β) = nrm Dw c a α * nrm Dw c a β := by
  simp only [nrm, map_mul, mul_pow, Finset.prod_mul_distrib]

theorem nrm_ne_zero (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) {α : 𝓞 E} (h : α ≠ 0) : nrm Dw c a α ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
  simpa [embK] using h

theorem nrm_isIntegral (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E) : IsIntegral ℤ (nrm Dw c a α) := by
  refine IsIntegral.prod _ fun τ _ => IsIntegral.pow ?_ _
  exact (RingOfIntegers.isIntegral α).map (embK c τ).toIntAlgHom

theorem vLa_nonneg {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {x : K} (h0 : x ≠ 0)
    (h : IsIntegral ℤ x) : 0 ≤ vLa la x := by
  have h1 : la.valuation K x ≤ 1 := la.valuation_le_one (⟨x, h⟩ : 𝓞 K)
  have h2 := (WithZero.log_le_log ((la.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 h1
  simp only [WithZero.log_one] at h2
  simp only [vLa]; omega

theorem vLa_mul {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) : vLa la (x * y) = vLa la x + vLa la y := by
  simp only [vLa, map_mul,
    WithZero.log_mul ((la.valuation K).ne_zero_iff.2 hx) ((la.valuation K).ne_zero_iff.2 hy)]
  ring

theorem killed_pow (Xo : Moduli Dw l) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (h : KilledBy Xo (l.Mb ^ 2) t) :
    KilledBy Xo l.Mb (t ^ l.M) := by
  intro a ha
  rw [← TorsFac.act_nat, Category.assoc, ← Xo.univ.t.act.mul]
  exact h _ (by rw [pow_two]; exact Ideal.mul_mem_mul (TorsFac.M_mem l) ha)

theorem exists_fac (Xo : Moduli Dw l) (π : 𝓞 E) (hM : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ l.M → ¬ ℓ ^ 2 ∣ l.M ∧
      ∃ α α' : 𝓞 E, α * α' = π ∧ α * H.bar α = (ℓ : 𝓞 E) ∧ l.Mb ≤ Ideal.span {H.bar α}) (ℓ : ℕ) (hp : ℓ.Prime) :
    ∃ (n' A Bn : ℕ) (α α' β : 𝓞 E), α * α' = π ∧ Nat.Coprime n' ℓ ∧ (l.M : 𝓞 E) = β * α * n' ∧
      α * H.bar α = (A : 𝓞 E) ∧ β * H.bar β = (Bn : 𝓞 E) ∧
      ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo (l.Mb ^ 2) t →
        t ^ (l.M ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 := by
  obtain ⟨h1, h2⟩ := TorsFac.factorisation E H Dw l Xo l.M ℓ l.odd dvd_rfl hp
  by_cases hd : ℓ ∣ l.M
  · obtain ⟨hs, α, α', e1, e2, e3⟩ := hM ℓ hp hd
    obtain ⟨n', Bn, j, β, a1, a2, a3, -, a5⟩ := h2 α ℓ e2 hs (Or.inl ⟨rfl, e3⟩)
    exact ⟨n', ℓ, Bn, α, α', β, e1, a1, a2, e2, a3, fun T t ht => a5 T t (killed_pow Xo t ht) ⟨2, ht⟩⟩
  · obtain ⟨n', j, a1, a2, a3⟩ := h1 hd
    refine ⟨n', 1, ℓ ^ (2 * j), 1, π, (ℓ : 𝓞 E) ^ j, one_mul _, a1, ?_, by simp, ?_, fun T t ht => ?_⟩
    · rw [a2]; push_cast; ring
    · rw [map_pow, map_natCast]; push_cast; ring
    · obtain ⟨b1, b2, -⟩ := a3 T t (killed_pow Xo t ht) ⟨2, ht⟩
      exact ⟨b1, b2⟩

theorem bound_of_chBound (Xo : Moduli Dw l) (c : Coeff l) (π : 𝓞 E) (hπ : π ≠ 0)
    (hM : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ l.M → ¬ ℓ ^ 2 ∣ l.M ∧
      ∃ α α' : 𝓞 E, α * α' = π ∧ α * H.bar α = (ℓ : 𝓞 E) ∧ l.Mb ≤ Ideal.span {H.bar α})
    [inst : StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (la : HeightOneSpectrum (𝓞 c.F))
    (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ρ : ℝ)
    (hρ : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (e : ℕ),
      OverLa la T.V io e → ChBound C e ρ w n)
    (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (hy : T.FinRes)
    (f : Rul Xo c) (hf : f ∈ thGen Xo c nab w n) :
    ((-(ρ + ((vLa la (nrm Dw c w π) : ℤ) : ℝ)) : ℝ) : EReal) ≤ nval T.V e (evI y f) := by
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hnab.1
  letI := H.starRing
  obtain ⟨x, P, hP, hf⟩ := hf
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨T', iT, r, y', C', ⟨hr, hiT, φ, hφ, hmap⟩, hfin, hgood, hrat⟩ :=
    Prep.exists_good_chart_allRat E H Dw l Xo c hnab.1 T io y hy (l.M ^ 2) (pow_pos hM0 2)
  have ho' := ho.bc iT hr hiT
  rw [← nval_bc iT hr hiT e]
  obtain ⟨ℓ, hp, hu⟩ := exists_resChar T' hfin
  obtain ⟨n', A, Bn, α, α', β, e1, a1, a2, a3, a4, a5⟩ := exists_fac Xo π hM ℓ hp
  letI := (iT.comp io).toAlgebra
  choose F hF using fun b : Fin n =>
    (RatData.exists_thetaVal_data E H Dw l Xo c T'.Fr y'.1).1 hrat (x b)
  have hev : iT (evI y f) = thExpr Xo c nab y'.1 P F := by
    letI : Algebra T.Fr T'.Fr := iT.toAlgebra
    exact GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field E H Dw l Xo c nab hnab T io y T'.Fr φ hφ y'.1 hmap w n x P hP F hF f hf
  have ht : ∀ b, ∃ t' : ptO Xo (xOf y') ⟶ Xo.univ.t.G, KilledBy Xo (l.Mb ^ 2) t' ∧
      IsUUOver Xo.univ.t.G Xo.univ.t.PP l.M (sOf1 y') 1 t' (F b) := by
    intro b
    have h1 : levPt Xo y'.1.x (x b) ^ l.M = 1 := by
      obtain ⟨t', -, -, -, -, b1, b2, -⟩ := hF b
      rw [← b1, ← pow_mul, ← pow_two]
      exact (a5 _ t' b2).1
    obtain ⟨t', -, b2, b3⟩ := (uu_through_moves E H Dw l Xo T'.Fr (xOf y') l.M l.odd (sOf1 y')).2 _ _ (F b) h1 (hF b)
    exact ⟨t', b2, b3⟩
  choose t' ht1 ht2 using ht
  have hb := GlobalTheory.T.harmonicValue_translated_product_valuation_bound E H Dw l Xo c hnab.1 T' (iT.comp io) y' C' hgood nab hnab (r * e) ρ w n ho'.1
    (hρ T' _ y' C' _ ho') l.M n' A Bn α β l.odd a2 a3 a4 (hu n' a1) (fun _ => 1) t' F
    (fun b => ⟨one_pow _, (a5 _ _ (ht1 b)).1, by
      haveI := Xo.univ.t.act.hom (α * β)
      rw [MonObj.one_comp, one_pow], (a5 _ _ (ht1 b)).2, ht2 b⟩) P hP.1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ffvMap E H Dw l c w n P hP T' _)
  have hh := (hv_linear E H Dw l Xo c hnab.1 nab hnab T'.Fr y'.1 n P).2.2 l.M F
  have hα : α ≠ 0 := by rintro rfl; exact hπ (by rw [← e1, zero_mul])
  have hα' : α' ≠ 0 := by rintro rfl; exact hπ (by rw [← e1, mul_zero])
  rw [map_mul, _root_.mul_assoc, nval_smul ho' (nrm_ne_zero c w hα), ← hh] at hb
  have hv1 : vLa la (nrm Dw c w α) ≤ vLa la (nrm Dw c w π) := by
    rw [← e1, nrm_mul, vLa_mul la (nrm_ne_zero c w hα) (nrm_ne_zero c w hα')]
    have := vLa_nonneg la (nrm_ne_zero (Dw := Dw) c w hα') (nrm_isIntegral c w α')
    omega
  rw [hev]
  change _ ≤ _ + nval T'.V (r * e) (thExpr Xo c nab y'.1 P F) at hb
  generalize nval T'.V (r * e) (thExpr Xo c nab y'.1 P F) = v at hb ⊢
  have hv2 : ((vLa la (nrm Dw c w α) : ℤ) : ℝ) ≤ ((vLa la (nrm Dw c w π) : ℤ) : ℝ) := by exact_mod_cast hv1
  induction v using EReal.rec with
  | bot => simp at hb
  | top => exact le_top
  | coe v =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hb
    rw [EReal.coe_le_coe_iff]
    linarith

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons GlobalTheory.PlaceTop in

theorem thBound : ThBoundSt := by
  intro D T h j hj hinj EX hO w g hg la y
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  obtain ⟨Tc, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
  have hv : vAtV y g = nval Tc.V e (evI yI g) := by
    show y.1.1 g = _
    rw [hq]
    rfl
  rw [hv, ← nrm_eq_nnW D T h j hj hinj EX w]
  obtain ⟨-, hpi, -⟩ := HalfGen.half_principal_and_split D T.toCore h.toLawsCore.toLawsM EX
  have hbar : ∀ i, T.Q.H.bar (EX.piG i) = piBarO EX i := fun i => (hpi i).1
  have hn : ∀ i, EX.piG i * T.Q.H.bar (EX.piG i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    have h2 : piBarO EX i * T.Q.H.bar (piBarO EX i) = _ := (hpi i).2
    rw [← h2, ← hbar, TorsFac.bar_bar, _root_.mul_comm]
  have h0 : ∀ i, EX.piG i ≠ 0 := fun i hi => by
    have := hn i
    rw [hi, zero_mul] at this
    exact (D.host.g_prime i).ne_zero (by exact_mod_cast this.symm)
  have hMe : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  refine bound_of_chBound (T.Q.Xo j) T.Q.c (EX.piG 0 * EX.piG 1) (mul_ne_zero (h0 0) (h0 1)) ?_ (T.nab j) hnab la
    (wtA w) w.n (ramLoss D la w) ?_ Tc io e ho yI hy g hg
  · intro ℓ hp hd
    have p0 := D.host.g_prime 0
    have p1 := D.host.g_prime 1
    have hne := D.host.g_ne
    rw [hMe] at hd ⊢
    rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp p0).1 h1
      refine ⟨fun h2 => hne ?_, EX.piG 0, EX.piG 1, rfl, hn 0, by rw [hbar]; exact hO 0⟩
      rw [pow_two] at h2
      exact (Nat.prime_dvd_prime_iff_eq p0 p1).1 (Nat.dvd_of_mul_dvd_mul_left p0.pos h2)
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp p1).1 h1
      refine ⟨fun h2 => hne ?_, EX.piG 1, EX.piG 0, _root_.mul_comm _ _, hn 1, by rw [hbar]; exact hO 1⟩
      rw [pow_two] at h2
      exact ((Nat.prime_dvd_prime_iff_eq p1 p0).1 (Nat.dvd_of_mul_dvd_mul_right p1.pos h2)).symm
  · intro T' io' y' C' e' ho'
    have hc := GlobalTheory.T.harmonicValuationLowerBound_hostField_all_places D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c hnab.1 T' io' y' C' e' ho'.1 (wtA w) w.n
      (WeightAlgebra.DF w) (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.DF_wtA_le (T.Q.Dw j) w)
    convert hc using 1
    refine Finset.sum_congr rfl fun p _ => ?_
    have h1 := ho'.2 (p : T.Q.c.F)
    rw [map_natCast] at h1
    have he : (e' : ℝ) ≠ 0 := by exact_mod_cast ho'.1.ne'
    rw [h1]
    push_cast
    rw [mul_div_cancel_left₀ _ he]

end GlobalTheory.ThetaBound
