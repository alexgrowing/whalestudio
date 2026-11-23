import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralChartCoverCuspFormNoPoleStatement

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspBound

theorem exists_mul_mem_closure {O K Ω : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field Ω] [Algebra K Ω] (S : Set Ω) {x : Ω} (hx : x ∈ Algebra.adjoin K S) :
    ∃ κ : O, κ ≠ 0 ∧ algebraMap K Ω (algebraMap O K κ) * x ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) := by
  have hmem : ∀ u : O, algebraMap K Ω (algebraMap O K u) ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) :=
    fun u => Subring.subset_closure (Or.inl ⟨u, rfl⟩)
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    exact ⟨1, one_ne_zero, by rw [map_one, map_one, one_mul]; exact Subring.subset_closure (Or.inr hx)⟩
  | algebraMap r =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) r
    have hb0 : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← map_mul, mul_div_cancel₀ _ hb0]
    exact hmem a
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x + y) =
        algebraMap K Ω (algebraMap O K t) * (algebraMap K Ω (algebraMap O K s) * x) +
        algebraMap K Ω (algebraMap O K s) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem (hmem t) h1) (mul_mem (hmem s) h2)
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x * y) =
        (algebraMap K Ω (algebraMap O K s) * x) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact mul_mem h1 h2

theorem inV_iff' (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0; simp [InV, vV]
  have hne := valV_ne_zero (V := T.V) h0
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log hne one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV; omega
  · intro h
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log hne one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_of_overLa' {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR}
    {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) (a : (la.valuation K).valuationSubring) : InV T (io a) := by
  rw [inV_iff', ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : (a : K) = 0
  · simp [h0, vLa]
  have hne : la.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h2 := (WithZero.log_le_log hne one_ne_zero).2 a.2
  rw [WithZero.log_one] at h2
  unfold vLa; omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem inV_iff_of_frBor {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {T : CDVR}
    {io : c.F →+* T.Fr} (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ)
    (h : letI := io.toAlgebra; FrBor t y.1 y'.1) : InV T (evI y f) ↔ InV T (evI y' f) := by
  obtain ⟨hE, hU, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h1 := unitIndep_of hE.wt hU a n f hf T io y y' t h 1
  have key : ∀ x : T.Fr, InV T x ↔ 0 ≤ nval T.V 1 x := fun x => by
    by_cases h0 : x = 0
    · subst h0; simp [nval_zero, InV]
    · rw [nval_of_ne h0, inV_iff', EReal.coe_nonneg]; simp
  rw [key, key, h1]

theorem inV_of_mem_B {O : Type} [CommRing O] {β : O →+* c.F} (P : GlobalTheory.Reg.PChart Xo c β) {e : P.Ω} {T : CDVR}
    {io : c.F →+* T.Fr} (ψ : P.R e →+* T.Fr) (hψ : ∀ k, ψ (algebraMap c.F _ k) = io k) (hO : ∀ a, InV T (io (β a)))
    (hg : ∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) (s : P.R e) (hs : (s : P.Ω) ∈ P.B) : InV T (ψ s) := by
  have hle : P.B ≤ (((algebraMap T.V T.Fr).range.comap ψ).map (P.R e).val.toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro w (⟨o, rfl⟩ | hw)
    · refine ⟨algebraMap c.F _ (β o), ?_, rfl⟩
      show ψ (algebraMap c.F _ (β o)) ∈ (algebraMap T.V T.Fr).range
      rw [hψ]; exact hO o
    · exact ⟨⟨w, Algebra.subset_adjoin (Or.inr hw)⟩, hg _ hw, rfl⟩
  obtain ⟨w, hw, hw'⟩ := hle hs
  obtain rfl : w = s := Subtype.ext hw'
  exact hw

end GlobalTheory.CuspBound

namespace GlobalTheory.CuspBound

set_option maxHeartbeats 1000000 in

theorem exists_bddAll_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ κ : c.F, κ ≠ 0 ∧ BddAll Xo c la κ f := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
  obtain ⟨J, hJ, P, hC, hreg⟩ := GlobalTheory.T.exists_integral_chart_cover_cuspForm_no_pole E H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
  haveI := Fintype.ofFinite J
  choose κ hκ0 hκ using fun j =>
    exists_mul_mem_closure (O := (la.valuation c.F).valuationSubring) (K := c.F) ((P j).gens : Set (P j).Ω) (hreg j)
  have hF := cusp_le_sec Xo c U a n hf
  refine ⟨algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j), ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective _ c.F)).2 (Finset.prod_ne_zero_iff.2 fun j _ => hκ0 j)
  intro T io m ho y _
  letI := io.toAlgebra
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hF
  let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
  have hW : ∀ x, x ∈ W ↔ InV T x := fun x =>
    ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h,
      by rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩
  have hO : ∀ a : (la.valuation c.F).valuationSubring, InV T (io (algebraMap _ c.F a)) := fun a => inV_of_overLa' ho a
  obtain ⟨j, e, he, ψ, z, t, hgW, hz, ht⟩ := hC T.Fr W (fun a => (hW _).2 (hO a)) y.1
  have hzI : Integral T io z := (P j).int e he T io ψ (fun a => hO a) (fun g hg => (hW _).1 (hgW g hg)) z hz
  let z' : IntFr Xo c T io := ⟨z, hE.test _ z, hzI⟩
  set κ' := algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j) with hκ'
  rw [← evI_smul, inV_iff_of_frBor (Submodule.smul_mem _ κ' hF) y z' t ht, evI_smul]
  show InV T (io κ' * evR Xo c f z)
  rw [(hev _).1 _ ψ _ _ hz]
  let s : (P j).R e := algebraMap c.F _ κ' * evR Xo c f ((P j).y e he)
  have hs : ψ s = io κ' * ψ (evR Xo c f ((P j).y e he)) := by
    simp only [s, map_mul, AlgHom.commutes]; rfl
  rw [← hs]
  refine inV_of_mem_B (P j) ψ.toRingHom (fun k => ψ.commutes k) hO
    (fun g hg => (hW _).1 (hgW g hg)) s ?_
  have hyg : evR Xo c f (P j).yg = ((P j).R e).val (evR Xo c f ((P j).y e he)) :=
    (hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)
  obtain ⟨d, hd'⟩ : κ j ∣ ∏ i, κ i := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have e1 : ((s : (P j).R e) : (P j).Ω) = algebraMap c.F (P j).Ω (algebraMap _ c.F d) *
      (algebraMap c.F (P j).Ω (algebraMap _ c.F (κ j)) * evR Xo c f (P j).yg) := by
    rw [hyg]
    simp only [s, hκ', hd', map_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_val]
    ring
  rw [e1]
  exact mul_mem (Subring.subset_closure (Or.inl ⟨d, rfl⟩)) (hκ j)

end GlobalTheory.CuspBound
