import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree

noncomputable section

namespace GlobalTheory.TrivialValuationTest

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Ring

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

theorem vV_unit (u : Vˣ) : vV V (algebraMap V F (u : V)) = 0 := by
  have h : valV V (algebraMap V F (u : V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm u.isUnit
  simp [vV, h]

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem vV_eq_zero_of_triv {T : CDVR} {ι : c.F →+* T.Fr} {y : IntFr Xo c T ι} (h : trivCls Xo c T ι y)
    {a : c.F} (ha : a ≠ 0) : vV T.V (ι a) = 0 := by
  obtain ⟨u, hu⟩ := h a ha
  rw [← hu]; exact vV_unit u

theorem not_overLa_of_triv {T : CDVR} {ι : c.F →+* T.Fr} {y : IntFr Xo c T ι} (h : trivCls Xo c T ι y)
    (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ) : ¬ OverLa la T.V ι e := by
  rintro ⟨he, hv⟩
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer c.F
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ; exact absurd hπ.symm WithZero.exp_ne_zero
  have h1 := hv π
  rw [vV_eq_zero_of_triv h hπ0, vLa, hπ] at h1
  simp at h1
  omega

theorem ordQ_smul (q : QPt Xo c) {a : c.F} (ha : a ≠ 0) (f : Rul Xo c) :
    ordQ Xo c q (a • f) = ordQ Xo c q f := by
  unfold ordQ
  rw [evI_smul]
  exact nval_mul_unit 1 ((map_ne_zero q.ι).2 ha) (vV_eq_zero_of_triv q.triv ha) _

theorem ord_nonneg_of_bddBelow {C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)} (h : RegularityR1Quotient Xo c C)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ C a n) (la : HeightOneSpectrum (𝓞 c.F)) (N : ℕ)
    (hb : ∀ v ∈ valSet Xo c (algCls Xo c) la, ((-(N : ℝ) : ℝ) : EReal) ≤ v f) (q : QPt Xo c) :
    0 ≤ ordQ Xo c q f := by
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer c.F
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ; exact absurd hπ.symm WithZero.exp_ne_zero
  have hN : vLa la (π ^ N) = N := by
    simp [vLa, map_pow, hπ, ← WithZero.exp_nsmul]
  rw [← ordQ_smul q (pow_ne_zero N hπ0) f]
  refine h a n _ ((C a n).smul_mem _ hf) ⟨la, fun v hv => ?_⟩ q
  rw [(isVal_valSet la v hv).smul _ _ (pow_ne_zero N hπ0), hN]
  calc (0 : EReal) = ((((N : ℤ) : ℝ)) : EReal) + ((-(N : ℝ) : ℝ) : EReal) := by
        rw [← EReal.coe_add]; simp
    _ ≤ _ := add_le_add le_rfl (hb v hv)

theorem ord_eq_top_of_no_point {C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)} (h : RegularityR2Quotient Xo c C)
    (la : HeightOneSpectrum (𝓞 c.F)) (h0 : valSet Xo c (algCls Xo c) la = ∅)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ C a n) (q : QPt Xo c) : ordQ Xo c q f = ⊤ := by
  by_contra hne
  have := (h a n a n 0 Fin.elim0 f 0 le_rfl (fun i => i.elim0) hf ⟨la, 0, by simp [h0]⟩ q).2 hne
  rw [iInf_of_empty] at this
  simp at this

theorem premise_fails_of_empty (hne : IntFrNe Xo c (algCls Xo c)) (ws : Fin 0 → Rul Xo c)
    (la : HeightOneSpectrum (𝓞 c.F)) : ¬ ∀ v ∈ valSet Xo c (algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤ := by
  intro h
  obtain ⟨T, io, e, ho, y, hy⟩ := hne la
  obtain ⟨i, -⟩ := h _ ⟨PtV.mk la ho y hy () trivial, rfl⟩
  exact i.elim0

theorem powerSeries_const_unit (K : Type) [Field K] (a : K) (ha : a ≠ 0) :
    ∃ u : (PowerSeries K)ˣ, algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u =
      ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp PowerSeries.C) a :=
  ⟨Units.map (PowerSeries.C : K →+* PowerSeries K).toMonoidHom (Units.mk0 a ha), rfl⟩

def powerSeriesCDVR (K : Type) [Field K] [CharZero K] : CDVR where
  V := PowerSeries K
  cpl := by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  ch0 := algebraRat.charZero _

theorem trivCls_powerSeries
    (y : IntFr Xo c (powerSeriesCDVR c.F)
      ((algebraMap (PowerSeries c.F) (FractionRing (PowerSeries c.F))).comp PowerSeries.C)) :
    trivCls Xo c _ _ y := fun a ha => powerSeries_const_unit c.F a ha

theorem regularity_first_clause_bot : RegularityR1Quotient Xo c (fun _ _ => ⊥) := by
  intro a n f hf _ q
  rw [(Submodule.mem_bot c.F).1 hf, ordQ, (isEval_evI q.y).zero (), nval_zero]
  exact le_top

end GlobalTheory.TrivialValuationTest
