import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.ProjectiveLattices.RegularityR2Quotient

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

theorem ramIdx_nonneg_of_isOver {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)} (h : IsOver (K := K) v la) :
    0 ≤ ramIdx v la := by
  have h' := h
  unfold IsOver at h'
  unfold ramIdx
  by_cases hne : {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v (algebraMap K Ω (a : K)) = n}.Nonempty
  · apply le_csInf hne
    rintro n ⟨a, ha, -, hv⟩
    have h0 := (h' a).2 ha
    rw [hv] at h0
    exact_mod_cast h0.le
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Int.csInf_empty]

theorem int_nonneg_of_ereal_eq {x e : ℤ} {w : EReal} (he : 0 ≤ e) (hw : 0 ≤ w)
    (h : (((x : ℤ) : ℝ) : EReal) = (((e : ℤ) : ℝ) : EReal) * w) : 0 ≤ x := by
  have h1 : (0 : EReal) ≤ (((e : ℤ) : ℝ) : EReal) * w := EReal.mul_nonneg (by exact_mod_cast he) hw
  rw [← h] at h1
  have h2 : (0 : ℝ) ≤ ((x : ℤ) : ℝ) := by exact_mod_cast h1
  exact_mod_cast h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem vAtV_mem_valSet {cls cls' : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop}
    (hc : ∀ T io y, cls T io y → cls' T io y) {PY : Type}
    {lies : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) :
    vAtV y ∈ valSet Xo c cls' la := by
  unfold vAtV valSet
  refine ⟨⟨((y.1).1, ()), ?_⟩, rfl⟩
  obtain ⟨T, io, e, hO, y1, hcl, eta, -, hy⟩ := y.2
  refine ⟨T, io, e, hO, y1, hc T io y1 hcl, (), trivial, ?_⟩
  rw [hy]
  rfl

theorem vV_of_trivCls {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (h : trivCls Xo c T io y)
    (a : c.F) (ha : a ≠ 0) : vV T.V (io a) = 0 := by
  unfold trivCls at h
  unfold vV
  obtain ⟨u, hu⟩ := h a ha
  rw [← hu]
  unfold valV
  have hnm : (u : T.V) ∉ (IsDiscreteValuationRing.maximalIdeal T.V).asIdeal := by
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm u.isUnit
  have hu1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr u) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    first
      | exact le_antisymm (HeightOneSpectrum.intValuation_le_one _ _)
          (not_lt.mp fun hlt => hnm ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).mp hlt))
      | exact (HeightOneSpectrum.intValuation_eq_one_iff_not_mem _ _).mpr hnm
      | exact le_antisymm (HeightOneSpectrum.intValuation_le_one _ _)
          (not_lt.mp fun hlt => hnm ((HeightOneSpectrum.intValuation_lt_one_iff_dvd _ _).mp hlt))
      | simp [HeightOneSpectrum.intValuation_def, Ideal.span_singleton_eq_top.mpr u.isUnit]
  rw [hu1]
  simp

theorem valC_add (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f g : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (f + g) Z = valC h a n f Z + valC h a n g Z := by
  simp only [valC, evC, evR]
  rw [evalAt_add, AddMonoidAlgebra.single_add]

theorem valC_zero (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Z : Comp Xo c) :
    valC h a n 0 Z = 0 := by
  simp only [valC, evC, evR]
  rw [evalAt_zero, AddMonoidAlgebra.single_zero]

theorem valC_smul_ct (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : c.F) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (t • f) Z = algebraMap c.F (AC Z) t * valC h a n f Z := by
  simp only [valC, evC, evR]
  rw [evalAt_smul, ← Algebra.smul_def, ← Algebra.smul_def, AddMonoidAlgebra.smul_single]

theorem evC_ne_zero_of_valC {h : GenFrEx Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} {Z : Comp Xo c}
    (hf : valC h a n f Z ≠ 0) : evC h Z f ≠ 0 := by
  intro h0
  apply hf
  unfold valC
  rw [h0, AddMonoidAlgebra.single_zero]

end Formalism.L2.Pj
