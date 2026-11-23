import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueBoundRamified
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmSecond
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PlacePartEigenLifts
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependent
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RamChartCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts GlobalTheory.PowGerm GlobalTheory.HarmCopies
open Matrix

section Val

variable (T : CDVR) (e : ℕ)

theorem nval_nonneg_of_mem {x : T.Fr} (hx : x ∈ (algebraMap T.V T.Fr).range) : (0 : EReal) ≤ nval T.V e x := by
  obtain ⟨r, rfl⟩ := hx
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, nval_zero]; exact le_top
  rw [nval_of_ne hr]
  have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) r
  have h2 : valV T.V (algebraMap T.V T.Fr r) ≠ 0 := valV_ne_zero hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  have h4 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr r) : ℝ) := by
    have : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by unfold vV; omega
    exact_mod_cast this
  exact_mod_cast div_nonneg h4 (Nat.cast_nonneg e)

theorem le_nval_int_comb {ι : Type} (s : Finset ι) (cf S : ι → T.Fr) (r : EReal)
    (hc : ∀ i, cf i ∈ (algebraMap T.V T.Fr).range) (hS : ∀ i, r ≤ nval T.V e (S i)) :
    r ≤ nval T.V e (∑ i ∈ s, cf i * S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nval_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (le_min ?_ ih) (nval_add e _ _)
    rw [nval_mul]
    calc r = 0 + r := (zero_add r).symm
      _ ≤ _ := add_le_add (nval_nonneg_of_mem T e (hc a)) (hS a)

theorem isIntPS_iff {n d : ℕ} (f : Germ.PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : Germ.PS T.V n d, MvPowerSeries.map (algebraMap T.V T.Fr) g = f := by
  constructor
  · intro h
    choose g hg using h
    exact ⟨g, MvPowerSeries.ext fun m => hg m⟩
  · rintro ⟨g, rfl⟩ m
    exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

theorem isIntPS_boxSer {n d : ℕ} (f : Fin n → Germ.PS T.Fr 1 d) (hf : ∀ b, IsIntPS T (f b)) :
    IsIntPS T (boxSer f) := by
  choose g hg using fun b => (isIntPS_iff T (f b)).1 (hf b)
  refine (isIntPS_iff T _).2 ⟨boxSer g, ?_⟩
  unfold boxSer
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← hg b, MvPowerSeries.rename_map]

end Val

section Values

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def colVal (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Fin n → Germ.PS T.Fr 1 (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  letI := io.toAlgebra
  ∑ mo ∈ P.support, P.coeff mo *
    ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1)

theorem chartVal_boxSer (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Fin n → Germ.PS T.Fr 1 (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : chartVal C k (boxSer f) P = colVal C k f P := by
  letI := io.toAlgebra
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.rename (letterEquiv (E →+* ℂ) Dw.mult n) Q = P :=
    MvPolynomial.rename_surjective _ (letterEquiv _ _ n).surjective P
  unfold chartVal colVal
  rw [nabValN_boxSer T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 (const_eq_zero C.ch.gauge) k n f _ _
    (letterEquiv (E →+* ℂ) Dw.mult n) _ C.ch.uvec _ (fun _ => rfl) (fun _ => rfl),
    GlobalTheory.NabCol.sum_support_rename (letterEquiv (E →+* ℂ) Dw.mult n) (fun mo =>
      ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))]
  refine Finset.sum_congr rfl fun mo _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hc : colM mo b = colOf (Finsupp.mapDomain (letterEquiv (E →+* ℂ) Dw.mult n) mo) b := by
    ext ℓ
    exact (Finsupp.mapDomain_apply (letterEquiv (E →+* ℂ) Dw.mult n).injective mo (ℓ, b)).symm
  rw [hc]

theorem bound_all_iff_bound_prod (C : IntegralChartA3 Xo c T io y) (e k : ℕ) {n : ℕ} (P : MvPolynomial (LtN Dw n) T.Fr)
    (r : EReal) :
    (∀ f : Germ.PS T.Fr n (chD C.ch), IsIntPS T f → r ≤ nval T.V e (chartVal C k f P)) ↔
      ∀ f : Fin n → Germ.PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → r ≤ nval T.V e (colVal C k f P) := by
  letI := io.toAlgebra
  constructor
  · intro h f hf
    rw [← chartVal_boxSer]
    exact h _ (isIntPS_boxSer T f hf)
  · intro h f hf
    obtain ⟨S, hS⟩ := exists_jet P.totalDegree f
    have h1 : chartVal C k f P = ∑ j : S, MvPowerSeries.coeff j.1 f *
        chartVal C k (MvPowerSeries.monomial j.1 1) P := by
      unfold chartVal
      rw [(nabJet T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 k n _ _ _).1 _ _ _ hS,
        (nabJet T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 k n _ _ _).2.1]
    rw [h1]
    refine le_nval_int_comb T e _ _ _ r (fun j => hf j.1) fun j => ?_
    rw [monomial_eq_boxSer, chartVal_boxSer]
    refine h _ fun b => (isIntPS_iff T _).2 ⟨∏ i, MvPowerSeries.X ((0 : Fin 1), i) ^ j.1 (b, i), ?_⟩
    simp only [map_prod, map_pow, MvPowerSeries.map_X]

end Values

section Lifts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def actM (C : IntegralChartA3 Xo c T io y) (a : 𝓞 E) : Matrix (Fin (chD C.ch)) (Fin (chD C.ch)) T.Fr :=
  letI := io.toAlgebra
  dAct T.Fr C.ch.B a

def intLift (C : IntegralChartA3 Xo c T io y) (φ : Lt1 Dw → Fin (chD C.ch) → T.V) (ℓ : Lt1 Dw) : HK C :=
  letI := io.toAlgebra
  (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)

def PairingLifts {π : Type} (e : ℕ) (β : ℝ) (pr : (E →+* ℂ) → π) (s : (E →+* ℂ) → Bool)
    (C : IntegralChartA3 Xo c T io y) (φ : Lt1 Dw → Fin (chD C.ch) → T.V) (ψ : Lt1 Dw → Fin (chD C.ch) → T.Fr) : Prop :=
  letI := io.toAlgebra
  (∀ ℓ i, (((-β : ℝ)) : EReal) ≤ nval T.V e (ψ ℓ i)) ∧
  (∀ ℓ ℓ' : Lt1 Dw, ℓ'.1 ≠ ComplexEmbedding.conjugate ℓ.1 →
    ∑ i, (algebraMap T.V T.Fr (φ ℓ' i) + ψ ℓ' i - (sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ') i) * C.ch.uvec ℓ i = 0) ∧
  OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => pr ℓ.1) (fun ℓ => s ℓ.1) (intLift C φ) (intLift C φ) ∧
  OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => pr ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ)) (intLift C φ) ∧
  OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => pr ℓ.1) (fun ℓ => s ℓ.1) (intLift C φ) (fun ℓ => (0, ψ ℓ))

def NoOwnType (C : IntegralChartA3 Xo c T io y) (ψ : Lt1 Dw → Fin (chD C.ch) → T.Fr) : Prop :=
  ∀ ℓ ℓ' : Lt1 Dw, ℓ.1 = ComplexEmbedding.conjugate ℓ'.1 → ψ ℓ ⬝ᵥ dir C ℓ' = 0

end Lifts

end GlobalTheory.RamChartCmp
