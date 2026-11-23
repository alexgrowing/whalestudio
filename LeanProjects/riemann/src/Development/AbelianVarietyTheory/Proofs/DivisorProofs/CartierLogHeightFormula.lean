import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNeg
open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry
open IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CovolFin

theorem log_valAt_prod {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (w : AbsoluteValue K ℝ)
    {ι : Type} (s : Finset ι) (u : ι → Z.functionFieldˣ) (hu : ∀ i ∈ s, UnitAt (below y) (u i : Z.functionField)) :
    UnitAt (below y) ((∏ i ∈ s, u i : Z.functionFieldˣ) : Z.functionField) ∧
      Real.log (w (valAt y ((∏ i ∈ s, u i : Z.functionFieldˣ) : Z.functionField))) =
        ∑ i ∈ s, Real.log (w (valAt y (u i : Z.functionField))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h₁ : valAt y (1 : Z.functionField) = 1 := by simpa using Base.valAt_stalk y 1
    simp [h₁, unitAt_one]
  | insert a s ha ih =>
    obtain ⟨U, e⟩ := ih fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have Ua := hu a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Units.val_mul]
    refine ⟨Ua.mul U, ?_⟩
    rw [SmallSec.valAt_mul Ua.regAt U.regAt, map_mul,
      Real.log_mul (w.pos (SmallSec.valAt_ne_zero Ua)).ne' (w.pos (SmallSec.valAt_ne_zero U)).ne', e]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem zpow_finsum {G : Type} [CommGroup G] (a : G) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

variable (Dw) in

theorem expo_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) :
    expo Dw (∑ i ∈ s, ρ i) = ∑ i ∈ s, expo Dw (ρ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LineTest.expo_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LineTest.expo_add, ih]

theorem sum_neg_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) (K : Sym E → ℝ) :
    ((-∑ i ∈ s, ρ i).sum fun a n => (n : ℝ) * K a) = -∑ i ∈ s, (ρ i).sum fun a n => (n : ℝ) * K a := by
  classical
  rw [Finsupp.sum_neg_index (fun _ => by simp)]
  simp only [Int.cast_neg, neg_mul]
  rw [Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  simp [Finsupp.sum, Finset.sum_neg_distrib]

open Classical in

theorem lgOf_neg_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v)
    (y : AlgPt Y.Y) :
    lgOf Y (-∑ i ∈ s, ρ i) v ε y = Real.log (ε.w (valAt y.1
      (((eqn (divOf Y (expo Dw (-∑ i ∈ s, ρ i))) (below y.1))⁻¹ *
        ∏ i ∈ s, (eqn (divOf Y (expo Dw (ρ i))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) -
      ∑ i ∈ s, lgOf Y (ρ i) v ε y := by
  have hp := LineTest.residueCharacteristic_prime v
  have UW := GlobalTheory.CombInd.Tens.unitAt_prod Y (-∑ i ∈ s, ρ i) (below y.1)
  have Ui := fun i => GlobalTheory.CombInd.Tens.unitAt_prod Y (ρ i) (below y.1)
  simp only [lgOf, dif_pos hp]
  rw [sum_neg_sum]
  set b := below y.1 with hb
  set t := (Y.gr_spec b).choose_spec.choose_spec.choose with ht
  have hP : (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (-∑ i ∈ s, ρ i) x) =
      (∏ i ∈ s, ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x)⁻¹ := by
    rw [GlobalTheory.CombInd.DualComb.expo_neg, expo_sum, Finset.prod_comm, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Pi.neg_apply, Finset.sum_apply, zpow_neg, zpow_finsum]
  have hprod : ((eqn (divOf Y (expo Dw (-∑ i ∈ s, ρ i))) b)⁻¹ * ∏ i ∈ s, (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹ : Y.Y.Fnˣ) =
      ((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (-∑ i ∈ s, ρ i) x) * (eqn (divOf Y (expo Dw (-∑ i ∈ s, ρ i))) b)⁻¹) *
        ∏ i ∈ s, ((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x) * (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹) := by
    rw [hP, Finset.prod_mul_distrib, mul_mul_mul_comm, inv_mul_cancel, one_mul]
  obtain ⟨Us, hs⟩ := GlobalTheory.CovolFin.log_valAt_prod y.1 ε.w s
    (fun i => (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x) * (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹) fun i _ => Ui i
  rw [hprod, Units.val_mul _ (∏ i ∈ s, _), SmallSec.valAt_mul UW.regAt Us.regAt, map_mul,
    Real.log_mul (ε.w.pos (SmallSec.valAt_ne_zero UW)).ne' (ε.w.pos (SmallSec.valAt_ne_zero Us)).ne', hs,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Units.val_mul]
  ring

end Free

theorem detOmSym_eq (E : Type) [Field E] (g : ℕ) :
    detOmSym E g = -∑ k : Fin g, Finsupp.single (ArIn.ind ∅, (none : Option ℝ), (Sum.inr (k : ℕ) : ((E →+* ℂ) × ℕ) ⊕ ℕ)) 1 := by
  have hind : ArIn.ind ∅ = fun _ => false := funext fun q => by simp [ArIn.ind]
  rw [hind, ← Finset.sum_neg_distrib]
  unfold detOmSym
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_
  simp [wholeSym, Finsupp.single_neg]

theorem lg_detOmSym : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (e : GlobalTheory.TrueGeo.Ext v) (y : AlgPt (O.var c)), (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).lg v e y = Real.log (e.w (valAt y.1 (genAt (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).D (below y.1) / ∏ k : Fin (D.R.f * O.N), genAt (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).D (below y.1) ^ (-1 : ℤ)))) - ∑ k : Fin (D.R.f * O.N), (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).lg v e y := by
  intro D O c v e y
  rw [detOmSym_eq]
  refine (lgOf_neg_sum (O.Φ.C c) Finset.univ _ v e y).trans ?_
  congr 3
  simp only [Setup.adl0, adlOf, genAt, Units.val_mul, Units.coe_prod, zpow_neg, zpow_one, div_eq_mul_inv,
    Finset.prod_inv_distrib, inv_inv, Units.val_inv_eq_inv_val]

end GlobalTheory.CovolFin
