import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqnRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightOfInducedBundle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetsOfParOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory AlgebraicGeometry IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Classical GlobalTheory.HtAdd

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HtAdd.SumLines

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem expo_single_eq (a : Sym E) (k : ℤ) : expo Dw (Finsupp.single a k) = k • expo Dw (Finsupp.single a 1) := by
  funext z
  simp only [Pi.smul_apply, LineTest.expo_single, smul_eq_mul]
  split_ifs <;> simp

theorem expo_sum_single {ι : Type} (s : Finset ι) (a : ι → Sym E) (n : ι → ℤ) :
    expo Dw (∑ i ∈ s, Finsupp.single (a i) (n i)) = ∑ i ∈ s, n i • expo Dw (Finsupp.single (a i) 1) := by
  induction s using Finset.induction_on with
  | empty => simp [LineTest.expo_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, LineTest.expo_add, ih, expo_single_eq]

theorem prod_zpow_sum {G ι κ : Type} [CommGroup G] [Fintype κ] (T : κ → G) (s : Finset ι) (n : ι → ℤ)
    (ex : ι → κ → ℤ) : ∏ z, T z ^ (∑ i ∈ s, n i • ex i) z = ∏ i ∈ s, (∏ z, T z ^ ex i z) ^ n i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, ← ih, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [Pi.add_apply, zpow_add, Pi.smul_apply, smul_eq_mul, mul_comm (n j), zpow_mul]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem divOf_sum_zsmul {ι : Type} (s : Finset ι) (n : ι → ℤ) (ex : ι → Letter Dw → ℤ) :
    divOf Y (∑ i ∈ s, n i • ex i) = ∑ i ∈ s, n i • divOf Y (ex i) := by
  simp only [divOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem isEqn_prod_eqn {ι : Type} (s : Finset ι) (a : ι → Sym E) (n : ι → ℤ) (x : Y.Y.X) :
    (divOf Y (expo Dw (∑ i ∈ s, Finsupp.single (a i) (n i)))).IsEqn x
      (∏ i ∈ s, eqn (divOf Y (expo Dw (Finsupp.single (a i) 1))) x ^ n i) := by
  rw [expo_sum_single, divOf_sum_zsmul]
  induction s using Finset.induction_on with
  | empty => simpa using CartierDiv.isEqn_zero x
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact ((Base.isEqn_eqn _ x).zsmul _).add ih

theorem unitAt_eqnRatio {ι : Type} (s : Finset ι) (a : ι → Sym E) (n : ι → ℤ) (x : Y.Y.X) :
    UnitAt x (eqnRatio Y s a n x : Y.Y.Fn) := by
  have := (Base.isEqn_eqn _ x).iff_unitAt.1 (isEqn_prod_eqn Y s a n x)
  rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this

end Free

section Val

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (w : AbsoluteValue K ℝ) (y : Sp K ⟶ X)

theorem valAt_mul_of_unitAt {f g : X.functionField} (hf : UnitAt (below y) f) (hg : UnitAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, -, rfl⟩ := hf
  obtain ⟨b, -, rfl⟩ := hg
  rw [← map_mul, Base.valAt_stalk, Base.valAt_stalk, Base.valAt_stalk, map_mul]

theorem log_valAt_mul {f g : X.functionField} (hf : UnitAt (below y) f) (hg : UnitAt (below y) g) :
    Real.log (w (valAt y (f * g))) = Real.log (w (valAt y f)) + Real.log (w (valAt y g)) := by
  rw [valAt_mul_of_unitAt y hf hg, map_mul,
    Real.log_mul (w.pos (Base.valAt_zpow y hf).1).ne' (w.pos (Base.valAt_zpow y hg).1).ne']

theorem log_valAt_zpow {f : X.functionField} (hf : UnitAt (below y) f) (k : ℤ) :
    Real.log (w (valAt y (f ^ k))) = k * Real.log (w (valAt y f)) := by
  rw [(Base.valAt_zpow y hf).2 k, map_zpow₀, Real.log_zpow]

theorem log_valAt_prod {ι : Type} (s : Finset ι) (g : ι → X.functionFieldˣ)
    (hg : ∀ i ∈ s, UnitAt (below y) (g i : X.functionField)) :
    Real.log (w (valAt y ((∏ i ∈ s, g i : X.functionFieldˣ) : X.functionField))) =
      ∑ i ∈ s, Real.log (w (valAt y (g i : X.functionField))) := by
  induction s using Finset.induction_on with
  | empty =>
    have h1 : valAt y (1 : X.functionField) = 1 := by simpa using Base.valAt_stalk y 1
    simp [h1]
  | insert j s hj ih =>
    have hs : UnitAt (below y) ((∏ i ∈ s, g i : X.functionFieldˣ) : X.functionField) :=
      (unitsAt (below y)).prod_mem fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert hj, Units.val_mul, log_valAt_mul w y (hg j (Finset.mem_insert_self j s)) hs,
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi), Finset.sum_insert hj]

end Val

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem frame_quot_eq {ι : Type} (s : Finset ι) (a : ι → Sym E) (n : ι → ℤ) (x : Y.Y.X)
    (T : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) :
    (∏ z : Letter Dw, T z.1 z.2 ^ expo Dw (∑ i ∈ s, Finsupp.single (a i) (n i)) z) *
        (eqn (divOf Y (expo Dw (∑ i ∈ s, Finsupp.single (a i) (n i)))) x)⁻¹ =
      (∏ i ∈ s, ((∏ z : Letter Dw, T z.1 z.2 ^ expo Dw (Finsupp.single (a i) 1) z) *
        (eqn (divOf Y (expo Dw (Finsupp.single (a i) 1))) x)⁻¹) ^ n i) * eqnRatio Y s a n x := by
  have hP : (∏ z : Letter Dw, T z.1 z.2 ^ expo Dw (∑ i ∈ s, Finsupp.single (a i) (n i)) z) =
      ∏ i ∈ s, (∏ z : Letter Dw, T z.1 z.2 ^ expo Dw (Finsupp.single (a i) 1) z) ^ n i := by
    rw [expo_sum_single]
    exact prod_zpow_sum (fun z : Letter Dw => T z.1 z.2) s n _
  rw [hP, eqnRatio]
  simp only [mul_zpow, Finset.prod_mul_distrib, inv_zpow', Finset.prod_inv_distrib, zpow_neg]
  group

theorem lgOf_sum_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {ι : Type} (s : Finset ι) (a : ι → Sym E)
    (n : ι → ℤ) (x : Y.Y.X), UnitAt x (eqnRatio Y s a n x : Y.Y.Fn) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y), below y.1 = x →
      lgOf Y (∑ i ∈ s, Finsupp.single (a i) (n i)) v ε y =
        ∑ i ∈ s, (n i : ℝ) * lgOf Y (Finsupp.single (a i) 1) v ε y +
          Real.log (ε.w (valAt y.1 (eqnRatio Y s a n x : Y.Y.Fn))) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y ι s a n x
  refine ⟨unitAt_eqnRatio Y s a n x, fun v ε y hx => ?_⟩
  subst hx
  have hR := unitAt_eqnRatio Y s a n (below y.1)
  have hU (w : Sym E →₀ ℤ) : UnitAt (below y.1)
      (((∏ z : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw w z) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := (Base.isEqn_eqn (divOf Y (expo Dw w)) (below y.1)).iff_unitAt.1
      (LineTest.isEqn_divOf Y (expo Dw w) (below y.1))
    rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
  have hprod : UnitAt (below y.1) ((∏ i ∈ s, ((∏ z : Letter Dw,
      (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw (Finsupp.single (a i) 1) z) *
        (eqn (divOf Y (expo Dw (Finsupp.single (a i) 1))) (below y.1))⁻¹) ^ n i : Y.Y.Fnˣ) : Y.Y.Fn) :=
    (unitsAt (below y.1)).prod_mem fun i _ => (unitsAt (below y.1)).zpow_mem (hU _) _
  simp only [lgOf, dif_pos (LineTest.residueCharacteristic_prime v)]
  rw [frame_quot_eq Y s a n (below y.1), Units.val_mul, log_valAt_mul _ _ hprod hR,
    log_valAt_prod _ _ _ _ fun i _ => (unitsAt (below y.1)).zpow_mem (hU _) _,
    ← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  simp only [Finsupp.sum_single_index, Int.cast_zero, zero_mul, Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl fun i _ => by rw [Units.val_zpow_eq_zpow_val, log_valAt_zpow _ _ (hU _)]]
  rw [Finset.mul_sum]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [add_right_comm]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

end Main

end GlobalTheory.HtAdd.SumLines
