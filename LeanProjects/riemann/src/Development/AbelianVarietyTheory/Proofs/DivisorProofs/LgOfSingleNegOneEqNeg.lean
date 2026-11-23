import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

namespace GradedLogInvariants
section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GradedInv

section Var

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isEqn_sum {ι : Type} (s : Finset ι) (D : ι → Y.Dv) (g : ι → Y.Fnˣ) (x : Y.X)
    (h : ∀ i ∈ s, (D i).IsEqn x (g i)) : (∑ i ∈ s, D i).IsEqn x (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CartierDiv.isEqn_zero x
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem unitAt_genAt_mul (D D' : Y.Dv) (hD : D' = -D) (x : Y.X) : UnitAt x (genAt D' x * genAt D x) := by
  have h1 : D'.IsEqn x (eqn D x)⁻¹ := hD ▸ (Base.isEqn_eqn D x).neg
  have h2 := (Base.isEqn_eqn D' x).iff_unitAt.1 h1
  convert h2 using 1
  simp only [genAt, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  ring

theorem log_val_inv (D D' : Y.Dv) (hD : D' = -D) (y : AlgPt Y) (T : Y.Fnˣ) (hT : D.IsEqn (below y.1) T)
    {v : HeightOneSpectrum (𝓞 F)} (ε : TrueGeo.Ext v) :
    Real.log (ε.w (valAt y.1 ((T⁻¹ * (eqn D' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn))) =
      -Real.log (ε.w (valAt y.1 ((T * (eqn D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn))) +
        Real.log (ε.w (valAt y.1 (genAt D' (below y.1) * genAt D (below y.1)))) := by
  have hG := unitAt_genAt_mul D D' hD (below y.1)
  have hU : UnitAt (below y.1) ((T * (eqn D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn) := by
    have h := (Base.isEqn_eqn D (below y.1)).iff_unitAt.1 hT
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv] using h
  have e : ((T⁻¹ * (eqn D' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn) =
      (genAt D' (below y.1) * genAt D (below y.1)) * ((T * (eqn D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn)⁻¹ := by
    have h0 : ((eqn D (below y.1) : Y.Fnˣ) : Y.Fn) ≠ 0 := Units.ne_zero _
    have h1 : ((eqn D' (below y.1) : Y.Fnˣ) : Y.Fn) ≠ 0 := Units.ne_zero _
    have h2 : ((T : Y.Fnˣ) : Y.Fn) ≠ 0 := Units.ne_zero _
    simp only [genAt, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have n1 : ε.w (valAt y.1 (genAt D' (below y.1) * genAt D (below y.1))) ≠ 0 :=
    (AbsoluteValue.ne_zero_iff ε.w).2 (SmallSec.valAt_ne_zero hG)
  have n2 : ε.w (valAt y.1 ((T * (eqn D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn)) ≠ 0 :=
    (AbsoluteValue.ne_zero_iff ε.w).2 (SmallSec.valAt_ne_zero hU)
  rw [e, SmallSec.valAt_mul hG.regAt hU.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv hU, map_mul, map_inv₀,
    Real.log_mul n1 (inv_ne_zero n2), Real.log_inv]
  ring

end Var

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem divOf_neg (n : Letter Dw → ℤ) : divOf Y (-n) = -divOf Y n := by
  simp [divOf, neg_smul, Finset.sum_neg_distrib]

theorem expo_single_neg_one (a : Sym E) :
    expo Dw (Finsupp.single a (-1)) = -expo Dw (Finsupp.single a 1) := by
  funext x
  simp only [expo_single, Pi.neg_apply]
  split_ifs <;> simp

theorem isEqn_prod (x : Y.Y.X) (n : Letter Dw → ℤ) :
    (divOf Y n).IsEqn x (∏ z : Letter Dw, (Y.gr_spec x).choose_spec.choose_spec.choose z.1 z.2 ^ n z) :=
  isEqn_sum _ _ _ x fun z _ =>
    ((Y.gr_spec x).choose_spec.choose_spec.choose_spec.2 z.1 z.2).zsmul (n z)

theorem exists_lgOf_eq_val (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    ∃ (κ : ℝ) (S : Sym E → ℝ), ∀ w : Sym E →₀ ℤ, lgOf Y w v ε y =
      Real.log (ε.w (valAt y.1 (((∏ z : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw w z) *
          (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) + κ * w.sum fun a n => (n : ℝ) * S a :=
  ⟨_, _, fun _ => dif_pos (residueCharacteristic_prime v)⟩

theorem exists_lgOf_single (a : Sym E) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    ∃ S : ℝ, ∀ n : ℤ, lgOf Y (Finsupp.single a n) v ε y =
      Real.log (ε.w (valAt y.1 (((∏ z : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw (Finsupp.single a n) z) *
          (eqn (divOf Y (expo Dw (Finsupp.single a n))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) + n * S := by
  obtain ⟨κ, S, h⟩ := exists_lgOf_eq_val Y v ε y
  refine ⟨κ * S a, fun n => ?_⟩
  rw [h, Finsupp.sum_single_index (by simp)]
  ring

theorem lgOf_single_neg_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (a : Sym E) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y), lgOf Y (Finsupp.single a (-1)) v ε y = -lgOf Y (Finsupp.single a 1) v ε y + Real.log (ε.w (valAt y.1 (genAt (divOf Y (expo Dw (Finsupp.single a (-1)))) (below y.1) * genAt (divOf Y (expo Dw (Finsupp.single a 1))) (below y.1)))) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y a v ε y
  obtain ⟨S, hS⟩ := exists_lgOf_single Y a v ε y
  have hex := expo_single_neg_one (Dw := Dw) a
  have hD : divOf Y (expo Dw (Finsupp.single a (-1))) = -divOf Y (expo Dw (Finsupp.single a 1)) := by
    rw [hex, divOf_neg]
  have hT := isEqn_prod Y (below y.1) (expo Dw (Finsupp.single a 1))
  have key := log_val_inv _ _ hD y _ hT ε
  have hinv : (∏ z : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^
      expo Dw (Finsupp.single a (-1)) z) = (∏ z : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^
      expo Dw (Finsupp.single a 1) z)⁻¹ := by
    rw [hex, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [Pi.neg_apply, zpow_neg]
  rw [hS (-1), hS 1, hinv, key]
  push_cast
  ring

end Flag

end GlobalTheory.CompanionTheory.GradedInv

end

end GradedLogInvariants
section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

theorem _root_.GlobalTheory.Adopt.lgOf_single_neg_one_eq_neg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (a : Sym E) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y), lgOf Y (Finsupp.single a (-1)) v ε y = -lgOf Y (Finsupp.single a 1) v ε y + Real.log (ε.w (valAt y.1 (genAt (divOf Y (expo Dw (Finsupp.single a (-1)))) (below y.1) * genAt (divOf Y (expo Dw (Finsupp.single a 1))) (below y.1)))) := by
  first | exact @GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.lgOf_single_neg_one | exact GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.lgOf_single_neg_one | (intros; apply GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.lgOf_single_neg_one <;> assumption)

end
