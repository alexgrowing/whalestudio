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
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory AlgebraicGeometry IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Classical GlobalTheory.HtAdd

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtAddCx

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : FlagCpt Z e} {σ : F →+* ℂ} (G : EigMet Z (embOf e σ))
  {p : Y.Y.pts σ}

theorem h_pos {n : Letter Dw → ℤ} {a : Y.Y.Fnˣ} (h : p ∈ Var.eqnSet σ (divOf Y n) a) : 0 < (Y.met G n).h a p :=
  (Var.Met.mem_posSet_iff h).1 (FlagCpt.posSet_met G n ▸ Set.mem_univ p)

theorem mem_add {n n' : Letter Dw → ℤ} {a a' : Y.Y.Fnˣ} (h : p ∈ Var.eqnSet σ (divOf Y n) a)
    (h' : p ∈ Var.eqnSet σ (divOf Y n') a') : p ∈ Var.eqnSet σ (divOf Y (n + n')) (a * a') := by
  rw [FlagCpt.divOf_add]
  exact CartierDiv.IsEqn.add h h'

theorem mem_zsmul {n : Letter Dw → ℤ} {a : Y.Y.Fnˣ} (h : p ∈ Var.eqnSet σ (divOf Y n) a) (k : ℤ) :
    p ∈ Var.eqnSet σ (divOf Y (k • n)) (a ^ k) := by
  have e : divOf Y (k • n) = k • divOf Y n := by
    simp only [divOf, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  rw [e]
  exact CartierDiv.IsEqn.zsmul h k

theorem log_add {n n' : Letter Dw → ℤ} {a a' : Y.Y.Fnˣ} (h : p ∈ Var.eqnSet σ (divOf Y n) a)
    (h' : p ∈ Var.eqnSet σ (divOf Y n') a') :
    Real.log ((Y.met G (n + n')).h (a * a') p) = Real.log ((Y.met G n).h a p) + Real.log ((Y.met G n').h a' p) := by
  rw [FlagCpt.met_add_h G n n' h h', Real.log_mul (h_pos G h).ne' (h_pos G h').ne']

theorem log_zero : Real.log ((Y.met G 0).h 1 p) = 0 := by
  have e₃ : Var.val p (1 : Y.Y.FnC σ) = 1 := Var.hasVal_one.val_eq
  simp [FlagCpt.met, FlagCpt.genSq, prodPow, Var.tv, e₃]

theorem log_zsmul {n : Letter Dw → ℤ} {a : Y.Y.Fnˣ} (h : p ∈ Var.eqnSet σ (divOf Y n) a) (k : ℤ) :
    Real.log ((Y.met G (k • n)).h (a ^ k) p) = k * Real.log ((Y.met G n).h a p) := by
  have step (j : ℤ) : Real.log ((Y.met G ((j + 1) • n)).h (a ^ (j + 1)) p) =
      Real.log ((Y.met G (j • n)).h (a ^ j) p) + Real.log ((Y.met G n).h a p) := by
    rw [add_smul, one_smul, zpow_add_one]
    exact log_add G (mem_zsmul h j) h
  induction k using Int.induction_on with
  | zero => rw [zero_smul, zpow_zero, log_zero]; simp
  | succ k ih => rw [step, ih]; push_cast; ring
  | pred k ih =>
    have := step (-(k : ℤ) - 1)
    rw [sub_add_cancel, ih] at this
    push_cast at this ⊢
    linarith

theorem log_sum {ι : Type} (s : Finset ι) (m : ι → Letter Dw → ℤ) (a : ι → Y.Y.Fnˣ) (k : ι → ℤ)
    (h : ∀ i, p ∈ Var.eqnSet σ (divOf Y (m i)) (a i)) :
    p ∈ Var.eqnSet σ (divOf Y (∑ i ∈ s, k i • m i)) (∏ i ∈ s, a i ^ k i) ∧
      Real.log ((Y.met G (∑ i ∈ s, k i • m i)).h (∏ i ∈ s, a i ^ k i) p) =
        ∑ i ∈ s, (k i : ℝ) * Real.log ((Y.met G (m i)).h (a i) p) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty, Finset.sum_empty]
    refine ⟨?_, log_zero G⟩
    have e : divOf Y 0 = 0 := by simp [divOf]
    rw [e]
    exact CartierDiv.isEqn_zero _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    exact ⟨mem_add (mem_zsmul (h j) _) ih.1, by rw [log_add G (mem_zsmul (h j) _) ih.1, ih.2, log_zsmul G (h j)]⟩

theorem log_comb {ι : Type} (s : Finset ι) (m : ι → Letter Dw → ℤ) (a : ι → Y.Y.Fnˣ) (k : ι → ℤ)
    (h : ∀ i, p ∈ Var.eqnSet σ (divOf Y (m i)) (a i)) {n : Letter Dw → ℤ} (hn : n = ∑ i ∈ s, k i • m i) {b : Y.Y.Fnˣ}
    (hb : p ∈ Var.eqnSet σ (divOf Y n) b) :
    Real.log ((Y.met G n).h b p) / 2 = ∑ i ∈ s, (k i : ℝ) * (Real.log ((Y.met G (m i)).h (a i) p) / 2) +
      Real.log ‖ratVal (((∏ i ∈ s, a i ^ k i) * b⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) p‖ := by
  subst hn
  obtain ⟨h1, h2⟩ := log_sum G s m a k h
  have h3 := Var.tv_ne_zero hb h1
  have e : ratVal (((∏ i ∈ s, a i ^ k i) * b⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) p = Var.tv b (∏ i ∈ s, a i ^ k i) p := by
    rw [Var.tv, Var.val_cx, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  rw [e, (Y.met G _).trans _ _ p hb h1, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 h3)) (h_pos G h1).ne', h2,
    Real.log_pow]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  push_cast
  ring

variable (Dw) in

theorem expo_comb {ι : Type} (s : Finset ι) (a : ι → Sym E) (n : ι → ℤ) :
    expo Dw (∑ i ∈ s, Finsupp.single (a i) (n i)) = ∑ i ∈ s, n i • expo Dw (Finsupp.single (a i) 1) := by
  funext x
  rw [Finset.sum_apply]
  unfold expo
  rw [← Finsupp.sum_finset_sum_index]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
    split_ifs <;> simp
  · intro a; simp
  · intro a b₁ b₂; split_ifs <;> simp

theorem parOf_none {w : Sym E →₀ ℤ} (hw : ∀ b ∈ w.support, b.2.1 = none) : parOf w = none := by
  unfold parOf
  split_ifs with h
  exacts [hw _ h.choose_spec, rfl]

theorem parOf_comb {ι : Type} (s : Finset ι) (a : ι → Sym E) (n : ι → ℤ) (h : ∀ i ∈ s, (a i).2.1 = none) :
    parOf (∑ i ∈ s, Finsupp.single (a i) (n i)) = none := parOf_none fun b hb => by
  obtain ⟨i, hi, hb⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hb)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]
  exact h i hi

end Free

theorem log_pn_comb : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) {ι : Type} (s : Finset ι) (a : ι → Sym D.host.E)
    (n : ι → ℤ), (∀ i ∈ s, (a i).2.1 = none) → ∀ (x : (O.var c).X) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ),
    under z = x →
    Real.log ((cxSt D.what₂.LL).pn (O.var c) σ _ ((adlOf (O.Φ.C c) (O.met.hm c) (∑ i ∈ s, Finsupp.single (a i) (n i))).m σ)
        ((cxSt D.what₂.LL).cx (O.var c) σ
          ((eqn (adlOf (O.Φ.C c) (O.met.hm c) (∑ i ∈ s, Finsupp.single (a i) (n i))).D x)⁻¹ : (O.var c).Fnˣ)) z) / 2 =
      ∑ i ∈ s, (n i : ℝ) * (Real.log ((cxSt D.what₂.LL).pn (O.var c) σ _
          ((adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (a i) 1)).m σ)
          ((cxSt D.what₂.LL).cx (O.var c) σ
            ((eqn (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (a i) 1)).D x)⁻¹ : (O.var c).Fnˣ)) z) / 2) +
        Real.log ‖ratVal (eqnRatio (O.Φ.C c) s a n x : (O.var c).Fn) z‖ := by
  intro D O hO c ι s a n ha x σ z hz
  obtain ⟨xa, P, h⟩ := hO
  subst hz
  have hm : ∀ w : Sym D.host.E →₀ ℤ, parOf w = none →
      (cxSt D.what₂.LL).pn (O.var c) σ _ ((adlOf (O.Φ.C c) (O.met.hm c) w).m σ)
        ((cxSt D.what₂.LL).cx (O.var c) σ ((eqn (adlOf (O.Φ.C c) (O.met.hm c) w).D (under z))⁻¹ : (O.var c).Fnˣ)) z =
      ((O.Φ.C c).met (xa.eigMetAt (embOf O.κ.e σ) none) (expo O.S.Dw w)).h
        (eqn (divOf (O.Φ.C c) (expo O.S.Dw w)) (under z)) z := fun w hw => by
    rw [h.hm_eq, ← hw]
    exact Var.pn_frame (m := (O.Φ.C c).met (xa.eigMetAt (embOf O.κ.e σ) (parOf w)) (expo O.S.Dw w)) (y := z)
      (Base.isEqn_eqn _ _)
  rw [hm _ (parOf_comb s a n ha)]
  refine (log_comb (Y := O.Φ.C c) (p := z) _ s (fun i => expo O.S.Dw (Finsupp.single (a i) 1)) _ n
    (fun i => Base.isEqn_eqn _ _) (expo_comb _ s a n) (Base.isEqn_eqn _ _)).trans
      (congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_) rfl)
  rw [hm _ (by simpa using parOf_comb {i} a 1 (by simpa using ha i hi))]
  rfl

end GlobalTheory.HtAddCx
