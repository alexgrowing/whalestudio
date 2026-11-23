import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstTan

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

@[simp] theorem fst_dualMapR (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).fst = φ a.fst := by
  simp [dualMapR]

@[simp] theorem snd_dualMapR (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).snd = φ a.snd := by
  simp [dualMapR]

theorem dualMapR_inl (φ : R →+* R') (a : R) : dualMapR φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a) := by
  ext <;> simp

theorem dualMapR_eps (φ : R →+* R') : dualMapR φ DualNumber.eps = DualNumber.eps := by
  ext <;> simp

theorem eq_dualMapR (φ : R →+* R') (ρ : DualNumber R →+* DualNumber R')
    (h : ∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r)) (he : ρ DualNumber.eps = DualNumber.eps) :
    ρ = dualMapR φ := RingHom.ext fun a => by
  have e : a = TrivSqZeroExt.inl a.fst + TrivSqZeroExt.inl a.snd * DualNumber.eps := by ext <;> simp
  rw [e, map_add, map_add, map_mul, map_mul, h, h, he, dualMapR_inl, dualMapR_inl, dualMapR_eps]

theorem isLocalRing_dual (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

end Dual

abbrev idealEps : Ideal (DualNumber ℂ⟦X⟧) :=
  (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧))

theorem isAdicComplete_idealEps : IsAdicComplete idealEps (DualNumber ℂ⟦X⟧) :=
  have : Module.Finite ℂ⟦X⟧ (DualNumber ℂ⟦X⟧) := inferInstanceAs (Module.Finite ℂ⟦X⟧ (ℂ⟦X⟧ × ℂ⟦X⟧))
  isAdicComplete_map_of_finite _ (DualNumber ℂ⟦X⟧)

abbrev constEps : DualNumber ℂ →+* DualNumber ℂ⟦X⟧ := dualMapR (PowerSeries.C (R := ℂ))

section Jet

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def jet (F : V → ℂ) (z : V) : DualNumber ℂ := TrivSqZeroExt.inl (F 0) + TrivSqZeroExt.inr (fderiv ℂ F 0 z)

@[simp] theorem fst_jet (F : V → ℂ) (z : V) : (jet F z).fst = F 0 := by simp [jet]

@[simp] theorem snd_jet (F : V → ℂ) (z : V) : (jet F z).snd = fderiv ℂ F 0 z := by simp [jet]

theorem jet_mul {F G : V → ℂ} (hF : DifferentiableAt ℂ F 0) (hG : DifferentiableAt ℂ G 0) (z : V) :
    jet (fun v => F v * G v) z = jet F z * jet G z := by
  ext
  · simp
  · rw [snd_jet, fderiv_fun_mul hF hG]
    simp [TrivSqZeroExt.snd_mul, _root_.mul_comm]

theorem jet_pow {F : V → ℂ} (hF : DifferentiableAt ℂ F 0) (z : V) (n : ℕ) :
    jet (fun v => F v ^ n) z = jet F z ^ n := by
  induction n with
  | zero => ext <;> simp
  | succ n ih => rw [pow_succ, ← ih, ← jet_mul (hF.fun_pow n) hF]; simp only [pow_succ]

theorem jet_congr {F G : V → ℂ} (h : F =ᶠ[nhds 0] G) (z : V) : jet F z = jet G z := by
  rw [jet, jet, h.eq_of_nhds, h.fderiv_eq]

def IsJet (x : V → ℂ⟦X⟧) (z : V) (y : DualNumber ℂ⟦X⟧) : Prop :=
  (∀ n, DifferentiableAt ℂ (fun v => PowerSeries.coeff n (x v)) 0) ∧ y.fst = x 0 ∧
    ∀ n, PowerSeries.coeff n y.snd = fderiv ℂ (fun v => PowerSeries.coeff n (x v)) 0 z

variable {z : V}

theorem isJet_zero (z : V) : IsJet (fun _ => 0) z 0 := ⟨fun n => by simp, rfl, fun n => by simp⟩

theorem IsJet.add {x x' : V → ℂ⟦X⟧} {y y' : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (h' : IsJet x' z y') :
    IsJet (fun v => x v + x' v) z (y + y') := by
  refine ⟨fun n => ?_, by simp [h.2.1, h'.2.1], fun n => ?_⟩
  · simp only [map_add]
    exact (h.1 n).fun_add (h'.1 n)
  · simp only [map_add, TrivSqZeroExt.snd_add]
    rw [fderiv_fun_add (h.1 n) (h'.1 n), h.2.2, h'.2.2, ContinuousLinearMap.add_apply]

theorem IsJet.sum {K : Type} (s : Finset K) {x : K → V → ℂ⟦X⟧} {y : K → DualNumber ℂ⟦X⟧}
    (h : ∀ i ∈ s, IsJet (x i) z (y i)) : IsJet (fun v => ∑ i ∈ s, x i v) z (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isJet_zero z
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsJet.const_mul {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (r : ℂ⟦X⟧) :
    IsJet (fun v => r * x v) z (TrivSqZeroExt.inl r * y) := by
  refine ⟨fun n => ?_, by simp [h.2.1], fun n => ?_⟩
  · simp only [PowerSeries.coeff_mul]
    exact DifferentiableAt.fun_sum fun p _ => (h.1 _).const_mul _
  · have e : (TrivSqZeroExt.inl r * y : DualNumber ℂ⟦X⟧).snd = r * y.snd := by simp [TrivSqZeroExt.snd_mul]
    simp only [e, PowerSeries.coeff_mul]
    rw [fderiv_fun_sum fun p _ => (h.1 _).const_mul _, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [fderiv_const_mul (h.1 _), h.2.2]
    rfl

theorem isJet_C {F : V → ℂ} (hF : DifferentiableAt ℂ F 0) (z : V) :
    IsJet (fun v => PowerSeries.C (F v)) z (constEps (jet F z)) := by
  refine ⟨fun n => ?_, by simp, fun n => ?_⟩
  · by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn, hF]
  · by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

theorem mem_idealEps_pow {a : DualNumber ℂ⟦X⟧} {n : ℕ} (h : a ∈ idealEps ^ n) :
    PowerSeries.X ^ n ∣ a.fst ∧ PowerSeries.X ^ n ∣ a.snd := by
  rw [idealEps, ← Ideal.map_pow, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at h
  obtain ⟨c, rfl⟩ := h
  exact ⟨⟨c.fst, by simp [TrivSqZeroExt.algebraMap_eq_inl]⟩, ⟨c.snd, by
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]; simp⟩⟩

theorem isJet_of_approx {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧}
    (h : ∀ e : ℕ, ∃ x' y', IsJet x' z y' ∧ (∀ v, PowerSeries.X ^ (e + 1) ∣ x v - x' v) ∧ y - y' ∈ idealEps ^ (e + 1)) :
    IsJet x z y := by
  have key : ∀ (n : ℕ) (a b : ℂ⟦X⟧), PowerSeries.X ^ (n + 1) ∣ a - b →
      PowerSeries.coeff n a = PowerSeries.coeff n b := fun n a b hab => by
    have := PowerSeries.X_pow_dvd_iff.1 hab n (Nat.lt_succ_self n)
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨fun n => ?_, PowerSeries.ext fun n => ?_, fun n => ?_⟩
  · obtain ⟨x', y', h₁, h₂, -⟩ := h n
    simp only [fun v => key n _ _ (h₂ v)]
    exact h₁.1 n
  · obtain ⟨x', y', h₁, h₂, h₃⟩ := h n
    rw [key n _ _ (h₂ 0), ← h₁.2.1]
    exact key n _ _ (by simpa using (mem_idealEps_pow h₃).1)
  · obtain ⟨x', y', h₁, h₂, h₃⟩ := h n
    simp only [fun v => key n _ _ (h₂ v)]
    rw [← h₁.2.2]
    exact key n _ _ (by simpa using (mem_idealEps_pow h₃).2)

theorem IsJet.dualMapR_eq {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (m : ℤ) (f : V → ℂ⸨X⸩)
    (hf : ∀ v, algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (x v) = HahnSeries.single m (1 : ℂ) * f v) (F : ℂ⸨X⸩)
    (hF : ∀ n, F.coeff n = fderiv ℂ (fun v => (f v).coeff n) 0 z) :
    dualMapR (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) y = TrivSqZeroExt.inl (HahnSeries.single m (1 : ℂ)) *
      (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr F) := by
  have c : ∀ (g : ℂ⸨X⸩) (n : ℤ), (HahnSeries.single m (1 : ℂ) * g).coeff (n + m) = g.coeff n := fun g n => by
    rw [HahnSeries.coeff_single_mul_add, _root_.one_mul]
  refine TrivSqZeroExt.ext (by simp [h.2.1, hf]) ?_
  have e : (TrivSqZeroExt.inl (HahnSeries.single m (1 : ℂ)) *
      (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr F) : DualNumber ℂ⸨X⸩).snd = HahnSeries.single m (1 : ℂ) * F := by
    simp [TrivSqZeroExt.snd_mul]
  rw [e, snd_dualMapR]
  ext k
  obtain ⟨n, rfl⟩ : ∃ n, k = n + m := ⟨k - m, by ring⟩
  rw [c, hF]
  simp only [fun v => (c (f v) n).symm.trans (congrArg (fun q : ℂ⸨X⸩ => q.coeff (n + m)) (hf v).symm)]
  generalize n + m = k
  rw [LaurentSeries.coe_algebraMap]
  simp only [PowerSeries.coeff_coe]
  by_cases hk : k < 0
  · simp [hk]
  · simp only [if_neg hk]
    exact h.2.2 _

end Jet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}

def TanRel (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ)
    (ν : Out.GtPt a.D₀ (epsR ℂ)) (g : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) : Prop :=
  ∀ x, GenRelR (A := DualNumber ℂ⟦X⟧) W.w (g.s (W.e x)) (LB.pullGen _ _ _ (ν.s x) (spMap constEps))

def IsConstMul (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ)
    (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) : Prop :=
  ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (p : Sp Z ⟶ W.P.D.toPre.P.A.left) (κ : ℂ⟦X⟧ →+* Z)
    (jf : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : Fin 4 → a.D₀.P.L.ι), p ≫ W.P.D.toPre.P.A.hom = spMap κ →
    (∀ i, ⊤ ≤ (p ≫ W.P.D.toPre.famφB (W.e x) i) ⁻¹ᵁ
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
    ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) =
        valR (p ≫ W.P.D.toPre.famφB (W.e x) i) _ (W.w.s (fun _ => j₀ i, jf i)).val) ∧
      (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) *
          valR p (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB (W.e x)) jf) (f.f jf) =
        κ r * valR (p ≫ W.φ) (LB.wchart a.D₀.P.L (a.D₀.famφB x) j₀) (s₀.f j₀)

def HasConstExp (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) {j : ℕ}
    (σ : Out.H0 W.P.U.LG.L j) : Prop :=
  ∃ f : ∀ y, W.P.D.toPre.SecB j y, (∀ e, W.P.U.toUnifPre.ExpandsAt e j σ f) ∧
    ∀ x : a.D₀.X, ∃ s₀ r, IsConstMul W j x s₀ (f (W.e x)) r

end GlobalTheory.ConstTan
