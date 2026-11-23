import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HermModel

open NumberField Matrix in
open scoped nonZeroDivisors in

theorem _root_.GlobalTheory.HermModel.finrank_eq_of_injective_of_span {R K M V : Type} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module R V] [Module K V] [IsScalarTower R K V] (f : M →ₗ[R] V) (hf : Function.Injective f)
    (hspan : Submodule.span K (Set.range f) = ⊤) :
    Module.finrank R M = Module.finrank K V := by
  have hle : Module.rank R M ≤ Module.rank K V := by
    rw [Module.rank_def]
    refine ciSup_le' fun s => ?_
    have hs : LinearIndependent R (f ∘ ((↑) : s.1 → M)) :=
      s.2.map' f (LinearMap.ker_eq_bot.mpr hf)
    exact ((LinearIndependent.iff_fractionRing R K).mp hs).cardinal_le_rank
  have hge : Module.rank K V ≤ Module.rank R M := by
    obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range f)
    have hrank : Module.rank K V = Cardinal.mk s := by
      rw [← rank_top, ← hspan, ← hs_span, rank_span_set hs_li]
    have hpre : ∀ x : s, ∃ m, f m = x.1 := fun x => hs_sub x.2
    choose g hg using hpre
    have hli : LinearIndependent R (f ∘ g) := by
      have : f ∘ g = ((↑) : s → V) := funext hg
      rw [this]
      exact (LinearIndependent.iff_fractionRing R K).mpr hs_li
    rw [hrank]
    exact (LinearIndependent.of_comp f hli).cardinal_le_rank
  unfold Module.finrank
  rw [le_antisymm hle hge]

section Trace

variable {E : Type} [Field E] [NumberField E]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.HermModel.eq_zero_of_trace_mul_integer {t : E}
    (ht : ∀ a : 𝓞 E, Algebra.trace ℚ E (t * a) = 0) : t = 0 := by
  classical
  have h0 : Algebra.traceForm ℚ E t = 0 := (NumberField.integralBasis E).ext fun i => by
    rw [NumberField.integralBasis_apply, Algebra.traceForm_apply, LinearMap.zero_apply]
    exact ht _
  exact (traceForm_nondegenerate ℚ E).1 t fun y => by rw [h0]; rfl

end Trace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (x - x') y = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y - _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x' y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (c • x) y = c * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x (y + y') = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y + _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y' := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x (c • y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc c := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.herm_zero_right (G : Matrix (Fin r) (Fin r) E) (x : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x 0 = 0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  simp

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.HermModel.eq_zero_of_herm_eq_zero {G : Matrix (Fin r) (Fin r) E}
    (hG : G.det ≠ 0) {w : Fin r → E} (hw : ∀ u, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G w u = 0) : w = 0 := by
  refine Matrix.eq_zero_of_vecMul_eq_zero hG (funext fun b => ?_)
  have h := hw (Pi.single b 1)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
  simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simpa [Matrix.vecMul, dotProduct] using h

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.HermModel.rank_integral_selfDual (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (_hξ : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) :
    r = D.p + D.q ∧ (LinearMap.range φ).FG ∧
      (∀ x y, IsIntegral ℤ ((NumberField.discr E : E) * (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y)))) ∧
      ∀ v : Fin r → E, (∀ y, ∃ n : ℤ, Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm v (φ y)) = n) ↔
        v ∈ LinearMap.range φ := by
  classical
  obtain ⟨hinj, hspan, -, hdet, hEF⟩ := h
  have hsmul : ∀ (c : 𝓞 E) (x : D.La), φ (c • x) = (c : E) • φ x := fun c x => by
    rw [map_smul]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hr := _root_.GlobalTheory.HermModel.finrank_eq_of_injective_of_span (R := 𝓞 E) (K := E) φ hinj hspan
    rw [Module.finrank_fin_fun] at hr
    rw [← hr, D.rank]
  · haveI := D.fin
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  · intro x y
    have hmem : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y) ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp ha
      refine ⟨D.EF (c • x) y, ?_⟩
      rw [eq_intCast, hEF, hsmul, _root_.GlobalTheory.HermModel.herm_smul_left, Algebra.traceForm_apply]
      change _ = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y) * (c : E))
      congr 1
      ring
    have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := fun i => by
      rw [NumberField.integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
    have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E) 1 hb
      (Submodule.one_le.mp le_rfl) hmem
    rw [← NumberField.coe_discr] at hint
    convert hint using 1
    rw [Algebra.smul_def, mul_one]
    simp
  · intro v
    constructor
    · intro hv
      by_cases hξ0 : ξ = 0
      · have hsub : ∀ x : D.La, x = 0 := fun x => D.unimod.1 <| by
          refine LinearMap.ext fun y => ?_
          have := hEF x y
          rw [hξ0, zero_mul, map_zero] at this
          simp [map_zero, Int.cast_eq_zero.mp this]
        have hbot : Submodule.span E (Set.range φ) ≤ ⊥ := by
          rw [Submodule.span_le]
          rintro _ ⟨x, rfl⟩
          rw [hsub x, map_zero]
          exact Submodule.zero_mem _
        have hv0 : v = 0 := by
          have : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
          simpa using hbot this
        rw [hv0]
        exact Submodule.zero_mem _
      · choose n hn using hv
        let ℓ : D.La →+ ℤ := AddMonoidHom.mk' n fun y y' => by
          apply Int.cast_injective (α := ℚ)
          rw [Int.cast_add, ← hn, ← hn, ← hn, map_add, _root_.GlobalTheory.HermModel.herm_add_right, mul_add,
            map_add]
        obtain ⟨x, hx⟩ := D.unimod.2 ℓ.toIntLinearMap
        have htr : ∀ y, Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) (φ y)) = 0 := by
          intro y
          have h1 : (D.EF x y : ℚ) = n y := by
            rw [hx]
            rfl
          rw [_root_.GlobalTheory.HermModel.herm_sub_left, mul_sub, map_sub, hn, ← hEF, h1, sub_self]
        have hzero : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) (φ y) = 0 := by
          intro y
          have : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) (φ y) = 0 := by
            refine _root_.GlobalTheory.HermModel.eq_zero_of_trace_mul_integer fun a => ?_
            have hc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((H.bar.symm a : 𝓞 E) : E) = (a : E) := by
              unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
              rw [← H.bar_eq, RingEquiv.apply_symm_apply]
            have := htr (H.bar.symm a • y)
            rw [hsmul, _root_.GlobalTheory.HermModel.herm_smul_right, hc, ← mul_assoc] at this
            exact this
          exact (mul_eq_zero.mp this).resolve_left hξ0
        have hall : ∀ u, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (v - φ x) u = 0 := by
          intro u
          have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
          induction hu using Submodule.span_induction with
          | mem w hw =>
            obtain ⟨y, rfl⟩ := hw
            exact hzero y
          | zero => exact _root_.GlobalTheory.HermModel.herm_zero_right _ _
          | add w w' _ _ hw hw' => rw [_root_.GlobalTheory.HermModel.herm_add_right, hw, hw', add_zero]
          | smul c w _ hw => rw [_root_.GlobalTheory.HermModel.herm_smul_right, hw, zero_mul]
        have hw := _root_.GlobalTheory.HermModel.eq_zero_of_herm_eq_zero hdet hall
        exact ⟨x, (sub_eq_zero.mp hw).symm⟩
    · rintro ⟨x, rfl⟩ y
      exact ⟨D.EF x y, (hEF x y).symm⟩

end GlobalTheory.HermModel
