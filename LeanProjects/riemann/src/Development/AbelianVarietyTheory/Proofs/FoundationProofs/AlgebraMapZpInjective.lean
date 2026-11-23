import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicComplete

noncomputable section

open GlobalTheory.K5 GlobalTheory.Glue

namespace GlobalTheory.GeoFix

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def InR (ψ : O0 p →+* Ω) (y : Ω) : Prop :=
  ∃ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt p (e t) ∧ IsAlgZp p (e t)) ∧
    y = ∑ t, e t * ψ (b t)

variable (p Ω) in

abbrev zpAlg : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra

theorem isAlgZp_iff (x : Ω) : IsAlgZp p x ↔ @IsAlgebraic ℤ_[p] Ω _ _ (zpAlg p Ω) x := by
  letI := zpAlg p Ω
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold IsAlgZp IsAlgebraic
  simp only [Polynomial.aeval_map_algebraMap]

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp p x) (hy : IsAlgZp p y) : IsAlgZp p (x * y) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff] at hx hy ⊢
  exact hx.mul hy

theorem isAlgZp_one : IsAlgZp p (1 : Ω) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff]
  exact isAlgebraic_one

theorem isInt_psi {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (b : O0 p) : IsInt p (ψ b) := by
  have hq : IsIntegral (O0 p) (T.qq n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C (qO p),
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Basic.qq_pow, sub_self]
  have hb : ψ b ∈ ψ.range := ⟨b, rfl⟩
  rw [h.rng] at hb
  exact adjoin_le_integralClosure hq hb

theorem inR_zero (ψ : O0 p →+* Ω) : InR ψ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun t => t.elim0, by simp⟩

theorem inR_psi (ψ : O0 p →+* Ω) (b : O0 p) : InR ψ (ψ b) :=
  ⟨1, fun _ => 1, fun _ => b, fun _ => ⟨isIntegral_one, isAlgZp_one⟩, by simp⟩

theorem inR_add {ψ : O0 p →+* Ω} {x y : Ω} (hx : InR ψ x) (hy : InR ψ y) : InR ψ (x + y) := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  obtain ⟨d', e', b', he', rfl⟩ := hy
  refine ⟨d + d', Fin.append e e', Fin.append b b', fun t => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) t
    · simpa using he i
    · simpa using he' i
  · rw [Fin.sum_univ_add]
    simp

theorem inR_sum {ψ : O0 p →+* Ω} {ι : Type*} (s : Finset ι) (f : ι → Ω) (hf : ∀ i ∈ s, InR ψ (f i)) :
    InR ψ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inR_zero ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inR_add (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem inR_mul {ψ : O0 p →+* Ω} {x y : Ω} (hx : InR ψ x) (hy : InR ψ y) : InR ψ (x * y) := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  obtain ⟨d', e', b', he', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine inR_sum _ _ fun i _ => inR_sum _ _ fun j _ => ?_
  refine ⟨1, fun _ => e i * e' j, fun _ => b i * b' j,
    fun _ => ⟨IsIntegral.mul (he i).1 (he' j).1, isAlgZp_mul (he i).2 (he' j).2⟩, ?_⟩
  simp only [Finset.univ_unique, Finset.sum_singleton, map_mul]
  ring

theorem inR_neg {ψ : O0 p →+* Ω} {x : Ω} (hx : InR ψ x) : InR ψ (-x) := by
  have := inR_mul (inR_psi ψ (-1)) hx
  simpa using this

theorem InR.isInt {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) {x : Ω} (hx : InR ψ x) : IsInt p x := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (isInt_psi h (b t))

theorem algebraMap_zp_injective : Function.Injective (algebraMap ℤ_[p] (O0 p)) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hm
  have hu : algebraMap ℤ_[p] (O0 p) ((PadicInt.unitCoeff h0 : ℤ_[p])) ≠ 0 :=
    ((Units.isUnit (PadicInt.unitCoeff h0)).map (algebraMap ℤ_[p] (O0 p))).ne_zero
  have hp0 : (p : O0 p) ^ m.valuation ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact mul_ne_zero hu hp0 hm

theorem exists_inR_of_isAlgZp (hc : IsClo p Ω) {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) {x : Ω}
    (hx : IsAlgZp p x) : ∃ D : O0 p, D ≠ 0 ∧ InR ψ (x * ψ D) := by
  letI := zpAlg p Ω
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hx' := (isAlgZp_iff x).1 hx
  obtain ⟨y, hy0, hyi⟩ := hx'.exists_integral_multiple
  set c : O0 p := algebraMap ℤ_[p] (O0 p) y with hcdef
  have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
    rw [h.rng]
    exact Subalgebra.algebraMap_mem _ c
  obtain ⟨D, hD⟩ := hmem
  have hc0 : c ≠ 0 := fun h0 => hy0 (algebraMap_zp_injective (by rw [← hcdef, h0, map_zero]))
  refine ⟨D, ?_, 1, fun _ => y • x, fun _ => 1, fun _ => ⟨?_, ?_⟩, ?_⟩
  · rintro rfl
    rw [map_zero] at hD
    exact hc0 (hc.inj (by rw [← hD, map_zero]))
  · exact hyi.tower_top
  · rw [isAlgZp_iff, Algebra.smul_def]
    exact (isAlgebraic_algebraMap y).mul hx'
  · simp only [Finset.univ_unique, Finset.sum_singleton, map_one, mul_one]
    rw [hD, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω, mul_comm]

theorem algebraMap_zp_eq (m : ℤ_[p]) :
    algebraMap ℤ_[p] (O0 p) m = algebraMap (Lau p) (O0 p) (HahnSeries.C m) := by
  have hH := (o0_isAdicComplete_span_p p).toIsHausdorff
  refine sub_eq_zero.1 (hH.haus' _ fun K => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hs := PadicInt.appr_spec K m
  rw [Ideal.mem_span_singleton] at hs
  obtain ⟨u, hu⟩ := hs
  have hm : m = (m.appr K : ℤ_[p]) + (p : ℤ_[p]) ^ K * u := by rw [← hu]; ring
  refine ⟨algebraMap ℤ_[p] (O0 p) u - algebraMap (Lau p) (O0 p) (HahnSeries.C u), ?_⟩
  conv_lhs => rw [hm]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

theorem isAlgZp_zp (m : ℤ_[p]) : IsAlgZp p (zp Ω m) := by
  refine ⟨Polynomial.X - Polynomial.C m, Polynomial.X_sub_C_ne_zero m, ?_⟩
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    zp, algebraMap_zp_eq, HahnSeries.C_apply, sub_self]

theorem isAlgZp_add {x y : Ω} (hx : IsAlgZp p x) (hy : IsAlgZp p y) : IsAlgZp p (x + y) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff] at hx hy ⊢
  exact hx.add hy

end GlobalTheory.GeoFix
