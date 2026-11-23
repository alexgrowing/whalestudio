import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneApproximationAtLevelPrimes
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws

noncomputable section

namespace GlobalTheory.SplitCharTrivial

open Filter Topology
open scoped TensorProduct Matrix

section Generic

open Formalism.UG GlobalTheory.UnRep.SplitRep

variable {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem cT_add (M N : Matrix (Fin n) (Fin n) A) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j
  simp [cT]

theorem cT_smul (a : A) (M : Matrix (Fin n) (Fin n) A) : cT σ (a • M) = σ a • cT σ M := by
  ext i j
  simp [cT]

def cut (ε : A) (hε : ε * ε = ε) (hσ : σ ε = ε) : UJ σ J →* UJ σ J where
  toFun g := ⟨mix ε hε g.1, by
    have hg : cT σ g.1.1 * J * g.1.1 = J := g.2
    have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, hε]; ring
    have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
    have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, h2]; ring
    change cT σ (mix ε hε g.1).1 * J * (mix ε hε g.1).1 = J
    simp only [mix_val, cT_add, cT_smul, cT_one, map_sub, map_one, hσ, add_mul, mul_add, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one, one_mul, hg]
    rw [← add_smul]; simp⟩
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    change ε • (1 : Matrix (Fin n) (Fin n) A) + (1 - ε) • 1 = 1
    rw [← add_smul]; simp
  map_mul' g h := by
    refine Subtype.ext (Units.ext ?_)
    have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, hε]; ring
    have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
    have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, h2]; ring
    change ε • (g.1.1 * h.1.1) + (1 - ε) • 1 = (mix ε hε g.1).1 * (mix ε hε h.1).1
    simp only [mix_val, add_mul, mul_add, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one, one_mul]

theorem cut_val (ε : A) (hε : ε * ε = ε) (hσ : σ ε = ε) (g : UJ σ J) :
    (cut σ J ε hε hσ g).1.1 = 1 + ε • (g.1.1 - 1) := by
  change ε • g.1.1 + (1 - ε) • 1 = _
  rw [sub_smul, smul_sub, one_smul]; abel

theorem proj_mul (P : Matrix (Fin n) (Fin n) A) (hP : P * P = P) (a b : A) :
    (1 + (a - 1) • P) * (1 + (b - 1) • P) = 1 + (a * b - 1) • P := by
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hP]
  rw [add_assoc, ← add_smul, ← add_smul]
  congr 2
  ring

def rf (P : Matrix (Fin n) (Fin n) A) (hP : P * P = P) (hJ : cT σ P * J = J * P) (a : A) (ha : a * σ a = 1) :
    UJ σ J :=
  ⟨⟨1 + (a - 1) • P, 1 + (σ a - 1) • P, by rw [proj_mul P hP, ha, sub_self, zero_smul, add_zero],
    by rw [proj_mul P hP, mul_comm, ha, sub_self, zero_smul, add_zero]⟩, by
    change cT σ (1 + (a - 1) • P) * J * (1 + (a - 1) • P) = J
    rw [cT_add, cT_smul, cT_one, add_mul, one_mul, Matrix.smul_mul, hJ, ← Matrix.mul_smul, map_sub, map_one]
    nth_rw 1 [← mul_one J]
    rw [← mul_add, mul_assoc, proj_mul P hP, mul_comm (σ a), ha, sub_self, zero_smul, add_zero, mul_one]⟩

theorem tendsto_UJ [TopologicalSpace A] {g : ℕ → UJ σ J} {g₀ : UJ σ J}
    (h1 : Tendsto (fun k => (g k).1.1) atTop (𝓝 g₀.1.1))
    (h2 : Tendsto (fun k => ((g k)⁻¹).1.1) atTop (𝓝 (g₀⁻¹).1.1)) : Tendsto g atTop (𝓝 g₀) := by
  rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

theorem tendsto_rf [TopologicalSpace A] [IsTopologicalRing A] (hσ : Continuous σ) (P : Matrix (Fin n) (Fin n) A)
    (hP : P * P = P) (hJ : cT σ P * J = J * P) {a : ℕ → A} (ha : ∀ k, a k * σ (a k) = 1) {a₀ : A}
    (ha₀ : a₀ * σ a₀ = 1) (h : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun k => rf σ J P hP hJ (a k) (ha k)) atTop (𝓝 (rf σ J P hP hJ a₀ ha₀)) := by
  have hc : Continuous fun x : A => (1 : Matrix (Fin n) (Fin n) A) + (x - 1) • P := by fun_prop
  exact tendsto_UJ σ J ((hc.tendsto _).comp h) (((hc.comp hσ).tendsto _).comp h)

theorem norm_cut (ε : A) (hε : ε * ε = ε) (hσ : σ ε = ε) (a : A) (ha : a * σ a = 1) :
    (1 + ε * (a - 1)) * σ (1 + ε * (a - 1)) = 1 := by
  simp only [map_add, map_mul, map_sub, map_one, hσ]
  linear_combination (a - 1) * (σ a - 1) * hε + ε * ha

theorem cut_rf (P : Matrix (Fin n) (Fin n) A) (hP : P * P = P) (hJ : cT σ P * J = J * P) (ε : A) (hε : ε * ε = ε)
    (hσ : σ ε = ε) (a : A) (ha : a * σ a = 1) :
    cut σ J ε hε hσ (rf σ J P hP hJ a ha) = rf σ J P hP hJ (1 + ε * (a - 1)) (norm_cut σ ε hε hσ a ha) := by
  refine Subtype.ext (Units.ext ((cut_val σ J ε hε hσ _).trans ?_))
  change 1 + ε • (1 + (a - 1) • P - 1) = 1 + (1 + ε * (a - 1) - 1) • P
  rw [add_sub_cancel_left, add_sub_cancel_left, smul_smul]

theorem map_scal {B : Type} [CommRing B] (f : A →+* B) (ε a : A) :
    f (1 + (1 - ε) * (a - 1)) = 1 + (1 - f ε) * (f a - 1) := by simp

theorem map_scal_zero {B : Type} [CommRing B] (f : A →+* B) (ε a : A) (h : f ε = 0) :
    f (1 + (1 - ε) * (a - 1)) = f a := by simp [h]

end Generic

section Scalars

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.UnRep GlobalTheory.UnRep.NormOne GlobalTheory.UnRep.SplitRep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_inv_inf {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun k => inclR (F := F) (E := E) (Ainf F) ((N k : E)⁻¹)) atTop (𝓝 0) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Tendsto (fun k => algebraMap F (Ainf F) ((N k : F)⁻¹)) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => ?_
    change Tendsto _ _ (𝓝 (0 : v.Completion))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hN).congr fun k => ?_
    rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
    simp
  have h2 := h1.smul_const (1 : Ainf F ⊗[F] E)
  rw [zero_smul] at h2
  refine h2.congr fun k => ?_
  change _ = (1 : Ainf F) ⊗ₜ[F] ((N k : E)⁻¹)
  rw [algebraMap_smul, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
    Algebra.smul_def, mul_one, map_inv₀, map_natCast]

theorem tendsto_ratio_inf {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (hN0 : ∀ k, N k ≠ 0) (α β : E) (hβ : β ≠ 0)
    (hw : ∀ k, 1 + N k * β ≠ 0) :
    Tendsto (fun k => inclR (F := F) (E := E) (Ainf F) ((1 + N k * α) / (1 + N k * β))) atTop
      (𝓝 (inclR (F := F) (Ainf F) (α / β))) := by
  classical
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  have a1 : IsOpen {x : (∀ v : InfinitePlace F, v.Completion) | IsUnit x} := Units.isOpen
  have a2 : ∀ x : (∀ v : InfinitePlace F, v.Completion), IsUnit x → ContinuousAt Ring.inverse x := by
    rintro _ ⟨x, rfl⟩
    exact NormedRing.inverse_continuousAt x
  have b1 : IsOpen {x : Ainf F | IsUnit x} := a1
  have b2 : ∀ x : Ainf F, IsUnit x → ContinuousAt Ring.inverse x := a2
  obtain ⟨-, h2⟩ := GlobalTheory.RealApprox.units_of_free (A := Ainf F) (R := Ainf F ⊗[F] E)
    (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E)) b1 b2
  set ι := inclR (F := F) (E := E) (Ainf F)
  have hi : ∀ x : E, x ≠ 0 → Ring.inverse (ι x) = ι x⁻¹ := fun x hx => by
    have : ι x * ι x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    rw [← mul_one (Ring.inverse _), ← this, ← mul_assoc, Ring.inverse_mul_cancel _ (hx.isUnit.map ι), one_mul]
  have t := tendsto_inv_inf (F := F) (E := E) hN
  have t1 := t.add_const (ι α)
  have t2 := t.add_const (ι β)
  rw [zero_add] at t1 t2
  have t3 := t1.mul ((h2 _ (hβ.isUnit.map ι)).tendsto.comp t2)
  rw [hi β hβ, ← map_mul, ← div_eq_mul_inv] at t3
  refine t3.congr fun k => ?_
  have hk : (N k : E) ≠ 0 := Nat.cast_ne_zero.2 (hN0 k)
  have e : (N k : E)⁻¹ + β = (N k : E)⁻¹ * (1 + N k * β) := by field_simp
  have hk' := hw k
  rw [Function.comp_apply, ← map_add, ← map_add, hi _ (by rw [e]; exact mul_ne_zero (inv_ne_zero hk) hk'), ← map_mul, e]
  congr 1
  field_simp

theorem exists_cut (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (N : ℕ) (hN : 0 < N) (α β : 𝓞 E)
    (hβ : 1 + (N : 𝓞 E) * β ≠ 0) (w : E) (hw : w = (1 + N * α) / (1 + N * β)) (hw1 : w * c w = 1) :
    ∃ e : Af F, e * e = e ∧ {v | e v ≠ 0}.Finite ∧ (∀ v, e v ≠ 0 → SplitPl c v) ∧
      ∃ a ∈ intAf F, ∃ b : 𝓞 E, ((1 - e) ⊗ₜ[F] (w - 1) : Af F ⊗[F] E) = N • (a ⊗ₜ[F] (b : E)) := by
  classical
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hβE : (1 : E) + N * β ≠ 0 := by exact_mod_cast hβ
  obtain ⟨s, hs0, hsP, hs⟩ := GlobalTheory.UnRep.exists_denominator_primes_prescribed E (fun P => Moved c P) Unit
    (fun _ => (w - 1) / N) (by
      intro _ P hQ
      by_cases hNP : (N : 𝓞 E) ∈ P.asIdeal
      · refine val_le_of_mul P _ ((α - β : 𝓞 E) : E) (1 + N * β) (fun h => P.isPrime.ne_top ?_) ?_
          (P.valuation_le_one _)
        · rw [Ideal.eq_top_iff_one]
          simpa using sub_mem h (Ideal.mul_mem_right β _ hNP)
        · push_cast
          rw [hw]
          field_simp
          ring
      · exact val_le_of_unit P _ N hNP
          (GlobalTheory.UnRep.valuation_eq_one_of_norm_one_of_not_moved F E c hc _ P hw1 hQ))
  obtain ⟨b, hb⟩ := hs ()
  obtain ⟨m, hm0, ⟨s', hs'⟩, hm⟩ := exists_multiple (F := F) s hs0
  have hfin : {v : HeightOneSpectrum (𝓞 F) | m ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {m}) (by simpa using hm0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let e : Af F := ∑ v ∈ hfin.toFinset, singleV F v 1
  have he1 : ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal → e v = 1 := fun v hv => by
    change evalV F v e = 1
    rw [map_sum, Finset.sum_eq_single v (fun w _ h => GlobalTheory.SplitIdem.evalV_singleV_ne _ w _ h.symm)
      (fun h => absurd (hfin.mem_toFinset.2 hv) h), GlobalTheory.SplitIdem.evalV_singleV_same]
  have he0 : ∀ v : HeightOneSpectrum (𝓞 F), m ∉ v.asIdeal → e v = 0 := fun v hv => by
    change evalV F v e = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ w _
      (fun h : v = w => hv (h ▸ hfin.mem_toFinset.1 hw))
  obtain ⟨a, ha, hae⟩ := exists_div m hm0 e he1 he0
  refine ⟨e, ?_, hfin.subset fun v hv => by_contra fun h => hv (he0 v h), fun v hv => ?_, a, ha, s' * b, ?_⟩
  · refine DFunLike.ext _ _ fun v => ?_
    change e v * e v = e v
    by_cases hv : m ∈ v.asIdeal
    · rw [he1 v hv, one_mul]
    · rw [he0 v hv, zero_mul]
  · obtain ⟨P, hP, hsP', hPc⟩ := hm v (by_contra fun h => hv (he0 v h))
    exact ⟨P, hP, hPc, hsP P hP hsP'⟩
  · have e1 : algebraMap F E (m : F) = (s : E) * (s' : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) hs'
      simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at this
      exact this
    rw [← hae, TensorProduct.smul_tmul, ← TensorProduct.tmul_smul, Algebra.smul_def, e1, nsmul_eq_mul]
    congr 1
    have hb' : (s : E) * (w - 1) = N * b := by rw [← hb]; field_simp
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at hb' ⊢
    linear_combination algebraMap (𝓞 E) E s' * hb'

theorem exists_seq (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) (u : E) (hu : u * c u = 1) :
    ∃ (w : ℕ → E) (e : ℕ → Af F), (∀ k, w k * c (w k) = 1) ∧
      (∀ k, e k * e k = e k ∧ {v | e k v ≠ 0}.Finite ∧ ∀ v, e k v ≠ 0 → SplitPl c v) ∧
      Tendsto (fun k => inclR (F := F) (Ainf F) (w k)) atTop (𝓝 (inclR (F := F) (Ainf F) u)) ∧
      Tendsto (fun k => ((1 - e k) ⊗ₜ[F] (w k - 1) : Af F ⊗[F] E)) atTop (𝓝 0) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  obtain ⟨α, hα, huα⟩ := hilbert90_matrix_subalgebra_norm_one c hc hc1 u hu
  obtain ⟨β, hβc⟩ := exists_conj c α
  have hαE : (α : E) ≠ 0 := by exact_mod_cast hα
  have hβE : (β : E) ≠ 0 := by rw [hβc]; simpa using hαE
  have hu2 : u = (α : E) / β := by rw [eq_div_iff hβE, hβc, huα]
  let N : ℕ → ℕ := fun k => (k + 2).factorial
  have hN1 : ∀ k, N k ≠ 1 := fun k => (Nat.one_lt_factorial.2 (by omega)).ne'
  have hN : Tendsto N atTop atTop := factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 2)
  have h1 : ∀ k (z : 𝓞 E), (1 : E) + N k * z ≠ 0 := fun k z => by exact_mod_cast one_add_ne_zero (N k) (hN1 k) z
  let w : ℕ → E := fun k => (1 + N k * α) / (1 + N k * β)
  have hw : ∀ k, w k * c (w k) = 1 := fun k => by
    have a1 := h1 k α
    have a2 := h1 k β
    simp only [w, map_div₀, map_add, map_mul, map_one, map_natCast, ← hβc, show c β = α by rw [hβc, hc]]
    field_simp
  choose e he1 he2 he3 a ha b hab using fun k => exists_cut c hc (N k) (Nat.factorial_pos _) α β
    (one_add_ne_zero (N k) (hN1 k) β) (w k) rfl (hw k)
  refine ⟨w, e, hw, fun k => ⟨he1 k, he2 k, he3 k⟩, ?_, ?_⟩
  · rw [hu2]
    exact tendsto_ratio_inf hN (fun k => (Nat.factorial_pos _).ne') _ _ hβE fun k => h1 k β
  · obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat F E
      (Submodule.span (𝓞 E) {(fun _ => 1 : Fin 1 → E)}) (Submodule.fg_span_singleton _)
    have ht := GlobalTheory.SplitRepsOpen.tendsto_smul_zero_of_compact (R := Af F)
      ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F).comp (tendsto_add_atTop_nat 2)) hC
      fun k => hLC _ (AddSubgroup.subset_closure ⟨a k, ha k, b k • (fun _ => 1 : Fin 1 → E),
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), rfl⟩)
    refine (tendsto_pi_nhds.1 ht 0).congr fun k => ?_
    rw [hab, Pi.smul_apply, Function.comp_apply, Nat.cast_smul_eq_nsmul]
    congr 2
    exact mul_one _

omit [NumberField F] [NumberField E] in

def cutH (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : R ⊗[F] E)
    (hε : ε * ε = ε) (hσ : sigR R σ ε = ε) : HA R σ J →* HA R σ J :=
  cut (sigR R σ) (JR R J) ε hε hσ

end Scalars

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IdemModTwo GlobalTheory.Member GlobalTheory.UnRep GlobalTheory.UnitarySplit
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem tendsto_AE {x : ℕ → Formalism.L2.Theta.AE D} {x₀ : Formalism.L2.Theta.AE D}
    (h1 : Tendsto (fun k => infPart D (x k)) atTop (𝓝 (infPart D x₀)))
    (h2 : Tendsto (fun k => finPart D (x k)) atTop (𝓝 (finPart D x₀))) : Tendsto x atTop (𝓝 x₀) := by
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h : ∀ z, e.symm (infPart D z, finPart D z) = z := fun z => by
    have : (infPart D z, finPart D z) = e z := Prod.ext (he z).1.symm (he z).2.symm
    rw [this]
    exact e.symm_apply_apply z
  have := (hc.tendsto _).comp (h1.prodMk_nhds h2)
  rw [h] at this
  exact this.congr fun k => h _

def cutA (V : HSp D) (ε : Formalism.L2.Theta.AE D) (hε : ε * ε = ε) (hσ : cA D ε = ε) : GA D V →* GA D V :=
  cutH (AF D.host.F) D.sp.cm.sig V.gram ε hε hσ

theorem mt_cutA (V : HSp D) (ε : Formalism.L2.Theta.AE D) (hε : ε * ε = ε) (hσ : cA D ε = ε) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutA V ε hε hσ g) = 1 + ε • (Formalism.L2.Theta.mt V g - 1) := cut_val _ _ ε hε hσ g

theorem mt_ext {V : HSp D} {g h : GA D V} (e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V h) : g = h :=
  Subtype.ext (Units.ext e)

theorem mt_mul {V : HSp D} (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := rfl

theorem cutA_mul (V : HSp D) (ε : Formalism.L2.Theta.AE D) (hε : ε * ε = ε) (hσ : cA D ε = ε)
    (hε' : (1 - ε) * (1 - ε) = 1 - ε) (hσ' : cA D (1 - ε) = 1 - ε) (g : GA D V) :
    cutA V ε hε hσ g * cutA V (1 - ε) hε' hσ' g = g :=
  mt_ext (GlobalTheory.UnRep.SplitRep.mix_mul_mix ε hε hε' (matHom V g))

section Char

variable {V : HSp D} {ν : GA D V →* Circle}

theorem eq_one_of_finset (hs : ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hS : ∀ v ∈ S, SplitPl (cF D) v) :
    ∀ g : GA D V, (∑ v ∈ S, pl D v) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 → ν g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro g hg
    rw [Finset.sum_empty, zero_smul] at hg
    rw [show g = 1 from mt_ext (sub_eq_zero.1 hg.symm), map_one]
  | insert v S hv ih =>
    intro g hg
    obtain ⟨e, he⟩ := GlobalTheory.MovedSplit.exists_splitAt D v (hS v (Finset.mem_insert_self _ _))
    have hp : pl D v * pl D v = pl D v := by
      rw [← map_mul, singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same, one_mul]
    have hp' : (1 - pl D v) * (1 - pl D v) = 1 - pl D v := by linear_combination hp
    have hσ : cA D (pl D v) = pl D v := cA_fj D _
    have hσ' : cA D (1 - pl D v) = 1 - pl D v := by rw [map_sub, map_one, hσ]
    have hq : pl D v * ∑ w ∈ S, pl D w = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun w hw => pl_mul_pl fun h => hv (h ▸ hw)
    rw [Finset.sum_insert hv] at hg
    rw [← cutA_mul V _ hp hσ hp' hσ' g, map_mul, hs e ((isSplitIdem_iff e).2 ⟨v, he⟩), one_mul]
    · refine ih (fun w hw => hS w (Finset.mem_insert_of_mem hw)) _ ?_
      rw [mt_cutA, add_sub_cancel_left, smul_smul]
      conv_rhs => rw [← hg, smul_smul]
      congr 1
      linear_combination hp
    · intro i j
      rw [mt_cutA, add_sub_cancel_left, he.2.2, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hp]

theorem eq_one_of_idem (hs : ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) (e : Af D.host.F)
    (h1 : e * e = e) (h2 : {v | e v ≠ 0}.Finite) (h3 : ∀ v, e v ≠ 0 → SplitPl (cF D) v) (g : GA D V)
    (hg : fj D e • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1) : ν g = 1 := by
  refine eq_one_of_finset hs h2.toFinset (fun v hv => h3 v (h2.mem_toFinset.1 hv)) g ?_
  rw [← map_sum, ← GlobalTheory.SplitReps.idem_eq_sum e h1 h2.toFinset (fun v => h2.mem_toFinset), hg]

end Char

theorem inf_fj (e : Af D.host.F) : infPart D (fj D e) = 0 := TensorProduct.zero_tmul _ _

theorem fin_fj (e : Af D.host.F) : finPart D (fj D e) = e ⊗ₜ[D.host.F] 1 := rfl

theorem idem_inf : (1 - fj D 1) * (1 - fj D 1) = 1 - fj D 1 := by
  have : fj D 1 * fj D 1 = fj D 1 := by rw [← map_mul, mul_one]
  linear_combination this

theorem conj_inf : cA D (1 - fj D 1) = 1 - fj D 1 := by rw [map_sub, map_one, cA_fj]

def pInf (V : HSp D) : GA D V →* GA D V := cutA V (1 - fj D 1) idem_inf conj_inf

theorem map_sub_one {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) : f ((M - 1) i j) = (M.map f - 1) i j := by
  simp [Matrix.one_apply, apply_ite f]

theorem map_cut {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) (ε : R) :
    (1 + ε • (M - 1)).map f = 1 + f ε • (M.map f - 1) := by
  ext i j
  simp [Matrix.one_apply, apply_ite f]

theorem infHom_pInf (V : HSp D) (g : GA D V) : infHom V (pInf V g) = infHom V g := by
  refine Units.ext ?_
  change (Formalism.L2.Theta.mt V (cutA V _ _ _ g)).map (infPart D) = (Formalism.L2.Theta.mt V g).map (infPart D)
  rw [mt_cutA, map_cut, RingHom.map_sub, RingHom.map_one, inf_fj, sub_zero, one_smul, add_sub_cancel]

theorem finHom_pInf (V : HSp D) (g : GA D V) : finHom V (pInf V g) = 1 := by
  refine Units.ext ?_
  change (Formalism.L2.Theta.mt V (cutA V _ _ _ g)).map (finPart D) = 1
  rw [mt_cutA, map_cut, RingHom.map_sub, RingHom.map_one, fin_fj, ← Algebra.TensorProduct.one_def, sub_self,
    zero_smul, add_zero]

theorem continuous_cA : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (Formalism.L2.Theta.AE D) := ⟨rfl⟩
  have : ContinuousAdd (Formalism.L2.Theta.AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  have : ContinuousSMul (AF D.host.F) (Formalism.L2.Theta.AE D) := IsModuleTopology.toContinuousSMul _ _
  exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (cF D x) := rfl

theorem inf_scal (e : Af D.host.F) (x : D.host.E) :
    infPart D (1 + (1 - fj D e) * (incA D x - 1)) = inclR (F := D.host.F) (Ainf D.host.F) x :=
  map_scal_zero (infPart D) (fj D e) (incA D x) (inf_fj e)

theorem tmul_scal {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (e : R) (x : E) :
    (1 + (1 - e ⊗ₜ[F] (1 : E)) * ((1 : R) ⊗ₜ[F] x - 1) : R ⊗[F] E) = 1 + (1 - e) ⊗ₜ[F] (x - 1) := by
  congr 1
  rw [Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul, ← TensorProduct.tmul_sub,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem fin_scal (e : Af D.host.F) (x : D.host.E) :
    finPart D (1 + (1 - fj D e) * (incA D x - 1)) = 1 + (1 - e) ⊗ₜ[D.host.F] (x - 1) :=
  (map_scal (finPart D) (fj D e) (incA D x)).trans (tmul_scal e x)

theorem tendsto_scal {w : ℕ → D.host.E} {u : D.host.E} {e : ℕ → Af D.host.F}
    (t1 : Tendsto (fun k => inclR (F := D.host.F) (Ainf D.host.F) (w k)) atTop
      (𝓝 (inclR (F := D.host.F) (Ainf D.host.F) u)))
    (t2 : Tendsto (fun k => ((1 - e k) ⊗ₜ[D.host.F] (w k - 1) : Af D.host.F ⊗[D.host.F] D.host.E)) atTop (𝓝 0)) :
    Tendsto (fun k => 1 + (1 - fj D (e k)) * (incA D (w k) - 1)) atTop
      (𝓝 (1 + (1 - fj D 1) * (incA D u - 1))) := by
  have : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousAdd (Af D.host.F) _
  refine tendsto_AE ?_ ?_
  · rw [inf_scal 1 u, funext fun k => inf_scal (e k) (w k)]
    exact t1
  · rw [fin_scal 1 u, sub_self, TensorProduct.zero_tmul, funext fun k => fin_scal (e k) (w k)]
    exact t2.const_add 1

section Refl

variable {V : HSp D} {P : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hP : P * P = P)
  (hJ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram = V.gram * P)

def rfA (a : Formalism.L2.Theta.AE D) (ha : a * cA D a = 1) : GA D V :=
  rf (cA D) (JR (AF D.host.F) V.gram) (P.map (incA D)) (by rw [← Matrix.map_mul, hP])
    (by rw [GlobalTheory.AutFunCounterexample.cT_map_gen, JR, ← Matrix.map_mul, ← Matrix.map_mul, hJ]) a ha

theorem mt_rfA (a : Formalism.L2.Theta.AE D) (ha : a * cA D a = 1) :
    Formalism.L2.Theta.mt V (rfA hP hJ a ha) = 1 + (a - 1) • P.map (incA D) := rfl

theorem norm_incA {u : D.host.E} (hu : u * cF D u = 1) : incA D u * cA D (incA D u) = 1 := by
  rw [cA_incA, ← map_mul, hu, map_one]

theorem mt_rfA_rat {u : D.host.E} (hu : u * cF D u = 1) :
    Formalism.L2.Theta.mt V (rfA hP hJ _ (norm_incA hu)) = (1 + (u - 1) • P).map (incA D) := by
  rw [mt_rfA]
  ext i j
  simp [Matrix.one_apply, apply_ite (incA D)]

theorem rfA_mem {u : D.host.E} (hu : u * cF D u = 1) : rfA hP hJ _ (norm_incA hu) ∈ GQ V :=
  ⟨(rf (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram P hP hJ u hu).1,
    (rf (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram P hP hJ u hu).2, Units.ext (mt_rfA_rat hP hJ hu).symm⟩

theorem cutA_rfA (ε : Formalism.L2.Theta.AE D) (hε : ε * ε = ε) (hσ : cA D ε = ε) (a : Formalism.L2.Theta.AE D)
    (ha : a * cA D a = 1) :
    cutA V ε hε hσ (rfA hP hJ a ha) = rfA hP hJ (1 + ε * (a - 1)) (norm_cut (cA D) ε hε hσ a ha) :=
  cut_rf (cA D) (JR (AF D.host.F) V.gram) _ _ _ ε hε hσ a ha

theorem tendsto_rfA {a : ℕ → Formalism.L2.Theta.AE D} (ha : ∀ k, a k * cA D (a k) = 1) {a₀ : Formalism.L2.Theta.AE D}
    (ha₀ : a₀ * cA D a₀ = 1) (h : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun k => rfA hP hJ (a k) (ha k)) atTop (𝓝 (rfA hP hJ a₀ ha₀)) := by
  have : IsModuleTopology (AF D.host.F) (Formalism.L2.Theta.AE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (Formalism.L2.Theta.AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact tendsto_rf (cA D) _ continuous_cA _ _ _ ha ha₀ h

theorem eq_one_refl {ν : GA D V →* Circle} (hν : Continuous ν) (hq : ∀ γ ∈ GQ V, ν γ = 1)
    (hs : ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) {u : D.host.E} (hu : u * cF D u = 1) :
    ν (pInf V (rfA hP hJ _ (norm_incA hu))) = 1 := by
  obtain ⟨-, -, -, -, c2, -, c1, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨w, e, hw, he, t1, t2⟩ := exists_seq (cF D) c2 c1 u hu
  have hε : ∀ k, fj D (e k) * fj D (e k) = fj D (e k) := fun k => by rw [← map_mul, (he k).1]
  have hε' : ∀ k, (1 - fj D (e k)) * (1 - fj D (e k)) = 1 - fj D (e k) := fun k => by linear_combination hε k
  have hσ' : ∀ k, cA D (1 - fj D (e k)) = 1 - fj D (e k) := fun k => by rw [map_sub, map_one, cA_fj]
  have n1 := fun k => norm_cut (cA D) _ (hε' k) (hσ' k) _ (norm_incA (hw k))
  have h1 : ∀ k, ν (rfA hP hJ _ (n1 k)) = 1 := fun k => by
    have a1 := hq _ (rfA_mem hP hJ (hw k))
    rw [← cutA_mul V _ (hε k) (cA_fj D _) (hε' k) (hσ' k) (rfA _ _ _ _), map_mul,
      eq_one_of_idem hs (e k) (he k).1 (he k).2.1 (he k).2.2 _
        (by rw [mt_cutA, add_sub_cancel_left, smul_smul, hε]), one_mul, cutA_rfA] at a1
    exact a1
  have t : Tendsto (fun k => 1 + (1 - fj D (e k)) * (incA D (w k) - 1)) atTop
      (𝓝 (1 + (1 - fj D 1) * (incA D u - 1))) := tendsto_scal t1 t2
  have t' := (hν.tendsto _).comp
    (tendsto_rfA hP hJ n1 (norm_cut (cA D) _ idem_inf conj_inf _ (norm_incA hu)) t)
  rw [pInf, cutA_rfA]
  exact tendsto_nhds_unique t' (tendsto_const_nhds.congr fun k => (h1 k).symm)

end Refl

theorem exists_proj (V : HSp D) (x : Fin V.rank → D.host.E) (hx : hermE (cF D) V.gramᵀ x x ≠ 0) :
    ∃ P : Matrix (Fin V.rank) (Fin V.rank) D.host.E, P * P = P ∧
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram = V.gram * P ∧
      ∀ u, GlobalTheory.UnRep.refl (cF D) V.gramᵀ x u = 1 + (u - 1) • P := by
  obtain ⟨-, -, -, -, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨-, -, l3, l4⟩ := GlobalTheory.UnRep.ReflLaws.refl_laws _ _ (cF D) V.rank V.gramᵀ ⟨c2, c1, gh, gd⟩ x hx
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin V.rank) (Fin V.rank) D.host.E,
      ∀ u, GlobalTheory.UnRep.refl (cF D) V.gramᵀ x u = 1 + (u - 1) • P :=
    ⟨(hermE (cF D) V.gramᵀ x x)⁻¹ • Matrix.vecMulVec x (V.gramᵀ *ᵥ fun b => cF D (x b)), fun u => by
      rw [GlobalTheory.UnRep.refl, smul_smul, div_eq_mul_inv]⟩
  have hPP : P * P = P := by
    have := l3 0 0
    rw [mul_zero, hP, zero_sub, neg_smul, one_smul] at this
    linear_combination (norm := noncomm_ring) this
  refine ⟨P, hPP, ?_, hP⟩
  have hr : GlobalTheory.UnRep.refl (cF D) V.gramᵀ x (-1) * GlobalTheory.UnRep.refl (cF D) V.gramᵀ x (-1) = 1 := by
    rw [l3, hP]; simp
  have hu : (⟨_, _, hr, hr⟩ : GL (Fin V.rank) D.host.E) ∈
      Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    refine (GlobalTheory.Member.RatElt.mem_UJ_iff _ _ _).2 fun a b => ?_
    refine neg_inj.1 ?_
    rw [← GlobalTheory.Member.RatElt.herm_eq, ← GlobalTheory.Member.RatElt.herm_eq, GlobalTheory.UnRep.Space.herm_neg_eq,
      GlobalTheory.UnRep.Space.herm_neg_eq, l4 (-1) (by simp)]
  have h1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.UnRep.refl (cF D) V.gramᵀ x (-1)) * V.gram *
    GlobalTheory.UnRep.refl (cF D) V.gramᵀ x (-1) = V.gram := hu
  have h2 := congrArg (· * GlobalTheory.UnRep.refl (cF D) V.gramᵀ x (-1)) h1
  simp only [mul_assoc, hr, mul_one] at h2
  rw [hP, cT_add, cT_smul, Formalism.UG.cT_one, add_mul, mul_add, one_mul, mul_one, add_right_inj, Matrix.smul_mul,
    Matrix.mul_smul, map_sub, map_neg, map_one] at h2
  exact smul_right_injective _ (by norm_num) h2

section Char

variable {V : HSp D} {ν : GA D V →* Circle}

theorem eq_one_rat (hν : Continuous ν) (hq : ∀ γ ∈ GQ V, ν γ = 1)
    (hs : ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) (l : List ((Fin V.rank → D.host.E) × D.host.E))
    (hl : ∀ p ∈ l, hermE (cF D) V.gramᵀ p.1 p.1 ≠ 0 ∧ p.2 * cF D p.2 = 1) :
    ∀ γ : GA D V, Formalism.L2.Theta.mt V γ = (l.map fun p => GlobalTheory.UnRep.refl (cF D) V.gramᵀ p.1 p.2).prod.map (incA D) →
      ν (pInf V γ) = 1 := by
  induction l with
  | nil =>
    intro γ h
    rw [List.map_nil, List.prod_nil, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)] at h
    rw [show γ = 1 from mt_ext h, map_one, map_one]
  | cons p l ih =>
    intro γ h
    obtain ⟨hx, hu⟩ := hl p List.mem_cons_self
    obtain ⟨P, hP, hJ, hr⟩ := exists_proj V p.1 hx
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, hr, ← mt_rfA_rat hP hJ hu] at h
    have h1 := eq_one_refl hP hJ hν hq hs hu
    generalize rfA hP hJ _ (norm_incA hu) = r at h h1
    have h2 := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (r⁻¹ * γ) (by
      rw [mt_mul, h, ← mul_assoc, ← mt_mul, inv_mul_cancel]
      exact one_mul _)
    rw [← mul_inv_cancel_left r γ, map_mul, map_mul, h1, h2, mul_one]

theorem eq_one_inf (hν : Continuous ν) (hq : ∀ γ ∈ GQ V, ν γ = 1)
    (hs : ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) (a : GA D V) (ha : a ∈ GinfC V) : ν a = 1 := by
  by_contra hne
  obtain ⟨γ, hγ, k, hk, h1, h2⟩ := GlobalTheory.RealApprox.weak_approx_real V a ha {g | ν g ≠ 1}
    (isOpen_ne_fun hν continuous_const) hne
  obtain ⟨-, -, -, -, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨r1, r2, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨γ', hγ'⟩ := (r1 γ).1 hγ
  obtain ⟨l, hl, e⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl _ _ (cF D) V.rank V.gramᵀ ⟨c2, c1, gh, gd⟩ γ'.1 fun x y => by
    have := r2 γ γ' hγ' x y
    rwa [GlobalTheory.UnRep.Space.herm_neg_eq, GlobalTheory.UnRep.Space.herm_neg_eq, neg_inj] at this
  have h3 := eq_one_rat hν hq hs l hl γ (by rw [← e]; exact congrArg Units.val hγ')
  have h4 : γ * k = pInf V γ := ga_ext V
    (by rw [infHom_pInf, map_mul, show infHom V k = 1 from hk, mul_one]) (by rw [finHom_pInf]; exact h2)
  exact h1 (by rw [h4, h3])

theorem tendsto_one_of_finCong {k : ℕ → GA D V} (hk : ∀ n, k n ∈ GfC V) (hc : ∀ n, FinCong V n.factorial (k n)) :
    Tendsto k atTop (𝓝 1) := by
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key : ∀ u : ℕ → GA D V, (∀ n, u n ∈ GfC V) → (∀ n : ℕ, FinCong V n.factorial (u n)) →
      Tendsto (fun n => Formalism.L2.Theta.mt V (u n)) atTop (𝓝 (Formalism.L2.Theta.mt V 1)) := fun u hu hu' => by
    have t : Tendsto (fun n => (finHom V (u n)).1) atTop (𝓝 (finHom V 1).1) := by
      rw [map_one]
      refine GlobalTheory.SplitRepsOpen.tendsto_one_of_cong D.host.F D.host.E _ h3 h4 _ fun n => ?_
      have := hu' n
      unfold GlobalTheory.Member.FinCong at this
      rw [h1] at this
      exact this
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => tendsto_AE ?_
      (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 t i) j)
    refine tendsto_const_nhds.congr fun n => ?_
    change (infHom V 1).1 i j = (infHom V (u n)).1 i j
    rw [map_one, show infHom V (u n) = 1 from hu n]
  exact tendsto_UJ (cA D) (JR (AF D.host.F) V.gram) (key k hk hc)
    ((key (fun n => (k n)⁻¹) (fun n => inv_mem (hk n))
      fun n => GlobalTheory.Member.PrincLevel.finCong_inv (hc n)).trans (by rw [← inv_one]; exact le_rfl))

theorem eq_one_of_suppSplit (hs : ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) {N : ℕ} {h : GA D V}
    (hh : h ∈ GfC V) (h0 : SuppSplit (cF D) N (finHom V h).1) : ν h = 1 := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h0
  refine eq_one_of_idem hs e h1 h2 (fun v hv => (h3 v hv).1) h ?_
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  refine parts_inj D _ _ ?_ ?_
  · have h6 : (Formalism.L2.Theta.mt V h).map (infPart D) = 1 := congrArg Units.val (show infHom V h = 1 from hh)
    rw [RingHom.map_mul, map_sub_one, h6, sub_self, Matrix.zero_apply, mul_zero]
  · rw [RingHom.map_mul, map_sub_one]
    exact congrFun (congrFun h4 i) j

end Char

theorem eq_one_of_rat_of_split : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ γ ∈ GQ V, ν γ = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → ∀ g, ν g = 1 := by
  intro D V ν hν hq hs g
  choose γ hγ a ha h hh k hk e hc hsp using
    fun n : ℕ => GlobalTheory.UnRep.Space.exists_rep_suppSplit D V n.factorial n.factorial_pos g
  have h1 : ∀ n, ν g = ν (k n) := fun n => by
    rw [e n, map_mul, map_mul, map_mul, hq _ (hγ n), eq_one_inf hν hq hs _ (ha n),
      eq_one_of_suppSplit hs (hh n) (hsp n), one_mul, one_mul, one_mul]
  have t := (hν.tendsto _).comp (tendsto_one_of_finCong hk hc)
  rw [map_one] at t
  exact tendsto_nhds_unique (tendsto_const_nhds.congr h1) t

end GlobalTheory.SplitCharTrivial

end
