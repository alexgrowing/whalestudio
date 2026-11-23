import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA

noncomputable section

namespace PI.IwaMeasEx.Nrm

open NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open Formalism.MainNotions.S

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAd_approx (N : ℕ) (hN : 1 ≤ N) (y : Af F) (hy : y ∈ Formalism.UG.intAd F) :
    ∃ a : 𝓞 F, ∃ z ∈ Formalism.UG.intAd F, y = algebraMap F (Af F) (algebraMap (𝓞 F) F a) + (N : Af F) * z := by
  have hN0 : ((N : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨a, ha⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx (R := 𝓞 F) (K := F) y (fun v => hy v)
    (N : 𝓞 F) hN0
  refine ⟨a, algebraMap F (Af F) ((N : F)⁻¹) * (y - algebraMap F (Af F) (algebraMap (𝓞 F) F a)), fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) ((N : F)⁻¹) *
      (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ∈ v.adicCompletionIntegers F
    have e1 : ((N : F))⁻¹ = (algebraMap (𝓞 F) F (N : 𝓞 F))⁻¹ := by rw [map_natCast]
    rw [e1, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀,
      Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R]
    have hv0 : v.intValuation (N : 𝓞 F) ≠ 0 := v.intValuation_ne_zero _ hN0
    calc (v.intValuation (N : 𝓞 F))⁻¹ * Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
        ≤ (v.intValuation (N : 𝓞 F))⁻¹ * v.intValuation (N : 𝓞 F) := mul_le_mul' le_rfl (ha v)
      _ = 1 := inv_mul_cancel₀ hv0
  · have h1 : (N : Af F) * algebraMap F (Af F) ((N : F)⁻¹) = 1 := by
      rw [← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ hNF, map_one]
    rw [← mul_assoc, h1, one_mul]
    ring

theorem inclE_mem {a : E} (ha : a ∈ Formalism.UG.intOE E) : Formalism.UG.inclE (F := F) (Af F) a ∈ IntAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)

theorem intOE_of_int (a : 𝓞 F) : algebraMap F E (algebraMap (𝓞 F) F a) ∈ Formalism.UG.intOE E := by
  have h : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F a)) :=
    (RingOfIntegers.isIntegral_coe a).map (algebraMap F E).toIntAlgHom
  obtain ⟨y, hy⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 E) |>.1 h
  exact ⟨y, hy⟩

theorem IntAf_approx (N : ℕ) (hN : 1 ≤ N) (x : E ⊗[F] Af F) (hx : x ∈ IntAf F E) :
    ∃ a ∈ Formalism.UG.intOE E, ∃ z ∈ IntAf F E,
      x = Formalism.UG.inclE (F := F) (Af F) a + (N : E ⊗[F] Af F) * z := by
  unfold IntAf Formalism.UG.tensInt at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact ⟨e, he, 0, zero_mem _, by rw [mul_zero, add_zero]; rfl⟩
    · obtain ⟨a, z, hz, rfl⟩ := intAd_approx N hN y hy
      refine ⟨algebraMap F E (algebraMap (𝓞 F) F a), intOE_of_int a, (1 : E) ⊗ₜ[F] z,
        Subring.subset_closure (Or.inr ⟨⟨z, hz⟩, rfl⟩), ?_⟩
      show (1 : E) ⊗ₜ[F] (algebraMap F (Af F) (algebraMap (𝓞 F) F a) + (N : Af F) * z) =
        algebraMap F E (algebraMap (𝓞 F) F a) ⊗ₜ[F] (1 : Af F) + (N : E ⊗[F] Af F) * ((1 : E) ⊗ₜ[F] z)
      rw [TensorProduct.tmul_add, Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.smul_tmul]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | one => exact ⟨1, one_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    obtain ⟨b, hb, w, hw, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, z + w, add_mem hz hw, by rw [map_add]; ring⟩
  | neg x _ hx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    exact ⟨-a, neg_mem ha, -z, neg_mem hz, by rw [map_neg]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    obtain ⟨b, hb, w, hw, rfl⟩ := hy
    refine ⟨a * b, mul_mem ha hb,
      Formalism.UG.inclE (F := F) (Af F) a * w + z * Formalism.UG.inclE (F := F) (Af F) b + (N : E ⊗[F] Af F) * z * w,
      add_mem (add_mem (mul_mem (inclE_mem ha) hw) (mul_mem hz (inclE_mem hb)))
        (mul_mem (mul_mem (natCast_mem _ N) hz) hw), by rw [map_mul]; ring⟩

variable (F E) in

def trT : E ⊗[F] Af F →ₗ[F] Af F :=
  TensorProduct.lift ((LinearMap.lsmul F (Af F)).comp (Algebra.trace F E))

theorem trT_tmul (e : E) (t : Af F) :
    trT F E (e ⊗ₜ[F] t) = algebraMap F (Af F) (Algebra.trace F E e) * t := by
  simp [trT, Algebra.smul_def]

theorem algebraMap_int_mem_intAd (c : 𝓞 F) :
    algebraMap F (Af F) (algebraMap (𝓞 F) F c) ∈ Formalism.UG.intAd F := fun v =>
  Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.int_R v c

theorem trT_mem (z : E ⊗[F] Af F) (hz : z ∈ IntAf F E) : trT F E z ∈ Formalism.UG.intAd F := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let f : 𝓞 E →ₐ[ℤ] E ⊗[F] Af F :=
    ((Algebra.TensorProduct.includeLeftRingHom).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  let g : Formalism.UG.intAd F →ₐ[ℤ] E ⊗[F] Af F :=
    ((Algebra.TensorProduct.includeRight (R := F) (A := E) (B := Af F)).toRingHom.comp
      (Formalism.UG.intAd F).subtype).toIntAlgHom
  let ψ := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have hle : IntAf F E ≤ ψ.toRingHom.range := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, ⟨o, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)
    · refine ⟨o ⊗ₜ 1, ?_⟩
      show ψ (o ⊗ₜ 1) = _
      rw [Algebra.TensorProduct.lift_tmul]
      show (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] (((1 : Formalism.UG.intAd F) : Af F))) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, OneMemClass.coe_one]
    · refine ⟨1 ⊗ₜ y, ?_⟩
      show ψ (1 ⊗ₜ y) = _
      rw [Algebra.TensorProduct.lift_tmul]
      show (algebraMap (𝓞 E) E 1 ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] ((y : Af F))) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, map_one]
  obtain ⟨w, rfl⟩ := hle hz
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o y =>
    have h1 : ψ.toRingHom (o ⊗ₜ y) = (algebraMap (𝓞 E) E o) ⊗ₜ[F] (y : Af F) := by
      show ψ (o ⊗ₜ y) = _
      rw [Algebra.TensorProduct.lift_tmul]
      show (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] ((y : Af F))) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1, trT_tmul]
    have hint : IsIntegral ℤ (Algebra.trace F E (algebraMap (𝓞 E) E o)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    obtain ⟨c, hc⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 F) |>.1 hint
    rw [← hc]
    exact mul_mem (algebraMap_int_mem_intAd c) y.2
  | add x y hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy

theorem mem_intOE (e : E) (he : Formalism.UG.inclE (F := F) (Af F) e ∈ IntAf F E) : e ∈ Formalism.UG.intOE E := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let S : Subring E := (IntAf F E).comap (Formalism.UG.inclE (F := F) (Af F))
  have hOE : ∀ o : 𝓞 E, algebraMap (𝓞 E) E o ∈ S := fun o =>
    Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)
  have htrF : ∀ z ∈ S, Algebra.trace F E z ∈ (algebraMap (𝓞 F) F).range := by
    intro z hz
    refine Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.mem_of_isInt (R := 𝓞 F) _ (fun v => ?_)
    have h1 := trT_mem _ hz
    have h2 : Formalism.UG.inclE (F := F) (Af F) z = z ⊗ₜ[F] (1 : Af F) := rfl
    rw [h2, trT_tmul, mul_one] at h1
    exact h1 v
  have htrQ : ∀ z ∈ S, ∃ k : ℤ, Algebra.trace ℚ E z = k := by
    intro z hz
    obtain ⟨c, hc⟩ := htrF z hz
    rw [← Algebra.trace_trace (S := F), ← hc]
    have hint : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F c)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe c)
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact ⟨k, by rw [← hk]; simp⟩
  let b := NumberField.integralBasis E
  have hB : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  let bd := (Algebra.traceForm ℚ E).dualBasis hB b
  have hSN : ∀ z ∈ S, z ∈ Submodule.span ℤ (Set.range bd) := by
    intro z hz
    rw [← bd.sum_repr z]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    obtain ⟨k, hk⟩ := htrQ (z * b i) (S.mul_mem hz (by rw [integralBasis_apply]; exact hOE _))
    rw [hk, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let SA : Subalgebra ℤ E :=
    { S with algebraMap_mem' := fun k => by rw [algebraMap_int_eq, eq_intCast]; exact intCast_mem S k }
  have hfg : (Subalgebra.toSubmodule SA).FG :=
    (Submodule.fg_span (Set.finite_range bd)).of_le fun z hz => hSN z hz
  have hint : IsIntegral ℤ e := IsIntegral.of_mem_of_fg SA hfg e he
  obtain ⟨y, hy⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 E) |>.1 hint
  exact ⟨y, hy⟩

end Gen

section Unit

open Formalism.L2.S.S7.GLOne

variable (I : AutInst)

abbrev iE : I.E →+* AEf I := Formalism.UG.inclE (F := I.F) (Af I.F)

def cid (u : (AEf I)ˣ) : Submodule (𝓞 I.E) I.E where
  carrier := {e | ((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I e ∈ IntAf I.F I.E}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add, mul_add] at *
    exact add_mem ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro r e he
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_def, map_mul, mul_left_comm]
    exact mul_mem (inclE_mem (RingHom.mem_range_self _ r)) he

theorem mem_cid {u : (AEf I)ˣ} {e : I.E} : e ∈ cid I u ↔ ((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I e ∈ IntAf I.F I.E :=
  Iff.rfl

theorem idl_eq (u : (AEf I)ˣ) : idl I u = cid I u :=
  Submodule.span_eq (cid I u)

theorem exists_nat_two (u : (AEf I)ˣ) : ∃ N : ℕ, 1 ≤ N ∧ (N : AEf I) * u ∈ IntAf I.F I.E ∧
    (N : AEf I) * ((u⁻¹ : (AEf I)ˣ) : AEf I) ∈ IntAf I.F I.E := by
  obtain ⟨a, ha, hua⟩ := AfT.exists_nat_mul_mem I (u : AEf I)
  obtain ⟨b, hb, hub⟩ := AfT.exists_nat_mul_mem I ((u⁻¹ : (AEf I)ˣ) : AEf I)
  refine ⟨a * b, Nat.mul_pos ha hb, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_comm (a : AEf I), mul_assoc]
    exact mul_mem (natCast_mem _ _) hua
  · rw [Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ _) hub

theorem mem_uO (u : (AEf I)ˣ) : ∃ N : ℕ, 1 ≤ N ∧ (N : I.E) ∈ cid I u ∧ ∀ x : AEf I,
    ((u⁻¹ : (AEf I)ˣ) : AEf I) * x ∈ IntAf I.F I.E →
    ∃ b ∈ cid I u, ∃ z ∈ IntAf I.F I.E, x = iE I b + iE I N * z := by
  obtain ⟨N, hN, hu, hui⟩ := exists_nat_two I u
  refine ⟨N, hN, ?_, fun x hx => ?_⟩
  · show ((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I N ∈ IntAf I.F I.E
    rw [map_natCast, mul_comm]
    exact hui
  · have hNx : (N : AEf I) * x ∈ IntAf I.F I.E := by
      have e : (N : AEf I) * x = ((N : AEf I) * u) * (((u⁻¹ : (AEf I)ˣ) : AEf I) * x) := by
        rw [mul_assoc, ← mul_assoc (u : AEf I), Units.mul_inv, one_mul]
      rw [e]
      exact mul_mem hu hx
    obtain ⟨a, -, z, hz, he⟩ := IntAf_approx (N * N) (Nat.mul_pos hN hN) _ hNx
    have hNE : (N : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hNA : IsUnit (N : AEf I) := AfT.isUnit_natCast I N hN
    have h1 : (N : AEf I) * iE I (a / N) = iE I a := by
      have : (N : I.E) * (a / N) = a := by field_simp
      rw [← map_natCast (iE I) N, ← map_mul, this]
    have hx' : x = iE I (a / N) + (N : AEf I) * z := by
      apply hNA.mul_left_cancel
      rw [he, mul_add, h1, Nat.cast_mul]
      ring
    refine ⟨a / N, ?_, z, hz, by rw [map_natCast]; exact hx'⟩
    show ((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I (a / N) ∈ IntAf I.F I.E
    have e : ((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I (a / N) =
        ((u⁻¹ : (AEf I)ˣ) : AEf I) * x - ((N : AEf I) * ((u⁻¹ : (AEf I)ˣ) : AEf I)) * z := by
      rw [hx']; ring
    rw [e]
    exact sub_mem hx (mul_mem hui hz)

theorem isFractional_cid (u : (AEf I)ˣ) : IsFractional (𝓞 I.E)⁰ (cid I u) := by
  obtain ⟨N, hN, hu, -⟩ := exists_nat_two I u
  have hN0 : ((N : ℕ) : 𝓞 I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨(N : 𝓞 I.E), mem_nonZeroDivisors_of_ne_zero hN0, fun b hb => ?_⟩
  have h : Formalism.UG.inclE (F := I.F) (Af I.F) ((N : I.E) * b) ∈ IntAf I.F I.E := by
    have e : iE I ((N : I.E) * b) = ((N : AEf I) * u) * (((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I b) := by
      rw [map_mul, map_natCast, mul_assoc, ← mul_assoc (u : AEf I), Units.mul_inv, one_mul]
    rw [e]
    exact mul_mem hu hb
  obtain ⟨y, hy⟩ := mem_intOE _ h
  refine ⟨y, ?_⟩
  rw [Algebra.smul_def, map_natCast]
  exact hy

def FI (u : (AEf I)ˣ) : FractionalIdeal (𝓞 I.E)⁰ I.E := ⟨cid I u, isFractional_cid I u⟩

theorem coe_FI (u : (AEf I)ˣ) : (FI I u : Submodule (𝓞 I.E) I.E) = cid I u := rfl

theorem FI_ne_zero (u : (AEf I)ˣ) : FI I u ≠ 0 := by
  obtain ⟨N, hN, hNm, -⟩ := mem_uO I u
  intro h
  have hm : (N : I.E) ∈ (FI I u : Submodule (𝓞 I.E) I.E) := hNm
  rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at hm
  exact (Nat.cast_ne_zero.mpr (by omega) : (N : I.E) ≠ 0) hm

theorem nrmF_eq (u : (AEf I)ˣ) : nrmF I u = ((FractionalIdeal.absNorm (FI I u) : ℚ) : ℝ)⁻¹ := by
  have h := idl_eq I u
  have hf : IsFractional (𝓞 I.E)⁰ (idl I u) := h ▸ isFractional_cid I u
  have e : (⟨idl I u, hf⟩ : FractionalIdeal (𝓞 I.E)⁰ I.E) = FI I u := Subtype.ext h
  unfold nrmF
  rw [dif_pos hf, e]

theorem nrmF_pos (u : (AEf I)ˣ) : 0 < nrmF I u := by
  rw [nrmF_eq]
  have h0 : FractionalIdeal.absNorm (FI I u) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact FI_ne_zero I u
  have h1 : (0 : ℚ) < FractionalIdeal.absNorm (FI I u) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm h0)
  positivity

theorem mem_of_sum (𝔡 : FractionalIdeal (𝓞 I.E)⁰ I.E) (d : I.E) (hd : d ∈ (𝔡 : Submodule (𝓞 I.E) I.E))
    (hd0 : d ≠ 0) {k : ℕ} (c : Fin k → I.E) (hc : ∀ i, c i ∈ (𝔡 : Submodule (𝓞 I.E) I.E))
    (s : Fin k → AEf I) (hs : ∀ i, s i ∈ IntAf I.F I.E) (x : I.E)
    (hx : iE I x = ∑ i, iE I (c i) * s i) : x ∈ (𝔡 : Submodule (𝓞 I.E) I.E) := by
  obtain ⟨r, hr, hrint⟩ := 𝔡.isFractional
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  set ρ : I.E := algebraMap (𝓞 I.E) I.E r with hρ
  have hρ0 : ρ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 I.E) I.E)).mpr hr0
  have hint : ∀ b ∈ (𝔡 : Submodule (𝓞 I.E) I.E), ρ * b ∈ Formalism.UG.intOE I.E := by
    intro b hb
    obtain ⟨y, hy⟩ := hrint b hb
    refine ⟨y, ?_⟩
    rw [hy, Algebra.smul_def]

  obtain ⟨rd, hrd⟩ := hint d hd
  have hrd0 : rd ≠ 0 := by
    rintro rfl
    rw [map_zero] at hrd
    exact mul_ne_zero hρ0 hd0 hrd.symm
  set M : ℕ := Ideal.absNorm (Ideal.span {rd}) with hMdef
  have hM : 1 ≤ M := by
    have : Ideal.absNorm (Ideal.span {rd}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hrd0
    omega
  obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {rd}))
  have hME : (M : I.E) = ρ * d * algebraMap (𝓞 I.E) I.E c0 := by
    have := congrArg (algebraMap (𝓞 I.E) I.E) hc0
    rw [map_mul, map_natCast, hrd] at this
    rw [← this, mul_comm]
  have hMne : (M : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)

  choose a ha z hz hsz using fun i => IntAf_approx (F := I.F) (E := I.E) M hM (s i) (hs i)
  have hx2 : iE I (ρ * (x - ∑ i, c i * a i)) = (M : AEf I) * ∑ i, iE I (ρ * c i) * z i := by
    rw [map_mul, map_sub, hx, map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsz i]
    simp only [map_mul]
    ring
  set y : I.E := ρ * (x - ∑ i, c i * a i) with hy
  have hyM : iE I (y / M) ∈ IntAf I.F I.E := by
    have e : iE I (y / M) = ∑ i, iE I (ρ * c i) * z i := by
      have hMA : IsUnit (M : AEf I) := AfT.isUnit_natCast I M hM
      apply hMA.mul_left_cancel
      rw [← hx2, ← map_natCast (iE I) M, ← map_mul]
      congr 1
      field_simp
    rw [e]
    exact sum_mem fun i _ => mul_mem (inclE_mem (hint _ (hc i))) (hz i)
  obtain ⟨w, hw⟩ := mem_intOE _ hyM

  have hsub : x - ∑ i, c i * a i = (c0 * w) • d := by
    rw [Algebra.smul_def, map_mul, hw]
    have : y = (M : I.E) * (y / M) := by field_simp
    have hyρ : x - ∑ i, c i * a i = y / ρ := by rw [hy]; field_simp
    rw [hyρ, this, hME]
    field_simp
  have hsum : ∑ i, c i * a i ∈ (𝔡 : Submodule (𝓞 I.E) I.E) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨ai, hai⟩ := ha i
    rw [← hai, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hc i)
  have : x = (x - ∑ i, c i * a i) + ∑ i, c i * a i := by ring
  rw [this, hsub]
  exact add_mem (Submodule.smul_mem _ _ hd) hsum

theorem FI_mul (u v : (AEf I)ˣ) : FI I (u * v) = FI I u * FI I v := by
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_mul, coe_FI, coe_FI, coe_FI]
  apply le_antisymm
  · intro x hx
    rw [mem_cid] at hx
    obtain ⟨Nu, hNu, hNum, hu⟩ := mem_uO I u
    obtain ⟨Nv, hNv, hNvm, hv⟩ := mem_uO I v
    have hy : ((v⁻¹ : (AEf I)ˣ) : AEf I) * (((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I x) ∈ IntAf I.F I.E := by
      rw [← mul_assoc, ← Units.val_mul, ← mul_inv_rev]; exact hx
    obtain ⟨b, hb, z, hz, hbz⟩ := hv _ hy
    have h1 : ((u⁻¹ : (AEf I)ˣ) : AEf I) * (u : AEf I) ∈ IntAf I.F I.E := by
      rw [Units.inv_mul]; exact one_mem _
    have h2 : ((u⁻¹ : (AEf I)ˣ) : AEf I) * ((u : AEf I) * z) ∈ IntAf I.F I.E := by
      rw [← mul_assoc, Units.inv_mul, one_mul]; exact hz
    obtain ⟨b1, hb1, z1, hz1, e1⟩ := hu _ h1
    obtain ⟨b2, hb2, z2, hz2, e2⟩ := hu _ h2
    have hxe : iE I x = (u : AEf I) * (((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I x) := by
      rw [← mul_assoc, Units.mul_inv, one_mul]
    have key : iE I x = ∑ i, iE I (![b1 * b, (Nu : I.E) * b, b2 * (Nv : I.E), (Nu : I.E) * Nv] i) *
        ![1, z1, 1, z2] i := by
      simp only [Fin.sum_univ_four, Matrix.cons_val]
      rw [hxe, hbz]
      have e3 : (u : AEf I) * (iE I b + iE I (Nv : I.E) * z) = iE I b * (u : AEf I) + iE I (Nv : I.E) * ((u : AEf I) * z) := by
        ring
      rw [e3, e2, e1]
      simp only [map_mul]
      ring
    have hd0 : ((Nu : I.E) * Nv) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
    have hP : ∀ {p q : I.E}, p ∈ cid I u → q ∈ cid I v → p * q ∈ ((FI I u * FI I v : FractionalIdeal (𝓞 I.E)⁰ I.E) : Submodule (𝓞 I.E) I.E) := by
      intro p q hp hq
      rw [FractionalIdeal.coe_mul]
      exact Submodule.mul_mem_mul hp hq
    have hcs : ∀ i, ![b1 * b, (Nu : I.E) * b, b2 * (Nv : I.E), (Nu : I.E) * Nv] i ∈
        ((FI I u * FI I v : FractionalIdeal (𝓞 I.E)⁰ I.E) : Submodule (𝓞 I.E) I.E) := by
      intro i
      match i with
      | 0 => exact hP hb1 hb
      | 1 => exact hP hNum hb
      | 2 => exact hP hb2 hNvm
      | 3 => exact hP hNum hNvm
    have hss : ∀ i, ![1, z1, 1, z2] i ∈ IntAf I.F I.E := by
      intro i
      match i with
      | 0 => exact one_mem _
      | 1 => exact hz1
      | 2 => exact one_mem _
      | 3 => exact hz2
    have hmem := mem_of_sum I (FI I u * FI I v) ((Nu : I.E) * Nv) (hP hNum hNvm) hd0 _ hcs _ hss x key
    rwa [FractionalIdeal.coe_mul] at hmem
  · refine Submodule.mul_le.2 fun m hm n hn => ?_
    rw [mem_cid] at *
    have e : (((u * v)⁻¹ : (AEf I)ˣ) : AEf I) * iE I (m * n) =
        (((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I m) * (((v⁻¹ : (AEf I)ˣ) : AEf I) * iE I n) := by
      rw [mul_inv_rev, Units.val_mul, map_mul]; ring
    rw [e]
    exact mul_mem hm hn

theorem nrmF_mul (u v : (AEf I)ˣ) : nrmF I (u * v) = nrmF I u * nrmF I v := by
  rw [nrmF_eq, nrmF_eq, nrmF_eq, FI_mul, map_mul, Rat.cast_mul, mul_inv]

end Unit

end PI.IwaMeasEx.Nrm

end
