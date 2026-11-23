import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsFurther
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem exists_nat_mul_isIntegral (e : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * e) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  have hpos : 0 < y.natAbs := Int.natAbs_pos.2 hy0
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos hpos hpos, ?_⟩
  have e1 : ((y.natAbs * y.natAbs : ℕ) : E) * e = (y : E) * ((y : E) * e) := by
    have h2 := Int.natAbs_mul_self' y
    rw [← mul_assoc, ← Int.cast_natCast, Nat.cast_mul, h2, Int.cast_mul]
  rw [e1]
  rw [zsmul_eq_mul] at h
  refine IsIntegral.mul ?_ h
  simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := y))

theorem exists_common_nat {M : Type} [AddCommMonoid M] {ι : Type} [Fintype ι] (S : AddSubmonoid M) (x : ι → M)
    (h : ∀ i, ∃ n : ℕ, 0 < n ∧ n • x i ∈ S) : ∃ n : ℕ, 0 < n ∧ ∀ i, n • x i ∈ S := by
  classical
  choose n hn hx using h
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
  exact nsmul_mem (hx i) _

theorem exists_nat_mul_mem_intAf (z : E ⊗[F] 𝔸) :
    ∃ n : ℕ, 0 < n ∧ (n : E ⊗[F] 𝔸) * z ∈ Formalism.L2.Herm.intAf F E := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    obtain ⟨n, hn, he⟩ := exists_nat_mul_isIntegral e
    obtain ⟨d, hd, ha⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_adele (F := F) a
    refine ⟨n * d, Nat.mul_pos hn hd, ?_⟩
    have e1 : ((n * d : ℕ) : E ⊗[F] 𝔸) * (e ⊗ₜ[F] a) =
        (((n : E) * e) ⊗ₜ[F] (1 : 𝔸)) * ((1 : E) ⊗ₜ[F] ((d : 𝔸) * a)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Nat.cast_mul,
        Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def',
        mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
    rw [e1]
    refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨(n : E) * e, ⟨⟨_, he⟩, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨(d : 𝔸) * a, fun v => Subring.mem_iInf.1 ha v⟩, rfl⟩))
  | add x y hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have e1 : ((n₁ * n₂ : ℕ) : E ⊗[F] 𝔸) * (x + y) =
        (n₂ : E ⊗[F] 𝔸) * ((n₁ : E ⊗[F] 𝔸) * x) + (n₁ : E ⊗[F] 𝔸) * ((n₂ : E ⊗[F] 𝔸) * y) := by
      push_cast; ring
    rw [e1]
    exact add_mem (mul_mem (natCast_mem _ _) hx) (mul_mem (natCast_mem _ _) hy)

theorem exists_nsmul_mem_of_mem_span {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (Lb : Set (Fin N → E))) : ∃ n : ℕ, 0 < n ∧ n • v ∈ Lb := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.NatMulIsIntegralSatakeParameters.exists_nsmul_mem
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.NatMulIsIntegralSatakeParameters.exists_nsmul_mem
  | exact @_root_.GlobalTheory.NatMulIsIntegralSatakeParameters.exists_nsmul_mem
  | exact _root_.GlobalTheory.NatMulIsIntegralSatakeParameters.exists_nsmul_mem
  | (apply _root_.GlobalTheory.NatMulIsIntegralSatakeParameters.exists_nsmul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIsIntegralSatakeParameters.exists_nsmul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIsIntegralSatakeParameters.exists_nsmul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIsIntegralSatakeParameters.exists_nsmul_mem ..)

end GlobalTheory.TwV.Xc

namespace GlobalTheory.TwV.Xc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

open Matrix

theorem exists_nsmul_mem_hatL {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E))
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) (z : Fin N → E ⊗[F] 𝔸) :
    ∃ n : ℕ, 0 < n ∧ n • z ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := exists_common_nat Lb.toAddSubmonoid (fun i : Fin N => (Pi.single i (1 : E) : Fin N → E))
    fun i => exists_nsmul_mem_of_mem_span Lb (by rw [hspan]; exact Submodule.mem_top)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_common_nat (Formalism.L2.Herm.intAf F E).toAddSubgroup.toAddSubmonoid z
    fun i => by
      obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_intAf (F := F) (E := E) (z i)
      exact ⟨n, hn, by rw [nsmul_eq_mul]; exact h⟩
  refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, ?_⟩
  have e1 : (d₁ * d₂) • z = ∑ i, (⟨d₂ • z i, h₂ i⟩ : Formalism.L2.Herm.intAf F E) •
      (fun j => inclE (F := F) 𝔸 ((d₁ • (Pi.single i (1 : E) : Fin N → E)) j)) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp only [Submonoid.smul_def, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, nsmul_eq_mul, mul_one, map_natCast]
      show _ = ((d₂ : E ⊗[F] 𝔸) * z j) * _
      rw [Nat.cast_mul]; ring
    · intro i _ hij
      show (d₂ • z i) * inclE (F := F) 𝔸 ((d₁ • (Pi.single i (1 : E) : Fin N → E)) j) = 0
      rw [Pi.smul_apply, Pi.single_eq_of_ne hij.symm, smul_zero, map_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [e1]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h₁ i, rfl⟩)

theorem exists_nsmul_mulVec_mem_hatL {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) (M : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) :
    ∃ D : ℕ, 0 < D ∧ ∀ u ∈ Formalism.L2.Herm.hatL (F := F) Lb, D • (M *ᵥ u) ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  haveI : Module.Finite ℤ Lb := Module.Finite.trans (𝓞 E) Lb
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Lb)
  obtain ⟨D, hD, hDj⟩ := exists_common_nat (Formalism.L2.Herm.hatL (F := F) Lb).toAddSubmonoid
    (fun j => M *ᵥ fun i => inclE (F := F) 𝔸 ((s j : Fin N → E) i))
    fun j => exists_nsmul_mem_hatL Lb hspan _
  refine ⟨D, hD, fun u hu => ?_⟩
  let Q : Submodule (Formalism.L2.Herm.intAf F E) (Fin N → E ⊗[F] 𝔸) :=
    { carrier := {u | D • (M *ᵥ u) ∈ Formalism.L2.Herm.hatL (F := F) Lb}
      add_mem' := fun {a b} ha hb => by
        show D • (M *ᵥ (a + b)) ∈ Formalism.L2.Herm.hatL (F := F) Lb
        have ha : D • (M *ᵥ a) ∈ Formalism.L2.Herm.hatL (F := F) Lb := ha
        have hb : D • (M *ᵥ b) ∈ Formalism.L2.Herm.hatL (F := F) Lb := hb
        rw [Matrix.mulVec_add, smul_add]; exact add_mem ha hb
      zero_mem' := by
        show D • (M *ᵥ 0) ∈ Formalism.L2.Herm.hatL (F := F) Lb
        rw [Matrix.mulVec_zero, smul_zero]; exact zero_mem _
      smul_mem' := fun t a ha => by
        show D • (M *ᵥ (t • a)) ∈ Formalism.L2.Herm.hatL (F := F) Lb
        have ha : D • (M *ᵥ a) ∈ Formalism.L2.Herm.hatL (F := F) Lb := ha
        rw [Submonoid.smul_def, Matrix.mulVec_smul, smul_comm]
        exact Submodule.smul_mem _ t ha }
  have hle : Formalism.L2.Herm.hatL (F := F) Lb ≤ Q := by
    show Submodule.span _ _ ≤ Q
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (⟨w, hw⟩ : Lb) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hw'
    have e : w = ∑ j, m j • (s j : Fin N → E) := by simpa using (congrArg Subtype.val hm).symm
    have e2 : (fun i => inclE (F := F) 𝔸 (w i)) = ∑ j, m j • fun i => inclE (F := F) 𝔸 ((s j : Fin N → E) i) := by
      funext i
      rw [e]
      simp [Finset.sum_apply, map_sum, map_zsmul]
    show (fun i => inclE (F := F) 𝔸 (w i)) ∈ Q
    rw [e2]
    have hj : ∀ j, (fun i => inclE (F := F) 𝔸 ((s j : Fin N → E) i)) ∈ Q := fun j => hDj j
    exact Submodule.sum_mem Q fun j _ => Q.toAddSubgroup.zsmul_mem (hj j) (m j)
  exact hle hu

end GlobalTheory.TwV.Xc

namespace GlobalTheory.TwV.Xc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

open Matrix

theorem exists_pow_div_mem (w : HeightOneSpectrum (𝓞 F)) {D : ℕ} (hD : 0 < D) :
    ∃ m : ℕ, ∀ c : 𝓞 F, c ∈ w.asIdeal ^ m →
      algebraMap F (w.adicCompletion F) (c : F) / (D : w.adicCompletion F) ∈ w.adicCompletionIntegers F := by
  have hD0 : (D : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  set L := WithZero.log (w.intValuation (D : 𝓞 F))
  refine ⟨(-L).toNat, fun c hc => ?_⟩
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem w c _).2 hc
  have h2 : WithZero.exp (-(((-L).toNat : ℕ) : ℤ)) ≤ w.intValuation (D : 𝓞 F) := by
    rw [← WithZero.exp_log (HeightOneSpectrum.intValuation_ne_zero w _ hD0), WithZero.exp_le_exp]
    have := Int.self_le_toNat (-L)
    omega
  have hc' : w.intValuation c ≤ w.intValuation (D : 𝓞 F) := h1.trans h2
  have hDw : (D : w.adicCompletion F) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
  have e1 : Valued.v (algebraMap F (w.adicCompletion F) (c : F)) = w.intValuation c := by
    rw [Formalism.UG.P.levelaf_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  have e2 : Valued.v (D : w.adicCompletion F) = w.intValuation (D : 𝓞 F) := by
    rw [← map_natCast (algebraMap F (w.adicCompletion F)), Formalism.UG.P.levelaf_valued_algebraMap,
      ← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap]
  rw [e1, e2]
  exact div_le_one_of_le₀ hc' zero_le'

end GlobalTheory.TwV.Xc

namespace GlobalTheory.TwV.Xc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

open Matrix

theorem inclE_algebraMap (R : Type) [CommRing R] [Algebra F R] (a : F) :
    inclE (F := F) R (algebraMap F E a) = (1 : E) ⊗ₜ[F] algebraMap F R a := by
  show algebraMap F E a ⊗ₜ[F] (1 : R) = _
  rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']

theorem prV_inclE (v : HeightOneSpectrum (𝓞 F)) (a : E) :
    prV (E := E) v (inclE (F := F) 𝔸 a) = inclE (F := F) (v.adicCompletion F) a := by
  show Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v) (a ⊗ₜ[F] (1 : 𝔸)) = a ⊗ₜ[F] 1
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem smul_mulVec_mem_hatL_of_oneOff {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) (w : HeightOneSpectrum (𝓞 F))
    (K : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) (hK : ∀ w', w' ≠ w → K.map (prV (E := E) w') = 1) :
    ∃ m : ℕ, ∀ c : 𝓞 F, c ∈ w.asIdeal ^ m → ∀ u ∈ Formalism.L2.Herm.hatL (F := F) Lb,
      inclE (F := F) 𝔸 (algebraMap F E (c : F)) • (K *ᵥ u) ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  haveI := hfin
  obtain ⟨D, hD, hDK⟩ := exists_nsmul_mulVec_mem_hatL Lb hfin hspan K
  obtain ⟨m, hm⟩ := exists_pow_div_mem w hD
  refine ⟨m, fun c hc u hu => ?_⟩
  have hu' := (GlobalTheory.LatticeStabLocal.mem_latS_adele_iff Lb u).1 hu
  have hy' := (GlobalTheory.LatticeStabLocal.mem_latS_adele_iff Lb _).1 (hDK u hu)
  have hcE : IsIntegral ℤ (algebraMap F E (c : F)) := c.2.map (algebraMap F E).toIntAlgHom
  refine (GlobalTheory.LatticeStabLocal.mem_latS_adele_iff Lb _).2 fun v => ?_
  by_cases hv : v = w
  · subst hv
    set t := algebraMap F (v.adicCompletion F) (c : F) / (D : v.adicCompletion F)
    have ht : t ∈ v.adicCompletionIntegers F := hm c hc
    have hDw : (D : v.adicCompletion F) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
    have e1 : (fun i => prV (E := E) v ((inclE (F := F) 𝔸 (algebraMap F E (c : F)) • (K *ᵥ u)) i)) =
        (⟨(1 : E) ⊗ₜ[F] t, Subring.subset_closure (Or.inr ⟨⟨t, ht⟩, rfl⟩)⟩ :
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) •
        (fun i => prV (E := E) v ((D • (K *ᵥ u)) i)) := by
      funext i
      show _ = ((1 : E) ⊗ₜ[F] t) * prV (E := E) v ((D • (K *ᵥ u)) i)
      rw [Pi.smul_apply, smul_eq_mul, map_mul, prV_inclE, inclE_algebraMap, Pi.smul_apply, map_nsmul,
        nsmul_eq_mul, ← mul_assoc]
      congr 1
      rw [Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_mul_cancel₀ _ hDw]
    rw [e1]
    exact Submodule.smul_mem _ _ (hy' v)
  · have e1 : (fun i => prV (E := E) v ((inclE (F := F) 𝔸 (algebraMap F E (c : F)) • (K *ᵥ u)) i)) =
        (⟨inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)),
          Subring.subset_closure (Or.inl ⟨⟨_, ⟨⟨_, hcE⟩, rfl⟩⟩, rfl⟩)⟩ :
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) •
        (fun i => prV (E := E) v (u i)) := by
      funext i
      show _ = inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) * prV (E := E) v (u i)
      rw [Pi.smul_apply, smul_eq_mul, map_mul, prV_inclE]
      congr 1
      have h2 := congrFun (GlobalTheory.LatticeStabLocal.prV_mulVec v K u) i
      rw [h2, hK v hv, Matrix.one_mulVec]
    rw [e1]
    exact Submodule.smul_mem _ _ (hu' v)

end GlobalTheory.TwV.Xc

namespace GlobalTheory.TwV.Xc

open Matrix

theorem latAd_smul_mem_of_sameOff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (w : HeightOneSpectrum (𝓞 F)) (x x' : GL (Fin N) (AfE F E)), SameOff w x x' → ∃ m : ℕ, ∀ c : 𝓞 F, c ∈ w.asIdeal ^ m → ∀ y ∈ latAd x Lb, (algebraMap F E (c : F)) • y ∈ latAd x' Lb := by
  intro F E _ _ _ _ _ N Lb hfin hspan w x x' hx
  set K : Matrix (Fin N) (Fin N) (AfE F E) := ((x'⁻¹ * x : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)) with hKdef
  have hK : ∀ w', w' ≠ w → K.map (prV (E := E) w') = 1 := by
    intro w' hw'
    have h := hx w' hw'
    have h1 : Formalism.UG.bc (prV (E := E) w') (x'⁻¹ * x) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    show (Formalism.UG.bc (prV (E := E) w') (x'⁻¹ * x)).val = 1
    rw [h1]
    rfl
  obtain ⟨m, hm⟩ := smul_mulVec_mem_hatL_of_oneOff Lb hfin hspan w K hK
  refine ⟨m, fun c hc y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem z hz =>
    apply Submodule.subset_span
    have hz : ((x⁻¹ : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)) *ᵥ
        (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) ∈ Formalism.L2.Herm.hatL (F := F) Lb := hz
    show ((x'⁻¹ : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)) *ᵥ
        (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap F E (c : F) • z) a)) ∈
          Formalism.L2.Herm.hatL (F := F) Lb
    have e1 : (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap F E (c : F) • z) a)) =
        inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap F E (c : F)) •
          (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) := by
      funext a
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    have e2 : ((x'⁻¹ : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)) *ᵥ
        (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) =
        K *ᵥ (((x⁻¹ : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)) *ᵥ
          (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a))) := by
      rw [Matrix.mulVec_mulVec, hKdef, Units.val_mul, Matrix.mul_assoc, ← Units.val_mul x, mul_inv_cancel,
        Units.val_one, Matrix.mul_one]
    rw [e1, Matrix.mulVec_smul, e2]
    exact hm c hc _ hz
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul b z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ b hz

end GlobalTheory.TwV.Xc
