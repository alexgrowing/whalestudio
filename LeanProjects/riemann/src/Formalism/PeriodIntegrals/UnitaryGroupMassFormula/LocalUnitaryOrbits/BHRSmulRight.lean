import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolHOfPi

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem b_fg : (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).FG := by
  let b := RingOfIntegers.basis E
  have h : Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) =
      Submodule.span (v.adicCompletionIntegers F)
        (Set.range fun i => inclR (F := F) (Fv F v) ((b i : 𝓞 E) : E)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      have hx : ((x : 𝓞 E) : E) = ∑ i, (b.repr x i) • ((b i : 𝓞 E) : E) := by
        have := congrArg (fun y : 𝓞 E => (y : E)) (b.sum_repr x)
        simpa using this.symm
      simp only
      rw [hx, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, Set.mem_univ _, rfl⟩
  rw [h]
  exact Submodule.fg_span (Set.finite_range _)

def bAlg : Subalgebra (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.toSubalgebra (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (b_one_mem (E := E) v)
    (fun _ _ hx hy => b_mul_mem v hx hy)

theorem b_int_of_sc {a : Fv F v} (ha : sc (E := E) v a ∈ OEv (E := E) v) : a ∈ v.adicCompletionIntegers F := by
  have hfg : (Subalgebra.toSubmodule (bAlg (E := E) v)).FG := b_fg v
  have hi : IsIntegral (v.adicCompletionIntegers F) (sc (E := E) v a) :=
    IsIntegral.of_mem_of_fg (bAlg (E := E) v) hfg _ ha
  let f : Fv F v →ₐ[v.adicCompletionIntegers F] Fv F v ⊗[F] E :=
    (Algebra.ofId (Fv F v) (Fv F v ⊗[F] E)).restrictScalars (v.adicCompletionIntegers F)
  have hfa : f a = sc (E := E) v a := by rw [b_sc_eq]; rfl
  rw [← hfa] at hi
  have hi' := (isIntegral_algHom_iff f (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 hi
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi'
  rw [← hy]
  exact y.2

theorem b_sigR_mem (σ : E →ₐ[F] E) {z : Fv F v ⊗[F] E} (hz : z ∈ OEv (E := E) v) :
    sigR (Fv F v) σ z ∈ OEv (E := E) v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, -, rfl⟩ := hx
    have hb : IsIntegral ℤ (σ (b : E)) := by
      simpa using (b.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    have e : sigR (Fv F v) σ (inclR (F := F) (Fv F v) (b : E)) =
        inclR (F := F) (Fv F v) ((⟨σ (b : E), hb⟩ : 𝓞 E) : E) := by
      simp [sigR, inclR]
    rw [e]
    exact b_inclR_mem (F := F) (E := E) v ⟨σ (b : E), hb⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have h1 : r • x = algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * x := by
      rw [← Algebra.smul_def]; rfl
    have h2 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * sigR (Fv F v) σ x =
        r • sigR (Fv F v) σ x := by
      rw [← Algebra.smul_def]; rfl
    have h3 : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) := by
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    rw [h1, map_mul, h3, h2]
    exact Submodule.smul_mem _ r hx

theorem b_tr_sc (s : Fv F v) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sc (E := E) v s * w) =
      s * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  rw [b_sc_eq, ← Algebra.smul_def, map_smul, smul_eq_mul]

end Int

section DualW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem b_hR_smul_right (x y : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem b_hR_smul_left (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem b_hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

theorem b_smulF (s : Fv F v) (y : Fin n → Fv F v ⊗[F] E) : s • y = sc (E := E) v s • y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  rfl

theorem b_BR_smul_right {a : ℕ} (s : Fv F v) (X Y : TupV (E := E) v n a) :
    BR (Fv F v) σ J X (s • Y) = s * BR (Fv F v) σ J X Y := by
  simp only [BR, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b_smulF v s (Y i), b_hR_smul_right, b_tr_sc]

theorem b_BR_single {a : ℕ} (i : Fin a) (u : Fin n → Fv F v ⊗[F] E) (Y : TupV (E := E) v n a) :
    BR (Fv F v) σ J (Pi.single i u) Y =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J u (Y i)) := by
  classical
  rw [BR, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, b_hR_zero_left, map_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
theorem dualW_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : DualW σ J ψ v Λ a := by
  classical
  rintro hS ⟨L, hLat, rfl⟩ hSD hU
  have hd0 := dV_ne_zero v
  have hinv : ∀ y, σ (σ y) = y := b_sig_sig σ hS.1
  ext Y
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]
  constructor
  · intro h
    refine ⟨dV v • Y, fun i => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩
    refine (hSD _).2 fun x hx => hP hS hU _ fun c hc => ?_
    have hcx : Pi.single i (sigR (Fv F v) σ c • x) ∈ LamT v (L : Set (Fin n → E)) a := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        exact b_lat_smul v L (b_sigR_mem v σ hc) hx
      · rw [Pi.single_eq_of_ne hj]
        exact Submodule.zero_mem _
    have h1 := h _ hcx
    rw [b_BR_single, b_hR_smul_left, sigR_sigR v σ hinv] at h1
    rw [Pi.smul_apply, b_smulF v, b_hR_smul_right, mul_left_comm, b_tr_sc]
    exact h1
  · rintro ⟨X', hX', rfl⟩ X hX
    rw [b_BR_smul_right, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    exact sum_mem fun i _ => b_trace_mem v ((hSD _).1 (hX' i) _ (hX i))

end DualW

end PI.OmLocU.SdB
