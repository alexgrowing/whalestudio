import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_eq_add (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let τ : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hinv) (AlgHom.ext hinv)
  have hτ : τ ≠ 1 := by
    intro h
    obtain ⟨x0, hx0⟩ := hnt
    apply hx0
    have := congrArg (fun f : E ≃ₐ[F] E => f x0) h
    simpa [τ] using this
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    refine le_antisymm (hfin ▸ AlgEquiv.card_le) ?_
    have h2 : ({1, τ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair hτ.symm
    rw [← h2]
    exact Finset.card_le_univ _
  have : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hfin])
  rw [trace_eq_sum_automorphisms]
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, τ} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hτ.symm, hcard])).symm
  rw [hu, Finset.sum_pair hτ.symm]
  rfl

variable (v : HeightOneSpectrum (𝓞 F))

theorem trace_inclR (x : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      algebraMap F (Fv F v) (Algebra.trace F E x) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e : Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      (Algebra.lmul F E x).baseChange (Fv F v) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext a e
    simp [inclR]
  rw [Algebra.trace_apply, e, LinearMap.trace_baseChange]
  rfl

theorem trace_v (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (w : Fv F v ⊗[F] E) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c e =>
    have e1 : c ⊗ₜ[F] e = c • inclR (F := F) (Fv F v) e := by
      simp [inclR, TensorProduct.smul_tmul']
    have hL : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c ⊗ₜ[F] e) =
        algebraMap F (Fv F v) (Algebra.trace F E e) * c := by
      rw [e1, map_smul, trace_inclR, smul_eq_mul, mul_comm]
    rw [hL, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      ← Algebra.smul_def, TensorProduct.smul_tmul]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    rw [← TensorProduct.tmul_add, ← trace_eq_add σ hinv hnt hfin e, Algebra.algebraMap_eq_smul_one]
  | add w1 w2 h1 h2 => rw [map_add, map_add, h1, h2, map_add]; abel

theorem sigR_sigR (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (w : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (sigR (Fv F v) σ w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c e => simp [sigR, hinv]
  | add w1 w2 h1 h2 => rw [map_add, map_add, h1, h2]

theorem b_inclR_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

theorem b_smul_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : c • x ∈ OEv (E := E) v :=
  Submodule.smul_mem (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (⟨c, hc⟩ : v.adicCompletionIntegers F) hx

theorem b_one_mem : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  simpa using b_inclR_mem (E := E) v 1

theorem b_sc_eq (c : Fv F v) : sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := rfl

theorem b_sc_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) : sc (E := E) v c ∈ OEv (E := E) v := by
  rw [b_sc_eq, Algebra.algebraMap_eq_smul_one]
  exact b_smul_mem v hc (b_one_mem v)

theorem b_mul_mem {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      have := b_inclR_mem (E := E) v (a * b)
      simpa using this
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y1 y2 _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x1 x2 _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

theorem b_trace_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x ∈ v.adicCompletionIntegers F := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    rw [trace_inclR]
    have hint : IsIntegral ℤ (Algebra.trace F E (a : E)) := Algebra.isIntegral_trace a.2
    exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v ⟨_, hint⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x1 x2 _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul c x _ h =>
    have e : c • x = (c : Fv F v) • x := rfl
    rw [e, map_smul, smul_eq_mul]
    exact (v.adicCompletionIntegers F).mul_mem _ _ c.2 h

theorem b_lat_smul {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {o : Fv F v ⊗[F] E} (ho : o ∈ OEv (E := E) v)
    {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v (L : Set (Fin n → E))) :
    o • x ∈ latLoc (E := E) v (L : Set (Fin n → E)) := by
  unfold OEv at ho
  rw [SetLike.mem_coe] at ho
  induction ho using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, -, rfl⟩ := hy
    unfold latLoc at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      have hel : e • l ∈ L := L.smul_mem e hl
      have eq : inclR (F := F) (Fv F v) (e : E) • ratV (F := F) (Fv F v) l =
          ratV (F := F) (Fv F v) (e • l) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, ratV]
        rw [← map_mul]
        rfl
      rw [eq]
      exact Submodule.subset_span ⟨_, hel, rfl⟩
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add z w _ _ hz hw =>
      rw [smul_add]
      exact Submodule.add_mem _ hz hw
    | smul r z _ hz =>
      rw [smul_comm]
      exact Submodule.smul_mem _ r hz
  | zero =>
    rw [zero_smul]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [add_smul]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ r hy

theorem b_sig_sig (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h4, h4, star_star]

theorem b_sig_nt (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hn
  push Not at hn
  have hs : σ = AlgHom.id F E := AlgHom.ext hn
  obtain ⟨-, htc, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h4 τ x
    rw [hs, AlgHom.id_apply] at this
    rw [starRingEnd_apply]; exact this.symm
  exact InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 hr)

end Gen

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def TrPerf : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ z : Fv F v ⊗[F] E,
    (∀ x ∈ OEv (E := E) v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * z) ∈ v.adicCompletionIntegers F) →
    z ∈ OEv (E := E) v

end Steps

end PI.OmLocU.SdB
