import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AnnX {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ (v : PlX X) (y : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    (∀ x ∈ OEv (E := X.B.I.E) v,
        psiV X.B.I.F ψ v (Algebra.trace (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (x * y)) = 1) ↔
      sc (E := X.B.I.E) v (dV v) * y ∈ OEv (E := X.B.I.E) v

namespace TrW

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_eq_add (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hfin
  obtain ⟨x0, hx0⟩ := hnt
  let σe : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hinv) (AlgHom.ext hinv)
  have hne : (1 : E ≃ₐ[F] E) ≠ σe := by
    intro h
    apply hx0
    have := congrArg (fun τ : E ≃ₐ[F] E => τ x0) h
    simpa [σe] using this.symm
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := hfin ▸ AlgEquiv.card_le
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σe} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Finset.card_pair hne]
    exact hle
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, huniv, Finset.card_pair hne, hfin])
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair hne]
  simp [σe]

variable (v : HeightOneSpectrum (𝓞 F))

theorem sc_eq (c : Fv F v) : sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := rfl

theorem inclR_mem' (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v := Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

theorem oev_smul' {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : c • x ∈ OEv (E := E) v := by
  change x ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hx
  change c • x ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)
  exact Submodule.smul_mem _ (⟨c, hc⟩ : v.adicCompletionIntegers F) hx

theorem one_mem : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  simpa using inclR_mem' (F := F) (E := E) v (1 : 𝓞 E)

theorem int_mem (r : 𝓞 F) : algebraMap F (Fv F v) (r : F) ∈ v.adicCompletionIntegers F := by
  first
    | exact v.coe_mem_adicCompletionIntegers r
    | simpa using v.coe_mem_adicCompletionIntegers (K := F) r
    | exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v r

theorem inclR_alg (a : F) : inclR (F := F) (Fv F v) (algebraMap F E a) =
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) a) := by
  show (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E) (algebraMap F E a) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F (Fv F v) (Fv F v ⊗[F] E)]

theorem alg_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E := E) v := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact oev_smul' (F := F) (E := E) v hc (one_mem (F := F) (E := E) v)

theorem mul_mem {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  simp only [OEv, SetLike.mem_coe] at hx hy ⊢
  have key : ∀ a : 𝓞 E, ∀ y ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ),
      inclR (F := F) (Fv F v) (a : E) * y ∈ Submodule.span (v.adicCompletionIntegers F)
        ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, -, rfl⟩ := hz
      exact Submodule.subset_span ⟨a * b, Set.mem_univ _, by simp [map_mul]⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [mul_add]; exact Submodule.add_mem _ hx hz
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, -, rfl⟩ := hz
    exact key a y hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem trace_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x ∈ v.adicCompletionIntegers F := by
  simp only [OEv, SetLike.mem_coe] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, -, rfl⟩ := hz
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR (v := v)]
    have hi : IsIntegral ℤ (Algebra.trace F E (a : E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe a)
    exact int_mem (F := F) v ⟨_, hi⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul c x _ hx =>
    show Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((c : Fv F v) • x) ∈ _
    rw [map_smul, smul_eq_mul]
    exact MulMemClass.mul_mem c.2 hx

theorem trace_v (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (w : Fv F v ⊗[F] E) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c e =>
    have ht := trace_eq_add σ hinv hnt hfin e
    have e1 : (c ⊗ₜ[F] e : Fv F v ⊗[F] E) = c • inclR (F := F) (Fv F v) e := by
      simp [inclR, TensorProduct.smul_tmul']
    have e2 : sigR (Fv F v) σ (c ⊗ₜ[F] e) = c ⊗ₜ[F] σ e := by
      simp [sigR, Algebra.TensorProduct.map_tmul]
    rw [e2, ← TensorProduct.tmul_add, ← ht, Algebra.algebraMap_eq_smul_one (A := E) (Algebra.trace F E e),
      ← TensorProduct.smul_tmul, e1, map_smul, PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR (v := v),
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1
    rw [smul_eq_mul, Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    abel

theorem dual_mem (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (θ t : 𝓞 E) (ht : σ (θ : E) = (t : E)) (e : 𝓞 F)
    (he : ((θ : E) - t) ^ 2 = algebraMap F E (e : F)) (hev : e ∉ v.asIdeal) (z : Fv F v ⊗[F] E)
    (hz : ∀ x ∈ OEv (E := E) v,
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * z) ∈ v.adicCompletionIntegers F) :
    z ∈ OEv (E := E) v := by
  have hsub : ∀ x y : Fv F v ⊗[F] E, x ∈ OEv (E := E) v → y ∈ OEv (E := E) v →
      x - y ∈ OEv (E := E) v := by
    intro x y hx hy
    simp only [OEv, SetLike.mem_coe] at hx hy ⊢
    exact Submodule.sub_mem _ hx hy
  have hθ := inclR_mem' (F := F) (E := E) v θ
  have ht' := inclR_mem' (F := F) (E := E) v t
  have hσθ : sigR (Fv F v) σ (inclR (F := F) (Fv F v) (θ : E)) = inclR (F := F) (Fv F v) (t : E) := by
    simp [sigR, inclR, Algebra.TensorProduct.map_tmul, ht]
  have hA := trace_v v σ hinv hnt hfin (inclR (F := F) (Fv F v) (θ : E) * z)
  have hB := trace_v v σ hinv hnt hfin z
  rw [RingHom.map_mul (sigR (Fv F v) σ), hσθ] at hA
  have hδ : (inclR (F := F) (Fv F v) (θ : E) - inclR (F := F) (Fv F v) (t : E)) * z =
      algebraMap (Fv F v) (Fv F v ⊗[F] E)
          (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) (θ : E) * z)) -
        inclR (F := F) (Fv F v) (t : E) *
          algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z) := by
    rw [hA, hB]
    ring
  have hδ2 : (inclR (F := F) (Fv F v) (θ : E) - inclR (F := F) (Fv F v) (t : E)) *
      (inclR (F := F) (Fv F v) (θ : E) - inclR (F := F) (Fv F v) (t : E)) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (e : F)) := by
    rw [← inclR_alg (F := F) (E := E) v, ← he, sq, map_mul, map_sub]
  have hAm : algebraMap (Fv F v) (Fv F v ⊗[F] E)
      (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) (θ : E) * z)) ∈ OEv (E := E) v :=
    alg_mem (F := F) (E := E) v (hz _ hθ)
  have hBm : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z) ∈
      OEv (E := E) v := by
    have := hz 1 (one_mem (F := F) (E := E) v)
    rw [one_mul] at this
    exact alg_mem (F := F) (E := E) v this
  have hmem : algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (e : F)) * z ∈ OEv (E := E) v := by
    rw [← hδ2, mul_assoc, hδ]
    exact mul_mem (F := F) (E := E) v (hsub _ _ hθ ht')
      (hsub _ _ hAm (mul_mem (F := F) (E := E) v ht' hBm))
  have hne : algebraMap F (Fv F v) (e : F) ≠ 0 := by
    intro h0
    apply hev
    have h1 : (e : F) = 0 := (algebraMap F (Fv F v)).injective (by rw [h0, map_zero])
    have h2 : e = 0 := RingOfIntegers.coe_eq_zero_iff.mp h1
    rw [h2]
    exact v.asIdeal.zero_mem
  have hval : Valued.v (algebraMap F (Fv F v) (e : F)) = 1 := by
    have h1 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v (e : F)
    have h2 : IsDedekindDomain.HeightOneSpectrum.valuation F v (e : F) = 1 := by
      rw [show (e : F) = algebraMap (𝓞 F) F e from rfl,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hev]
    rw [← h2, ← h1]
    rfl
  have hinvm : (algebraMap F (Fv F v) (e : F))⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  rw [← Algebra.smul_def] at hmem
  have hz' : z = (algebraMap F (Fv F v) (e : F))⁻¹ • ((algebraMap F (Fv F v) (e : F)) • z) := by
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hz']
  exact oev_smul' (F := F) (E := E) v hinvm hmem

end Gen

end TrW

open TrW in

theorem annX_of {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (hC : CondAll) : AnnX X ψ := by
  intro hψ hstd v y
  obtain ⟨hun, htr, hdeg, hfix⟩ := X.B.I.cm
  let σ : X.B.I.E →ₐ[X.B.I.F] X.B.I.E :=
    { toRingHom := starRingEnd X.B.I.E
      commutes' := fun a => (hfix _).mpr ⟨a, rfl⟩ }
  have hinv : ∀ a, σ (σ a) = a := fun a => star_star a
  obtain ⟨Q, hQmax, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
    (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have h1 : algebraMap (𝓞 X.B.I.E) X.B.I.E (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) x) = 0 := by
        rw [hx, map_zero]
      rw [← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E,
        IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E] at h1
      have h2 : algebraMap (𝓞 X.B.I.F) X.B.I.F x = 0 :=
        (algebraMap X.B.I.F X.B.I.E).injective (by rw [h1, map_zero])
      have h3 : x = 0 := RingOfIntegers.coe_eq_zero_iff.mp h2
      rw [h3]
      exact v.asIdeal.zero_mem)
  obtain ⟨θ, t, ht, hθt⟩ := hun.2.2 Q hQmax
  have ht' : (t : X.B.I.E) = star (θ : X.B.I.E) := ht
  have hσθ : σ (θ : X.B.I.E) = t := ht'.symm
  have hnt : ∃ x, σ x ≠ x := by
    refine ⟨(θ : X.B.I.E), fun h => hθt ?_⟩
    have h1 : θ = t := RingOfIntegers.coe_injective (by
      have h' := h
      rw [hσθ] at h'
      exact h'.symm)
    rw [h1, sub_self]
    exact Q.zero_mem
  have hfixd : star (((θ : X.B.I.E) - t) ^ 2) = ((θ : X.B.I.E) - t) ^ 2 := by
    rw [star_pow, star_sub, ← ht', ht', star_star]
    ring
  obtain ⟨f, hf⟩ := (hfix _).mp hfixd
  have hfi : IsIntegral ℤ f := by
    have h1 := RingOfIntegers.isIntegral_coe ((θ - t) ^ 2)
    push_cast at h1
    rw [← hf] at h1
    exact (isIntegral_algebraMap_iff (algebraMap X.B.I.F X.B.I.E).injective).mp h1
  let e : 𝓞 X.B.I.F := ⟨f, hfi⟩
  have he : ((θ : X.B.I.E) - t) ^ 2 = algebraMap X.B.I.F X.B.I.E (e : X.B.I.F) := hf.symm
  have hev : e ∉ v.asIdeal := by
    intro hmem
    apply hθt
    rw [← hQv, Ideal.mem_comap] at hmem
    have h2 : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e = (θ - t) ^ 2 := by
      apply RingOfIntegers.coe_injective
      rw [← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E,
        IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E]
      push_cast
      exact he.symm
    rw [h2] at hmem
    exact hQmax.isPrime.mem_of_pow_mem 2 hmem
  have hlin : ∀ (c : Fv X.B.I.F v) (x w : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
      Algebra.trace (Fv X.B.I.F v) _ (x * (algebraMap (Fv X.B.I.F v) _ c * w)) =
        c * Algebra.trace (Fv X.B.I.F v) _ (x * w) := by
    intro c x w
    rw [mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hCv := fun x => hC X.B.I.F htr ψ hψ hstd v x
  rw [sc_eq]
  constructor
  · intro h
    refine dual_mem v σ hinv hnt hdeg θ t hσθ e he hev _ (fun x hx => ?_)
    rw [hlin]
    refine (hCv _).mp (fun c hc => ?_)
    rw [mul_comm, ← hlin, ← Algebra.smul_def]
    rw [show x * (c • y) = c • x * y by rw [smul_mul_assoc, mul_smul_comm]]
    exact h _ (oev_smul' v hc hx)
  · intro h x hx
    have h1 : dV v * Algebra.trace (Fv X.B.I.F v) _ (x * y) ∈ v.adicCompletionIntegers X.B.I.F := by
      rw [← hlin]
      exact trace_mem v (mul_mem v hx h)
    have := (hCv _).mpr h1 1 (v.adicCompletionIntegers X.B.I.F).one_mem
    rwa [mul_one] at this

end Formalism.L2.SG.Pf.NcVal
