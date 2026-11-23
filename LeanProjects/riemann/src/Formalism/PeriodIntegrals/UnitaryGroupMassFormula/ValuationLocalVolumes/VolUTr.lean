import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUTr

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
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let σ' : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun y => hinv y) (AlgHom.ext fun y => hinv y)
  have hσ' : ∀ y, σ' y = σ y := fun y => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ σ' := by
    obtain ⟨y, hy⟩ := hnt
    intro h
    apply hy
    have h2 := congrArg (fun f : E ≃ₐ[F] E => f y) h
    simp only [AlgEquiv.one_apply] at h2
    rw [← hσ', ← h2]
  have hle : Nat.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← hfin]
    calc Nat.card (E ≃ₐ[F] E) ≤ Nat.card (E →ₐ[F] E) :=
          Nat.card_le_card_of_injective (fun f => (f : E →ₐ[F] E))
            (fun f g h => AlgEquiv.coe_algHom_injective h)
      _ ≤ Module.finrank F E := card_algHom_le_finrank F E E
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ'} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair hne, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hle
  haveI hgal : IsGalois F E := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [hfin]
    apply le_antisymm hle
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, huniv, Finset.card_pair hne]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair hne]
  rfl

variable (v : HeightOneSpectrum (𝓞 F))

theorem sc_eq (c : Fv F v) : sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := rfl

theorem inclR_mem' (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v := by
  exact Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

theorem oev_smul' {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : c • x ∈ OEv (E := E) v := by
  exact Submodule.smul_mem _ (⟨c, hc⟩ : v.adicCompletionIntegers F) hx

theorem one_mem : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have h := inclR_mem' v (1 : 𝓞 E)
  simpa using h

theorem int_mem (r : 𝓞 F) : algebraMap F (Fv F v) (r : F) ∈ v.adicCompletionIntegers F := by
  have h := v.coe_mem_adicCompletionIntegers (K := F) r
  convert h using 1
  exact (IsScalarTower.algebraMap_apply (𝓞 F) F (Fv F v) r).symm

theorem inclR_alg (a : F) : inclR (F := F) (Fv F v) (algebraMap F E a) =
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) a) := by
  show (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E) (algebraMap F E a) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F (Fv F v) (Fv F v ⊗[F] E)]

theorem alg_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E := E) v := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact oev_smul' v hc (one_mem v)

theorem mul_mem {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  have hx' : x ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) := hx
  have hy' : y ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) := hy
  show x * y ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)
  clear hx hy
  induction hx' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction hy' using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      exact Submodule.subset_span ⟨a * b, Set.mem_univ _, by simp⟩
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hy
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add x z _ _ hx hz =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

theorem trace_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x ∈ v.adicCompletionIntegers F := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hgen : ∀ a : 𝓞 E, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) (a : E)) ∈
      v.adicCompletionIntegers F := by
    intro a
    have ht : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((1 : Fv F v) ⊗ₜ (a : E)) =
        algebraMap F (Fv F v) (Algebra.trace F E (a : E)) := by
      rw [Algebra.trace_apply, Algebra.trace_apply]
      have h : Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) ((1 : Fv F v) ⊗ₜ (a : E)) =
          (Algebra.lmul F E (a : E)).baseChange (Fv F v) := by
        ext k
        simp
      rw [h, LinearMap.trace_baseChange]
    have hint : IsIntegral ℤ (Algebra.trace F E (a : E)) := Algebra.isIntegral_trace a.2
    have h2 := int_mem v (⟨_, hint⟩ : 𝓞 F)
    show Algebra.trace _ _ ((1 : Fv F v) ⊗ₜ (a : E)) ∈ _
    rw [ht]
    exact h2
  have hx' : x ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact hgen a
  | zero =>
    rw [map_zero]
    exact (v.adicCompletionIntegers F).zero_mem
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, map_smul, smul_eq_mul]
    exact (v.adicCompletionIntegers F).mul_mem _ _ c.2 hy

theorem trace_v (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (w : Fv F v ⊗[F] E) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have h1 : ∀ e : E, algebraMap (Fv F v) (Fv F v ⊗[F] E)
      (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((1 : Fv F v) ⊗ₜ e)) =
      (1 : Fv F v) ⊗ₜ e + (1 : Fv F v) ⊗ₜ σ e := by
    intro e
    have ht : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((1 : Fv F v) ⊗ₜ e) =
        algebraMap F (Fv F v) (Algebra.trace F E e) := by
      rw [Algebra.trace_apply, Algebra.trace_apply]
      have h : Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) ((1 : Fv F v) ⊗ₜ e) =
          (Algebra.lmul F E e).baseChange (Fv F v) := by
        ext k
        simp
      rw [h, LinearMap.trace_baseChange]
    rw [ht, ← inclR_alg v, trace_eq_add σ hinv hnt hfin e, map_add]
    rfl
  have hL : (Algebra.linearMap (Fv F v) (Fv F v ⊗[F] E)) ∘ₗ
        (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) =
      LinearMap.id + σ.toLinearMap.baseChange (Fv F v) := by
    ext e
    simpa using h1 e
  have hw := LinearMap.congr_fun hL w
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply, LinearMap.add_apply,
    LinearMap.id_apply] at hw
  rw [hw]
  congr 1

theorem dual_mem (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (θ t : 𝓞 E) (ht : σ (θ : E) = (t : E)) (e : 𝓞 F)
    (he : ((θ : E) - t) ^ 2 = algebraMap F E (e : F)) (hev : e ∉ v.asIdeal) (z : Fv F v ⊗[F] E)
    (hz : ∀ x ∈ OEv (E := E) v,
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * z) ∈ v.adicCompletionIntegers F) :
    z ∈ OEv (E := E) v := by
  set A := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z with hAdef
  set B := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) (θ : E) * z) with hBdef
  have hA : A ∈ v.adicCompletionIntegers F := by simpa using hz 1 (one_mem v)
  have hB : B ∈ v.adicCompletionIntegers F := hz _ (inclR_mem' v θ)
  have tA := trace_v v σ hinv hnt hfin z
  have tB := trace_v v σ hinv hnt hfin (inclR (F := F) (Fv F v) (θ : E) * z)
  have hsθ : sigR (Fv F v) σ (inclR (F := F) (Fv F v) (θ : E)) = inclR (F := F) (Fv F v) (t : E) := by
    simp [sigR, inclR, ht]
  set Δ := inclR (F := F) (Fv F v) ((θ : E) - t) with hΔ
  have key : Δ * z = algebraMap (Fv F v) (Fv F v ⊗[F] E) B -
      inclR (F := F) (Fv F v) (t : E) * algebraMap (Fv F v) (Fv F v ⊗[F] E) A := by
    rw [tA, tB, map_mul, hsθ, hΔ, map_sub]
    ring
  have hΔ2 : Δ * Δ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (e : F)) := by
    rw [hΔ, ← map_mul, ← sq, he, inclR_alg]
  have hΔm : Δ ∈ OEv (E := E) v := by
    have := inclR_mem' (E := E) v (θ - t)
    simpa [hΔ] using this
  have hmem : Δ * (algebraMap (Fv F v) (Fv F v ⊗[F] E) B -
      inclR (F := F) (Fv F v) (t : E) * algebraMap (Fv F v) (Fv F v ⊗[F] E) A) ∈ OEv (E := E) v :=
    mul_mem v hΔm (Submodule.sub_mem _ (alg_mem v hB)
      (mul_mem v (inclR_mem' v t) (alg_mem v hA)))
  have hval : Valued.v (algebraMap F (Fv F v) (e : F)) = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F e)
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hev] at h
    exact h
  have he0 : algebraMap F (Fv F v) (e : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hval; exact zero_ne_one hval
  have hinvm : (algebraMap F (Fv F v) (e : F))⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have hzeq : z = (algebraMap F (Fv F v) (e : F))⁻¹ • (Δ * (algebraMap (Fv F v) (Fv F v ⊗[F] E) B -
      inclR (F := F) (Fv F v) (t : E) * algebraMap (Fv F v) (Fv F v ⊗[F] E) A)) := by
    rw [← key, ← mul_assoc, hΔ2, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ he0, one_smul]
  rw [hzeq]
  exact oev_smul' v hinvm hmem

end Gen

end TrW

open TrW in

theorem annX_of {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (hC : Formalism.L2.SG.Pf.NcVal.CondAll) : AnnX X ψ := by
  intro hψ hs v y
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨P, hPmax, hPv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]
      exact bot_le)
  obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
  set σ := X.B.I.cm.sig with hσ
  have hσx : ∀ x, σ x = star x := fun x => rfl
  have hinv : ∀ y, σ (σ y) = y := fun y => by rw [hσx, hσx, star_star]
  have ht : σ (θ : X.B.I.E) = (t : X.B.I.E) := by rw [hσx]; exact htθ.symm
  have hne : (θ : X.B.I.E) ≠ t := by
    intro h
    apply hnot
    have : θ - t = 0 := by ext; simp [h]
    rw [this]; exact P.zero_mem
  have hnt : ∃ x, σ x ≠ x := ⟨θ, by rw [ht]; exact fun h => hne h.symm⟩
  have hfix : star (((θ : X.B.I.E) - t) ^ 2) = ((θ : X.B.I.E) - t) ^ 2 := by
    have htθ' : (t : X.B.I.E) = star (θ : X.B.I.E) := htθ
    have h1 : star (t : X.B.I.E) = θ := by rw [htθ', star_star]
    rw [star_pow, star_sub, h1, ← htθ']
    ring
  obtain ⟨f, hf⟩ := (X.B.I.cm.fixed _).1 hfix
  have hint : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E f) := by
    rw [hf]
    have h1 : (((θ - t) ^ 2 : 𝓞 X.B.I.E) : X.B.I.E) = ((θ : X.B.I.E) - t) ^ 2 := by push_cast; ring
    rw [← h1]
    exact RingOfIntegers.isIntegral_coe _
  have hfint : IsIntegral ℤ f :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E)
      (algebraMap X.B.I.F X.B.I.E).injective).mp hint
  set e : 𝓞 X.B.I.F := ⟨f, hfint⟩ with he
  have he2 : ((θ : X.B.I.E) - t) ^ 2 = algebraMap X.B.I.F X.B.I.E (e : X.B.I.F) := hf.symm
  have hev : e ∉ v.asIdeal := by
    intro hm
    rw [← hPv] at hm
    have hm' : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e ∈ P := hm
    have heq : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e = (θ - t) ^ 2 := by
      apply RingOfIntegers.coe_injective
      rw [← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E,
        IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E, map_pow, map_sub]
      exact he2.symm
    rw [heq] at hm'
    exact hnot (hPmax.isPrime.mem_of_pow_mem 2 hm')
  have hfin := X.B.I.cm.deg2
  have hTr : ∀ x, Algebra.trace (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (x * (sc (E := X.B.I.E) v (dV v) * y)) =
      dV v * Algebra.trace (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (x * y) := by
    intro x
    rw [sc_eq, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]
  constructor
  · intro h
    refine dual_mem v σ hinv hnt hfin θ t ht e he2 hev _ fun x hx => ?_
    rw [hTr]
    refine (hC X.B.I.F X.B.I.cm.totReal ψ hψ hs v _).1 fun s hs' => ?_
    have e3 : Algebra.trace (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (x * y) * s =
        Algebra.trace (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((s • x) * y) := by
      rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
    rw [e3]
    exact h _ (oev_smul' v hs' hx)
  · intro h x hx
    have hm := trace_mem v (mul_mem v hx h)
    rw [hTr] at hm
    have := (hC X.B.I.F X.B.I.cm.totReal ψ hψ hs v _).2 hm 1 (one_mem _)
    simpa using this

end Formalism.L2.SG.Pf.NcVal.VolUTr
