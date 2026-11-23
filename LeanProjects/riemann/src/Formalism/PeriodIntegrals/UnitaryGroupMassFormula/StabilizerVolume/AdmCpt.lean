import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNeSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear

noncomputable section

namespace PI.VolStabS.AdmissibleCompactSupport

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open PI.VolStabS PI.VolStabS.PositiveNearLattice Set Filter
open scoped TensorProduct RestrictedProduct

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_finBox {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hc : ∀ v, IsCompact (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsCompact {x : Af F | ∀ v, x v ∈ D v} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | D v = (v.adicCompletionIntegers F : Set (Fv F v))}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hf
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) =>
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let K : Set (Πʳ v, [R v, A v]_[𝓟 S]) := {x | ∀ v, x v ∈ D v}
  have hK : IsCompact K := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have e : ((↑) : Πʳ v, [R v, A v]_[𝓟 S] → ∀ v, R v) '' K = Set.pi univ D := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩ v _
        exact hx v
      · intro hg
        refine ⟨⟨g, ?_⟩, fun v => hg v (mem_univ v), rfl⟩
        rw [eventually_principal]
        intro v hv
        have h := hg v (mem_univ v)
        rwa [show D v = _ from hv] at h
    rw [e]
    exact isCompact_univ_pi hc
  have e : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion R A hS '' K := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      rw [eventually_principal]
      intro v hv
      have h := hx v
      rwa [show D v = _ from hv] at h
    · rintro ⟨y, hy, rfl⟩ v
      exact hy v
  rw [e]
  exact hK.image (RestrictedProduct.continuous_inclusion hS)

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem crd_projV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F))
    (i : Fin a) (j : Fin M) (k : Fin d) :
    crd b (Fv F v) (projV v Y i j) k = (crd b (Af F) (Y i j) k) v := by
  simp only [projV]
  rw [crd_map]
  rfl

theorem eventually_mem_latV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) :
    ∀ᶠ v in cofinite, projV v Y ∈ latV b v := by
  have h : ∀ (i : Fin a) (j : Fin M) (k : Fin d), ∀ᶠ v in cofinite,
      (crd b (Af F) (Y i j) k) v ∈ v.adicCompletionIntegers F :=
    fun i j k => (crd b (Af F) (Y i j) k).2
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
    h i j k] with v hv
  intro i j k
  have := crd_projV b Y v i j k
  simp only [crd] at this
  rw [this]
  exact hv i j k

variable {a M : ℕ} (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)

theorem mulSupport_finite
    (hae : ∀ᶠ v in cofinite, Φv v = (latV b v).indicator 1) (Y : Fin a → Fin M → Af F ⊗[F] E) :
    (Function.mulSupport fun v => Φv v (projV v Y)).Finite := by
  refine (Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b Y))).subset ?_
  intro v hv h
  apply hv
  simp only
  rw [h.1, Set.indicator_of_mem h.2]
  rfl

theorem factor_ne_zero (hae : ∀ᶠ v in cofinite, Φv v = (latV b v).indicator 1)
    (Y : Fin a → Fin M → Af F ⊗[F] E) (h : ∏ᶠ v, Φv v (projV v Y) ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) : Φv v (projV v Y) ≠ 0 := by
  have hfin := mulSupport_finite b Φv hae Y
  rw [finprod_eq_prod _ hfin] at h
  by_cases hv : v ∈ hfin.toFinset
  · exact Finset.prod_ne_zero_iff.1 h v hv
  · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
    rw [hv]
    exact one_ne_zero

end PI.VolStabS.AdmissibleCompactSupport

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.VolStabS.AdmissibleCompactSupport

end PI.VolStabS
