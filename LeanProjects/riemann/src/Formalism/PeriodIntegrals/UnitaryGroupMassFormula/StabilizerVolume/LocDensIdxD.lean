import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxC
import ReciprocityTheory.ResidueCardinality.ArtinOntoB

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

section Surj

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

theorem psi_surj (k0 : Fin 2) (hσ : ∀ x, σ (σ x) = x)
    (hC : ∀ k l, algebraMap F (Fv F v) (Cmat b σ k l) ∈ v.adicCompletionIntegers F)
    (hu : ∀ k, algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) ∈ v.adicCompletionIntegers F)
    (hk0 : b.repr 1 k0 ≠ 0) : Function.Surjective (psi b v σ a k0) := by
  intro g
  have hinv : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  set u : Fv F v := algebraMap F (Fv F v) (b.repr 1 k0) with hu_def
  have hu0 : u ≠ 0 := (map_ne_zero (algebraMap F (Fv F v))).mpr hk0
  let Y : Fin a → Fin a → Fv F v ⊗[F] E := fun i j =>
    (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm ![(g (i, j) : Fv F v), (g (j, i) : Fv F v)]
  let D : Fin a → Fv F v ⊗[F] E := fun i => ((g (i, i) : Fv F v) / u) • (1 : Fv F v ⊗[F] E)
  let M : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then Y i j else if j < i then sigR (Fv F v) σ (Y j i) else D i
  have hD : ∀ i, sigR (Fv F v) σ (D i) = D i := by
    intro i
    simp [D, sigR, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  have hY : ∀ i j k, cr b v (Y i j) k = ![(g (i, j) : Fv F v), (g (j, i) : Fv F v)] k :=
    fun i j k => cr_symm b v _ k
  have hDk : ∀ i k, cr b v (D i) k = (g (i, i) : Fv F v) / u * algebraMap F (Fv F v) (b.repr 1 k) :=
    fun i k => cr_smul_one b v _ k
  have hM : M ∈ HermR (Fv F v) σ a := by
    show ∀ i j, sigR (Fv F v) σ (M j i) = M i j
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [M, h, lt_asymm h, hinv]
    · simp [M, hD]
    · simp [M, h, lt_asymm h]
  have hO : (⟨M, hM⟩ : HermR (Fv F v) σ a) ∈ hermO b v σ a := by
    rw [mem_hermO_iff]
    intro i j k
    rw [crdS_eq]
    show cr b v (M i j) k ∈ _
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [M, if_pos h]
      rw [hY]
      fin_cases k <;> simp
    · simp only [M, lt_irrefl, if_false]
      rw [hDk]
      have e : (g (i, i) : Fv F v) / u * algebraMap F (Fv F v) (b.repr 1 k)
          = (g (i, i) : Fv F v) * algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) := by
        rw [map_div₀, ← hu_def]
        ring
      rw [e]
      exact mul_mem (g _).2 (hu k)
    · simp only [M, if_neg (lt_asymm h), if_pos h]
      rw [cr_sig]
      refine sum_mem fun l _ => mul_mem (hC k l) ?_
      rw [hY]
      fin_cases l <;> simp
  refine ⟨⟨⟨M, hM⟩, hO⟩, ?_⟩
  funext q
  obtain ⟨i, j⟩ := q
  simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with h1 h2
  · apply Subtype.ext
    show cr b v (M i j) 0 = _
    simp only [M, if_pos h1]
    rw [hY]
    simp
  · apply Subtype.ext
    show cr b v (M j i) 1 = _
    simp only [M, if_pos h2]
    rw [hY]
    simp
  · have hij : i = j := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    subst hij
    apply Subtype.ext
    show cr b v (M i i) k0 = _
    simp only [M, lt_irrefl, if_false]
    rw [hDk, ← hu_def]
    exact div_mul_cancel₀ _ hu0

end Surj

end IdxHW

end PI.VolStabS
