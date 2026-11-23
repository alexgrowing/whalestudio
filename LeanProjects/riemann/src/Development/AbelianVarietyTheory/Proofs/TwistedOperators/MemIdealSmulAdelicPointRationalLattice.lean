import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepLatIdeal

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem smul_mem_of_mem_smul (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (a : E)
    (ha : ∀ m ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E m * a) (x : Fin n → E) (hx : x ∈ 𝔪 • Λ) :
    a • x ∈ Λ := by
  refine Submodule.smul_induction_on (p := fun w => a • w ∈ Λ) hx (fun m hm y hy => ?_) (fun u v hu hv => ?_)
  · obtain ⟨c, hc⟩ := ha m hm
    have e : a • (m • y) = c • y := by
      rw [← algebraMap_smul E m y, ← algebraMap_smul E c y, smul_smul, hc, mul_comm]
    simp only [e]
    exact Λ.smul_mem c hy
  · simp only [smul_add]
    exact Λ.add_mem hu hv

theorem smul_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (a : E)
    (ha : ∀ m ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E m * a)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) • z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    have hax := smul_mem_of_mem_smul Λ 𝔪 a ha x hx
    change _ ∈ Submodule.span _ _
    refine Submodule.subset_span ⟨a • x, hax, ?_⟩
    funext i
    show (a • x) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (x i ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [smul_add]; exact Submodule.add_mem _ hu hv
  | smul s u _ hu =>
    rw [Subring.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ s hu

theorem eq_zero_of_mem_hatL_bot (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (⊥ : Submodule (𝓞 E) (Fin n → E))) : z = 0 := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    have hx0 : x = 0 := (Submodule.mem_bot _).1 hx
    subst hx0
    funext i
    show (0 : E) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = 0
    exact TensorProduct.zero_tmul _ _
  | zero => rfl
  | add u v _ _ hu hv => rw [hu, hv, add_zero]
  | smul s u _ hu => rw [hu, smul_zero]

theorem nontrivial_af : Nontrivial (Formalism.L2.Herm.Af F) := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' := congrArg (fun b : Formalism.L2.Herm.Af F => b v) h
  simp at h'

theorem mem_smul_span (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (y : Fin n → E)
    (hy : g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    y ∈ 𝔪 • Submodule.span (𝓞 E) {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ} := by
  by_cases h𝔪 : 𝔪 = ⊥
  · subst h𝔪
    have h0 : g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = 0 :=
      eq_zero_of_mem_hatL_bot _ (by simpa [Submodule.bot_smul] using hy)
    have hv : (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = 0 := by
      have := congrArg (fun w => (g⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ w) h0
      simpa [Matrix.mulVec_mulVec] using this
    haveI := nontrivial_af (F := F)
    have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] Formalism.L2.Herm.Af F) :=
      Algebra.TensorProduct.includeLeft_injective (algebraMap F (Formalism.L2.Herm.Af F)).injective
    have hy0 : y = 0 := by
      funext i
      apply hinj
      simpa using congrFun hv i
    subst hy0
    exact Submodule.zero_mem _
  · have hP : (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have h1 : (1 : E) ∈ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
        (((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hP]
      exact FractionalIdeal.one_mem_one _
    have key : ∀ c ∈ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
        (((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E),
        c • y ∈ 𝔪 • Submodule.span (𝓞 E) {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
          Formalism.L2.Herm.hatL (F := F) Λ} := by
      intro c hc
      refine Submodule.mul_induction_on (C := fun c => c • y ∈ 𝔪 • Submodule.span (𝓞 E)
        {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) Λ})
        hc (fun m hm a ha => ?_) (fun u v hu hv => ?_)
      · obtain ⟨m', hm', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
        have hint : ∀ t ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E t * a := by
          intro t ht
          obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
            ((FractionalIdeal.mem_inv_iff hP).1 ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ ht))
          exact ⟨c, by rw [hc, mul_comm]⟩
        have hcol : (fun i => (a • y) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) =
            (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) • (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) := by
          funext i
          show (a * y i) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y i ⊗ₜ[F] 1)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        have haS : g.1 *ᵥ (fun i => (a • y) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
          rw [hcol, Matrix.mulVec_smul]
          exact smul_mem_hatL Λ 𝔪 a hint _ hy
        rw [mul_smul, algebraMap_smul]
        exact Submodule.smul_mem_smul hm' (Submodule.subset_span haS)
      · rw [add_smul]
        exact Submodule.add_mem _ hu hv
    simpa using key 1 h1

end General

theorem mem_smul_latAt : ∀ (D : D7) (V : HSp D) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (x : GA D V) (y : Fin V.rank → D.host.E), (Lev.finE V x⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) → y ∈ 𝔪 • latAt Λ x := by
  intro D V Λ 𝔪 _ x y hy
  unfold GlobalTheory.SepPer.latAt
  exact mem_smul_span Λ 𝔪 (Lev.finE V x⁻¹) y hy

end GlobalTheory.SepLatIdeal

end
