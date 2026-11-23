import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SdUniq

theorem not_selfDual_one (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    (k : Measure V) : ¬ SelfDual k (fun _ _ => (1 : ℂ)) := by
  intro hk
  haveI := hk.1
  obtain ⟨h, hh⟩ := exists_ne (0 : V)
  obtain ⟨g, hg1, hg0, hgc, -⟩ := exists_continuous_one_zero_of_isCompact (X := V)
    (s := {0}) (t := {-h}) isCompact_singleton isClosed_singleton
    (by simpa [eq_comm] using hh)
  let g' : V → ℂ := fun x => ((g x : ℝ) : ℂ)
  have hc' : Continuous g' := Complex.continuous_ofReal.comp g.continuous
  have hs' : HasCompactSupport g' := hgc.comp_left (g := Complex.ofReal) (by simp)
  let Φ : V → ℂ := fun x => g' x - g' (x - h)
  have hc2 : Continuous fun x => g' (x - h) := hc'.comp (by fun_prop)
  have hs2 : HasCompactSupport fun x => g' (x - h) :=
    hs'.comp_homeomorph (Homeomorph.subRight h)
  have hΦc : Continuous Φ := hc'.sub hc2
  have hΦs : HasCompactSupport Φ := hs'.sub hs2
  have e : ∫ x, Φ x * (1 : ℂ) ∂k = 0 := by
    simp only [mul_one, Φ]
    rw [integral_sub (hc'.integrable_of_hasCompactSupport hs')
      (hc2.integrable_of_hasCompactSupport hs2), integral_sub_right_eq_self g' h, sub_self]
  have hI : Integrable (fun _ : V => ∫ x, Φ x * (1 : ℂ) ∂k) k := by
    rw [e]
    exact integrable_zero V ℂ k
  have key : ∫ _ : V, (∫ x, Φ x * (1 : ℂ) ∂k) * (1 : ℂ) ∂k = Φ (-0) := hk.2 Φ hΦc hΦs hI 0
  rw [e, zero_mul, integral_zero, neg_zero] at key
  have h1 : g 0 = 1 := hg1 rfl
  have h2 : g (-h) = 0 := hg0 rfl
  have h3 : Φ 0 = 1 := by simp [Φ, g', h1, h2]
  rw [h3] at key
  exact zero_ne_one key

variable (F : Type) [Field F] [NumberField F]

noncomputable def chiV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)

theorem chiV_apply (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    chiV F ψ v t = psiV F ψ v t := rfl

theorem selfDual_unique_coord : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 → ∀ μ ν : Measure (ι → Fv F v), SelfDual μ (fun x y => psiV F ψ v (x ⬝ᵥ (A.map (algebraMap F (Fv F v)) *ᵥ y))) → SelfDual ν (fun x y => psiV F ψ v (x ⬝ᵥ (A.map (algebraMap F (Fv F v)) *ᵥ y))) → μ = ν := by
  intro F _ _ ψ hψ v k hk ι _ _ A hA hdet μ ν hμ hν
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hc : Continuous (chiV F ψ v) :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖chiV F ψ v t‖ = 1 := fun t => hψ.2.1 _
  have hne : ∃ t, chiV F ψ v t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine not_selfDual_one (Fv F v) k ?_
    have e : (fun s t : Fv F v => psiV F ψ v (s * t)) = fun _ _ => (1 : ℂ) := by
      funext s t
      exact hcon _
    rwa [e] at hk
  set M : Matrix ι ι (Fv F v) := A.map (algebraMap F (Fv F v)) with hM
  have hMs : Mᵀ = M := by
    rw [hM, ← Matrix.transpose_map, hA.eq]
  have hMd : M.det ≠ 0 := by
    have : M.det = algebraMap F (Fv F v) A.det := by
      rw [hM]; exact (RingHom.map_det (algebraMap F (Fv F v)) A).symm
    rw [this]
    exact (map_ne_zero _).2 hdet
  have hs : ∀ x y, Matrix.toBilin' M x y = Matrix.toBilin' M y x := by
    intro x y
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, dotProduct_comm,
      ← Matrix.mulVec_transpose, hMs]
  have hn : ∀ x, (∀ y, Matrix.toBilin' M x y = 0) → x = 0 := by
    intro x hx
    refine Matrix.eq_zero_of_vecMul_eq_zero hMd ?_
    refine dotProduct_eq_zero _ fun w => ?_
    rw [← Matrix.dotProduct_mulVec, ← Matrix.toBilin'_apply']
    exact hx w
  have huniq := GlobalTheory.SelfDualFinite.existsUnique_of_bilin v (chiV F ψ v) hc hu hne (ι → Fv F v)
    (Matrix.toBilin' M) hs hn
  have e : (fun x y : ι → Fv F v => chiV F ψ v (Matrix.toBilin' M x y)) =
      fun x y => psiV F ψ v (x ⬝ᵥ (M *ᵥ y)) := by
    funext x y
    rw [Matrix.toBilin'_apply', chiV_apply]
  rw [e] at huniq
  exact huniq.unique ⟨hμ.1, hμ.2⟩ ⟨hν.1, hν.2⟩

end GlobalTheory.CompanionTheory.SW.SdUniq
