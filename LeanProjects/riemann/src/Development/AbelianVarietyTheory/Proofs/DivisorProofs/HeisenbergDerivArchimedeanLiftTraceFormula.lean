import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.HeisArch

variable {F : Type} [Field F] [NumberField F]

def evIr : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIr_apply (a : AF F) : evIr a = evI F a := rfl

def sndr : AF F →+* Af F := RingHom.snd _ _

theorem sndr_apply (a : AF F) : sndr a = a.2 := rfl

theorem realAd_mul_infAd (t : ℝ) (α : mixedEmbedding.mixedSpace F) :
    realAd F t * infAd F α = infAd F (t • α) := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm α = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • α)
    rw [← map_mul, Algebra.smul_def]
  · show (0 : Af F) * 0 = 0
    exact mul_zero _

theorem evIr_infAd (α : mixedEmbedding.mixedSpace F) : evIr (infAd F α) = α := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm α) = α
  exact RingEquiv.apply_symm_apply _ _

theorem sndr_infAd (α : mixedEmbedding.mixedSpace F) : sndr (infAd F α) = 0 := rfl

theorem at_of_snd (z : AF F) (h : z.2 = 0) : At (evI F) z := by
  intro u hu
  have h1 : u.1 = 0 := by
    have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (this.trans (map_zero _).symm)
  show u * z = 0
  refine Prod.ext ?_ ?_
  · show u.1 * z.1 = 0
    rw [h1, zero_mul]
  · show u.2 * z.2 = 0
    rw [h, mul_zero]

variable (F) in
theorem exists_strictHenselian_absolutely_closed_local_ring (κ : Type) [Fintype κ] :
    ∃ T : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ),
      ∀ b y, (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) b y =
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i) := by
  let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : ((κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      (GlobalTheory.VacLn.trPair F κ).flip
  have hL : ∀ b y, L b y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i) := fun b y => rfl
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    apply GlobalTheory.VacLn.trPair_nondeg b
    intro y
    have := congrArg (fun φ : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ => φ y) hb
    simpa [hL, GlobalTheory.VacLn.trPair_apply] using this
  have hdim : Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F) =
      Module.finrank ℝ ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) := by
    rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap :
      ((κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _)]
    exact (Subspace.dual_finrank_eq).symm
  refine ⟨(LinearMap.linearEquivOfInjective L hinj hdim).toContinuousLinearEquiv, fun b y => ?_⟩
  rfl

end GlobalTheory.ArchDecay.HeisArch

noncomputable section

namespace GlobalTheory.ArchDecay.HeisArch

theorem infAd_zero {F : Type} [Field F] [NumberField F] : infAd F (0 : mixedEmbedding.mixedSpace F) = 0 := by
  unfold infAd; rw [map_zero, map_zero]; rfl

theorem heisD_liftI : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) ≃L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ), ∀ (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ schA F (Fin n × Fin d), heisD M ψ (liftI M ζ) f = dR F (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (-(2 * Real.pi * Complex.I)) ζ f := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring F (Fin n × Fin d)
  refine ⟨T, fun ζ f hf => ?_⟩
  funext x
  set L : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, arch F x i * ζ.2 i) with hLdef
  set c0 : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (evIr (⅟(2 : AF F)) * ∑ i, ζ.1 i * ζ.2 i) with hc0
  have hco : ∀ t : ℝ, M.co.e (realAd F t • liftI M ζ) =
      (fun i => infAd F (t • ζ.1 i), fun i => infAd F (t • ζ.2 i)) := by
    intro t
    rw [map_smul, liftI, LinearEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_ <;> funext i <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, realAd_mul_infAd]
  have hline : ∀ t : ℝ, M.heisLine ψ (liftI M ζ) t f x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L + t ^ 2 * c0 : ℝ) : ℂ)) *
        f (x + fun i => infAd F (t • ζ.1 i)) := by
    intro t
    simp only [Model.heisLine, Darboux.rho, schr, hco t]
    congr 1
    set P : AF F := x ⬝ᵥ (fun i => infAd F (t • ζ.2 i)) +
      ⅟(2 : AF F) * ((fun i => infAd F (t • ζ.1 i)) ⬝ᵥ (fun i => infAd F (t • ζ.2 i))) with hP
    have hAt : At (evI F) P := by
      apply at_of_snd
      rw [← sndr_apply, hP, map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
      simp [dotProduct, Function.comp_def, sndr_infAd]
    rw [hψ.2.2 P hAt, ← evIr_apply]
    congr 3
    rw [hP, map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
    simp only [Function.comp_def, evIr_infAd, dotProduct]
    have e1 : (∑ i, evIr (x i) * (t • ζ.2 i)) = t • ∑ i, arch F x i * ζ.2 i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm]; rfl
    have e2 : evIr (⅟(2 : AF F)) * (∑ i, (t • ζ.1 i) * (t • ζ.2 i)) =
        (t ^ 2) • (evIr (⅟(2 : AF F)) * ∑ i, ζ.1 i * ζ.2 i) := by
      rw [show (∑ i, (t • ζ.1 i) * (t • ζ.2 i)) = (t ^ 2) • ∑ i, ζ.1 i * ζ.2 i from by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_smul_comm, sq]]
      exact mul_smul_comm _ _ _
    rw [e1, e2, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hg : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L + t ^ 2 * c0 : ℝ) : ℂ)))
      (-(2 * Real.pi * Complex.I) * (L : ℂ)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * L + t ^ 2 * c0) L 0 := by
      have h0 : HasDerivAt (fun t : ℝ => t * L + t ^ 2 * c0) (1 * L + ((2 : ℕ) * (0 : ℝ) ^ (2 - 1)) * c0) 0 :=
        ((hasDerivAt_id' (0 : ℝ)).mul_const L).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const c0)
      exact h0.congr_deriv (by norm_num)
    have h2 := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
    convert h2 using 1
    simp
  have hh : HasDerivAt (fun t : ℝ => f (x + fun i => infAd F (t • ζ.1 i))) (dD F ζ.1 f x) 0 :=
    ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F ζ.1 hf).1 x).hasDerivAt
  have hx0 : (x + fun i => infAd F ((0 : ℝ) • ζ.1 i)) = x := by
    funext i
    show x i + infAd F ((0 : ℝ) • ζ.1 i) = x i
    rw [zero_smul, infAd_zero, add_zero]
  show deriv (fun t : ℝ => M.heisLine ψ (liftI M ζ) t f x) 0 = _
  have hd : HasDerivAt (fun t : ℝ => M.heisLine ψ (liftI M ζ) t f x)
      (-(2 * Real.pi * Complex.I) * (L : ℂ) * f (x + fun i => infAd F ((0 : ℝ) • ζ.1 i)) +
        Complex.exp (-(2 * Real.pi * Complex.I) * (((0 : ℝ) * L + (0 : ℝ) ^ 2 * c0 : ℝ) : ℂ)) * dD F ζ.1 f x) 0 := by
    rw [show (fun t : ℝ => M.heisLine ψ (liftI M ζ) t f x) = _ from funext hline]
    exact hg.mul hh
  rw [hd.deriv]
  simp only [dR, mM, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hT, hx0]
  rw [← hLdef]
  simp
  ring

end GlobalTheory.ArchDecay.HeisArch
