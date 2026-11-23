import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJStandardLPartial

open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

theorem hasProd_of_hasProd_compl {ι : Type*} {f : ι → ℂ} {b : ℂ} (S : Finset ι)
    (h : HasProd (fun i : {i // i ∉ S} ↦ f i) b) : HasProd f ((∏ i ∈ S, f i) * b) := by
  have h1 : HasProd ((S : Set ι).mulIndicator f) (∏ i ∈ S, f i) := by
    have : HasProd ((S : Set ι).mulIndicator f) (∏ i ∈ S, (S : Set ι).mulIndicator f i) :=
      hasProd_prod_of_ne_finset_one fun i hi ↦ Set.mulIndicator_of_notMem (by simpa using hi) _
    rwa [Finset.prod_congr rfl fun i hi ↦ Set.mulIndicator_of_mem (by simpa using hi) f] at this
  have h2 : HasProd (({i | i ∉ S} : Set ι).mulIndicator f) b :=
    (hasProd_subtype_iff_mulIndicator (s := {i | i ∉ S})).1 h
  have h3 := h1.mul h2
  have heq : (fun i ↦ (S : Set ι).mulIndicator f i * ({i | i ∉ S} : Set ι).mulIndicator f i) = f := by
    funext i
    by_cases hi : i ∈ S
    · rw [Set.mulIndicator_of_mem (by simpa using hi), Set.mulIndicator_of_notMem (by simpa using hi),
        mul_one]
    · rw [Set.mulIndicator_of_notMem (by simpa using hi), Set.mulIndicator_of_mem (by simpa using hi),
        one_mul]
  rwa [heq] at h3

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_sphericalIntegrable (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    {f : AdelicGLn.AdelicGL K n → ℂ} (hfc : Continuous f)
    (hP : ∀ Ψ ∈ GJMatrix.matrixSchwartzBruhat K n, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (GJGlobal.zetaIntegrand Ψ f s) ν)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (hξ : ∀ v, ξ v ∈ smoothVectors (π v))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (hf : ∀ g, f g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)
        (localComp n v g))
    (hf0 : ∃ g, f g ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      (∀ v ∉ S, Integrable (fun g : GL (Fin n) (v.adicCompletion K) ↦
        integralIndicator (v.adicCompletion K) n (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g *
            detPow g (s + ((n : ℂ) - 1) / 2)) (localHaar n v)) ∧
      Multipliable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
        zetaIntegral (localHaar n (v : HeightOneSpectrum (𝓞 K)))
          (integralIndicator ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) n)
          (Parabolic.matrixCoeff (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) (ξ v) (ℓ v)) s := by
  obtain ⟨g₀, hg₀⟩ := hf0
  set c₀ := ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) with hc₀
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀)).Finite := by
    refine ((finite_setOf_not_mem g₀).union S.finite_toSet).subset fun v hv ↦ ?_
    by_contra hc
    simp only [mem_union, Finset.mem_coe, not_or] at hc
    have hK : localComp n v g₀ ∈ integralGL (v.adicCompletion K) n := by
      by_contra h
      exact hc.1 h
    apply hv
    show ℓ v (π v (localComp n v g₀) (ξ v)) = 1
    rw [(hsph v hc.2).1 _ hK, (hsph v hc.2).2]
  rw [hf g₀] at hg₀
  have hfi0 : fi (archComp K n g₀) ≠ 0 := left_ne_zero_of_mul hg₀
  have hc₀0 : c₀ ≠ 0 := right_ne_zero_of_mul hg₀
  have hloc0 : ∀ v : HeightOneSpectrum (𝓞 K),
      Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) ≠ 0 :=
    fun v h ↦ hc₀0 (finprod_eq_zero _ v h hsupp)
  have hfic : Continuous fi := by
    have key : ∀ x, fi x = f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ := by
      intro x
      have : f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) = fi x * c₀ := by
        rw [hf, archComp_prodEquiv_symm]
        simp_rw [localComp_prodEquiv_symm]
        rfl
      rw [this, mul_div_cancel_right₀ _ hc₀0]
    have hc : Continuous fun x ↦ f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ :=
      (hfc.comp ((AdelicGLn.prodEquiv K n).symm.continuous.comp
        (continuous_id.prodMk continuous_const))).div_const c₀
    exact hc.congr fun x ↦ (key x).symm
  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar
  obtain ⟨φ, -, hφne, -, -⟩ := exists_archBump μi hfic hfi0
  have hbump : ∀ v ∈ S, ∃ Φ : Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ, IsSchwartzBruhat Φ ∧
      ∃ a : ℂ, a ≠ 0 ∧ ∀ s : ℂ,
        Integrable (fun g : GL (Fin n) (v.adicCompletion K) ↦ Φ (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g *
            detPow g (s + ((n : ℂ) - 1) / 2)) (localHaar n v) ∧
        ∫⁻ g : GL (Fin n) (v.adicCompletion K), ‖Φ (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g *
            detPow g (s + ((n : ℂ) - 1) / 2)‖ₑ ∂localHaar n v ≠ 0 ∧
        zetaIntegral (localHaar n v) Φ (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s =
          a * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2) :=
    fun v _ ↦ exists_localBump (localHaar n v) (π v) (hξ v) (ℓ v) (hloc0 v)
  choose Φb hΦbSB a ha hΦb using hbump
  set Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ :=
    fun v ↦ if h : v ∈ S then Φb v h else integralIndicator (v.adicCompletion K) n with hΦdef
  have hΦS : ∀ v (hv : v ∈ S), Φ v = Φb v hv := fun v hv ↦ by simp only [hΦdef, dif_pos hv]
  have hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v) := fun v hv ↦ by rw [hΦS v hv]; exact hΦbSB v hv
  have hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n :=
    fun v hv ↦ by simp only [hΦdef, dif_neg hv]
  obtain ⟨σ₀, hσ₀⟩ := hP _ (matrixTensor_mem φ S Φ hSB hS0)
  refine ⟨σ₀, fun s hs ↦ ?_⟩
  obtain ⟨-, hE2⟩ := globalZeta_eq_euler ν μi φ hSB hS0 hξ hsph hfic hf (hσ₀ s hs)
  have hAne : ¬ (archIntegrand φ fi s =ᵐ[μi] 0) := by
    intro h0
    apply hφne s
    have h0' : (fun x ↦ ‖archIntegrand φ fi s x‖ₑ) =ᵐ[μi] 0 := h0.mono fun x hx ↦ by simp [hx]
    rw [lintegral_congr_ae h0']
    simp
  obtain ⟨hBint, hP'⟩ := hE2 hAne
  have hlocint : ∀ v, Integrable (localIntegrand Φ π ξ ℓ s v) (localHaar n v) :=
    integrable_factor_finite (localIntegrand Φ π ξ ℓ s)
      (fun v ↦ (continuous_localIntegrand' hSB hS0 hξ s v).measurable)
      (by
        filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv k hk
        exact localIntegrand_eq_one hS0 hsph s hv hk)
      (fun y ↦ rfl) hBint (fun v hv ↦ by
        by_cases hvS : v ∈ S
        · have := (hΦb v hvS s).2.1
          simp only [localIntegrand, hΦS v hvS]
          exact this
        · exact absurd (fun k hk ↦ localIntegrand_eq_one hS0 hsph s hvS hk) hv)
  have hram0 : ∀ v ∈ S, zetaIntegral (localHaar n v) (Φ v)
      (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s ≠ 0 := by
    intro v hv
    rw [hΦS v hv, (hΦb v hv s).2.2]
    exact mul_ne_zero (ha v hv) (detPow_ne_zero' _ _)
  refine ⟨fun v hv ↦ ?_, ?_⟩
  · refine (hlocint v).congr (Eventually.of_forall fun g ↦ ?_)
    simp only [localIntegrand, hS0 v hv]
  · refine (hasProd_compl_of_hasProd hP' S hram0).multipliable.congr fun v ↦ ?_
    rw [hS0 v v.2]

end GJStandardL

end

end GroundTheory.Automorphic
