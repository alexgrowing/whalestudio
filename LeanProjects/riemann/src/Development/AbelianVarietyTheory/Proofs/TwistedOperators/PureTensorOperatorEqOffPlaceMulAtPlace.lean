import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionFiniteAdelicPureTensorEqLocalConvolut

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.OffOp

section General

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group A] [TopologicalSpace A]
  [IsTopologicalGroup A]

def splitEquiv (ι : A →* G) (π : G →* A) (hπι : ∀ a, π (ι a) = a) (hc : ∀ a g, π g = 1 → Commute (ι a) g) :
    π.ker × A ≃* G where
  toFun p := p.1 * ι p.2
  invFun g := (⟨g * (ι (π g))⁻¹, by simp [MonoidHom.mem_ker, hπι]⟩, π g)
  left_inv p := by
    have h : π p.1 = 1 := p.1.2
    ext <;> simp [hπι, h]
  right_inv g := by simp
  map_mul' p q := by
    have := (hc p.2 q.1 q.1.2).eq
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_assoc]
    rw [← mul_assoc (q.1 : G), ← this, mul_assoc]

variable [T2Space A] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem exists_op (ι : A →* G) (π : G →* A) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ a, π (ι a) = a)
    (hc : ∀ a g, π g = 1 → Commute (ι a) g) (μ : Measure A) [μ.IsHaarMeasure] (ν : Measure G) [ν.IsHaarMeasure]
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (hσ : GlobalTheory.PRep.IsSmooth σ)
    {φ : G → ℂ} (hφ : φ ∈ GlobalTheory.SplitWeil.SB G) :
    ∃ H : W →ₗ[ℂ] W, (∀ g x, H (σ (ι g) x) = σ (ι g) (H x)) ∧
      (∀ x, ∀ k ∈ leftStabilizer φ, π k = 1 → σ k (H x) = H x) ∧
      ∀ f ∈ GlobalTheory.SplitWeil.SB A, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ (σ.comp ι) f B →
        ∀ Ψ : G → ℂ, (∀ h a, π h = 1 → Ψ (h * ι a) = φ h * f a) → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ Ψ (H ∘ₗ B) := by
  classical
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hNc : IsClosed (π.ker : Set G) := by
    have hset : (π.ker : Set G) = π ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hNc.locallyCompactSpace
  let e : π.ker × A ≃ₜ* G :=
    { splitEquiv ι π hπι hc with
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (hι.comp continuous_snd)
      continuous_invFun := by
        refine Continuous.prodMk ?_ hπ
        exact (continuous_id.mul (hι.comp hπ).inv).subtype_mk _ }
  have he : ∀ p : π.ker × A, e p = (p.1 : G) * ι p.2 := fun p => rfl
  let μN : Measure π.ker := Measure.haar
  let P : Measure (π.ker × A) := μN.prod μ
  have hE : MeasurableEmbedding e := e.toHomeomorph.isClosedEmbedding.measurableEmbedding
  haveI : (P.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P e
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • P.map e := ⟨_, Measure.isMulLeftInvariant_eq_smul ν (P.map e)⟩
  let σN : Representation ℂ π.ker W := σ.comp π.ker.subtype
  have hσN : GlobalTheory.PRep.IsSmooth σN := fun x => (hσ x).preimage continuous_subtype_val
  let φN : π.ker → ℂ := fun h => φ h
  have hφN1 : IsLocallyConstant φN := hφ'.1.comp_continuous continuous_subtype_val
  have hφN2 : HasCompactSupport φN := hφ'.2.comp_isClosedEmbedding hNc.isClosedEmbedding_subtypeVal
  let T : W →ₗ[ℂ] W := smoothOp σN μN φN
  have hT : ∀ (l : Module.Dual ℂ W) (y : W), l (T y) = ∫ h, φN h * l (σN h y) ∂μN := by
    intro l y
    simpa [smul_eq_mul] using hσN.map_smoothOp (μ := μN) hφN1 hφN2 l y
  refine ⟨((c : ℝ) : ℂ) • T, ?_, ?_, ?_⟩
  · intro g x
    simp only [LinearMap.smul_apply, map_smul]
    congr 1
    refine (hσN.map_smoothOp_of_intertwining (μ := μN) hσN hφN1 hφN2 (σ (ι g)) (fun h y => ?_) x).symm
    show σ (ι g) (σ h y) = σ h (σ (ι g) y)
    rw [← Module.End.mul_apply, ← map_mul, (hc g h h.2).eq, map_mul, Module.End.mul_apply]
  · intro x k hk hk1
    have hmem := hσN.smoothOp_mem_fixed (μ := μN) hφN1 hφN2
      (K := (leftStabilizer φ).comap π.ker.subtype) (fun k' hk' g => hk' g) x
    have hfix := (mem_fixed.1 hmem) ⟨k, MonoidHom.mem_ker.2 hk1⟩ hk
    simp only [LinearMap.smul_apply, map_smul]
    congr 1
  · intro f hf B hB Ψ hΨ v l
    have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
    let F : π.ker × A → ℂ := fun p => φN p.1 * f p.2 * l (σ (e p) v)
    have hFe : ∀ p, Ψ (e p) * l (σ (e p) v) = F p := by
      intro p
      show Ψ (e p) * l (σ (e p) v) = φ p.1 * f p.2 * l (σ (e p) v)
      rw [he p, hΨ _ _ p.1.2]
    have hFlc : IsLocallyConstant F := by
      have h1 : IsLocallyConstant fun p : π.ker × A => φN p.1 := hφN1.comp_continuous continuous_fst
      have h2 : IsLocallyConstant fun p : π.ker × A => f p.2 := hf'.1.comp_continuous continuous_snd
      have h3 : IsLocallyConstant fun p : π.ker × A => l (σ (e p) v) :=
        ((hσ.isLocallyConstant_orbit v).comp_continuous e.continuous).comp l
      exact (h1.mul h2).mul h3
    have hFcs : HasCompactSupport F := by
      refine IsCompact.of_isClosed_subset (IsCompact.prod hφN2 hf'.2) (isClosed_tsupport F) ?_
      refine closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
      intro p hp
      refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
      · intro h0
        apply hp
        show φN p.1 * f p.2 * l (σ (e p) v) = 0
        rw [h0, zero_mul, zero_mul]
      · intro h0
        apply hp
        show φN p.1 * f p.2 * l (σ (e p) v) = 0
        rw [h0, mul_zero, zero_mul]
    have hFi : Integrable F P := hFlc.continuous.integrable_of_hasCompactSupport hFcs
    refine ⟨?_, ?_⟩
    · rw [hν]
      refine Integrable.smul_measure_nnreal ?_
      rw [hE.integrable_map_iff]
      exact hFi.congr (Filter.Eventually.of_forall fun p => (hFe p).symm)
    · have hin : ∀ a, ∫ h, F (h, a) ∂μN = f a * l (T (σ (ι a) v)) := by
        intro a
        rw [hT, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        show φN h * f a * l (σ (e (h, a)) v) = f a * (φN h * l (σ h (σ (ι a) v)))
        rw [he, map_mul, Module.End.mul_apply]
        ring
      have hB2 := (hB v (l ∘ₗ T)).2
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply] at hB2
      rw [hν, integral_smul_nnreal_measure, hE.integral_map,
        integral_congr_ae (Filter.Eventually.of_forall hFe), integral_prod_symm F hFi,
        show (fun a => ∫ h, F (h, a) ∂μN) = fun a => f a * l (T (σ (ι a) v)) from funext hin, ← hB2]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, NNReal.smul_def,
        Complex.real_smul]

end General

variable {D : D7}

theorem isFinFamily_update {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (u : HeightOneSpectrum (𝓞 D.host.F))
    {f : GLoc D.sp.cm.sig V.gram u → ℂ} (hf : f ∈ CcLoc D.sp.cm.sig V.gram u) :
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) (Function.update ff u f) := by
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v = u
    · subst hv
      simpa using hf
    · rw [Function.update_of_ne hv]
      exact hff.1 v
  · filter_upwards [hff.2, Filter.eventually_cofinite_ne u] with v hv hne
    rw [Function.update_of_ne hne]
    exact hv

theorem finite_mulSupport {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (g : GfC V) :
    (Function.mulSupport fun v => ff v (finLoc V v g)).Finite := by
  have hev := GlobalTheory.AdelicU.eventually_proj_mem_stabLoc (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V)
    (g := (g : GA D V))
  refine (Filter.eventually_cofinite.1 (hff.2.and hev)).subset fun v hv => ?_
  rintro ⟨h1, h2⟩
  apply hv
  show ff v (proj D.sp.cm.sig V.gram v (g : GA D V)) = 1
  rw [h1]
  exact (Set.indicator_of_mem h2 1).trans rfl

theorem finFn_update_mul {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (u : HeightOneSpectrum (𝓞 D.host.F))
    {f : GLoc D.sp.cm.sig V.gram u → ℂ} (hf : f ∈ CcLoc D.sp.cm.sig V.gram u) (h : GfC V) (a : Gv V u)
    (hh : finLoc V u h = 1) :
    finFn V (Function.update ff u f) (h * locFin V u a) =
      finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u)) h * f a := by
  have hu : unitLoc D.sp.cm.sig V.gram (frameLat V) u ∈ CcLoc D.sp.cm.sig V.gram u := unitLoc_mem u
  have m1 := finite_mulSupport (isFinFamily_update hff u hf) (h * locFin V u a)
  have m2 := finite_mulSupport (isFinFamily_update hff u hu) h
  have hfin : ∀ (ff' : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (g : GfC V),
      finFn V ff' g = ∏ᶠ v, ff' v (finLoc V v g) := fun _ _ => rfl
  have hloc : ∀ v, finLoc V v (locFin V u a) = proj D.sp.cm.sig V.gram v (emb D.sp.cm.sig V.gram u a) :=
    fun _ => rfl
  rw [hfin, hfin, ← mul_finprod_cond_ne u m1, ← mul_finprod_cond_ne u m2]
  have hoff : (∏ᶠ (v) (_ : v ≠ u), Function.update ff u f v (finLoc V v (h * locFin V u a))) =
      ∏ᶠ (v) (_ : v ≠ u), Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u) v (finLoc V v h) := by
    refine finprod_congr fun v => finprod_congr fun hv => ?_
    rw [Function.update_of_ne hv, Function.update_of_ne hv, map_mul, hloc, proj_emb_ne D.sp.cm.sig V.gram hv, mul_one]
  rw [hoff, Function.update_self, Function.update_self, map_mul, hh, hloc, proj_emb_self, one_mul]
  have h1 : unitLoc D.sp.cm.sig V.gram (frameLat V) u 1 = 1 :=
    (Set.indicator_of_mem (one_mem _) 1).trans rfl
  rw [h1, one_mul, mul_comm]

theorem exists_offOp : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ (H : W →ₗ[ℂ] W) (K : Subgroup (GfC V)), IsOpen (K : Set (GfC V)) ∧ (∀ g x, H (σ (locFin V u g) x) = σ (locFin V u g) (H x)) ∧ (∀ x, ∀ k ∈ K, finLoc V u k = 1 → σ k (H x) = H x) ∧ ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (μf u) (σ.comp (locFin V u)) f B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (Function.update ff u f)) (H ∘ₗ B) := by
  intro D V u μf hμf hK ν hν W _ _ σ hσ ff hff
  haveI := hμf u
  haveI : LocallyCompactSpace (GfC V) := GlobalTheory.AdelicU.locallyCompactSpace_finPts D.sp.cm.sig V.gram
  haveI : ν.IsHaarMeasure := hν.1
  have hu : unitLoc D.sp.cm.sig V.gram (frameLat V) u ∈ CcLoc D.sp.cm.sig V.gram u := unitLoc_mem u
  have hfam := isFinFamily_update hff u hu
  have hφ := (GlobalTheory.TrConv.conv_finFn D V μf hμf hK ν hν _ _ hfam hfam).2.2
  have hφ' : IsLocallyConstant (finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u))) ∧
      HasCompactSupport (finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u))) := hφ
  have hι : Continuous (locFin V u) := continuous_induced_rng.2 (continuous_emb D.sp.cm.sig V.gram u)
  have hπ : Continuous (finLoc V u) := (continuous_proj D.sp.cm.sig V.gram u).comp continuous_subtype_val
  have hπι : ∀ a, finLoc V u (locFin V u a) = a := fun a => proj_emb_self D.sp.cm.sig V.gram u a
  have hc : ∀ a g, finLoc V u g = 1 → Commute (locFin V u a) g := fun a g hg =>
    Subtype.ext (commute_emb D.sp.cm.sig V.gram a hg).eq
  obtain ⟨H, h1, h2, h3⟩ := exists_op (locFin V u) (finLoc V u) hι hπ hπι hc (μf u) ν σ hσ hφ
  exact ⟨H, leftStabilizer _, isOpen_leftStabilizer hφ'.1 hφ'.2, h1, h2,
    fun f hf B hB => h3 f hf B hB _ fun h a hh => finFn_update_mul hff u hf h a hh⟩

end GlobalTheory.OffOp

end
