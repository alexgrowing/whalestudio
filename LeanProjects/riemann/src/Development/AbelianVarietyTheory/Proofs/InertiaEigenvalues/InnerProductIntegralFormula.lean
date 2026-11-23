import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFormulaOfKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdelicL2Norm

theorem adInner_eq_mul_integral {G H W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G) [ν.IsMulLeftInvariant]
    [ν.IsOpenPosMeasure] (π : G →* H) (hπ : Function.Surjective π) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J₀ J : Subgroup H) (hle : J ≤ J₀) (ho : IsOpen (J.comap π : Set G))
    (h1 : ν (J₀.comap π) = 1) (ρ : G →* Module.End ℂ W) (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y)
    (χ : J →* ℂˣ) (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) {I : Type} [Fintype I] (y : I → H)
    (hy : Formalism.IndefR.Bridge.IsReps (π.comp Γ.subtype) J y) :
    ∃ c : ℝ, 0 < c ∧ ∀ f ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
      ∀ f' ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
        IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν ∧
        Formalism.IndefR.Bridge.adInner (π.comp Γ.subtype) J y f f' =
          (c : ℂ) * ∫ h in 𝓖, inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) ∂ν := by
  set m := ν (J.comap π) with hmdef
  have hm0 : m ≠ 0 := ho.measure_ne_zero ν ⟨1, by simp⟩
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top (h1 ▸ ENNReal.one_ne_top) (measure_mono (Subgroup.comap_mono hle))
  have h𝓖' : IsFundamentalDomain Γ 𝓖 (m⁻¹ • ν) := h𝓖.mono Measure.smul_absolutelyContinuous
  have h1' : (m⁻¹ • ν) (J.comap π) = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, ← hmdef, ENNReal.inv_mul_cancel hm0 hmt]
  obtain ⟨-, key⟩ := GlobalTheory.InnerClassSum.integral_inner_eq_adInner (m⁻¹ • ν) π hπ Γ h𝓖' J ho h1' ρ hρ χ hχ y hy
  refine ⟨m.toReal⁻¹, inv_pos.2 (ENNReal.toReal_pos hm0 hmt), fun f hf f' hf' => ?_⟩
  obtain ⟨hi, he⟩ := key f hf f' hf'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at hi ⊢
    rw [Measure.restrict_smul] at hi
    exact (integrable_smul_measure (ENNReal.inv_ne_zero.2 hmt) (ENNReal.inv_ne_top.2 hm0)).1 hi
  · rw [← he, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_inv, Complex.real_smul]

theorem integrableOn_coord {G H W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G) (π : G →* H)
    (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) (ρ : G →* Module.End ℂ W)
    (hρc : ∀ x, Continuous fun h => ρ h x) (χ : J →* ℂˣ) (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) (Γ : Subgroup G) (f f' : H → W)
    (hF : f ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ)
    (hF' : f' ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ)
    {𝓖 : Set G} (hi : IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f (π h)))) 𝓖 ν)
    (hi' : IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f' (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν) (a a' : W) :
    IntegrableOn (fun h => star (inner ℂ a (ρ h⁻¹ (f (π h)))) * inner ℂ a' (ρ h⁻¹ (f' (π h)))) 𝓖 ν := by
  have hr : ∀ g ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ, ∀ (x : H) (k : J),
      g (x * k) = (χ k : ℂ) • g x := fun g hg x k => by
    have := hg 1 x k
    simpa using this
  have hf := hr f hF
  have hf' := hr f' hF'
  have hcont : Continuous fun h => star (inner ℂ a (ρ h⁻¹ (f (π h)))) * inner ℂ a' (ρ h⁻¹ (f' (π h))) := by
    refine continuous_iff_continuousAt.2 fun h₀ => ?_
    have hψ : Continuous fun h : G => star (inner ℂ a (ρ h⁻¹ (f (π h₀)))) * inner ℂ a' (ρ h⁻¹ (f' (π h₀))) :=
      (continuous_star.comp (continuous_const.inner ((hρc _).comp continuous_inv))).mul
        (continuous_const.inner ((hρc _).comp continuous_inv))
    refine hψ.continuousAt.congr ?_
    have hU : {h : G | h₀⁻¹ * h ∈ J.comap π} ∈ nhds h₀ :=
      (ho.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
    filter_upwards [hU] with h hh
    have e : π h = π h₀ * ((⟨π (h₀⁻¹ * h), hh⟩ : J) : H) := by
      simp [← map_mul]
    rw [e, hf, hf', map_smul, map_smul, inner_smul_right, inner_smul_right, star_mul']
    have hn : star ((χ ⟨π (h₀⁻¹ * h), hh⟩ : ℂˣ) : ℂ) * ((χ ⟨π (h₀⁻¹ * h), hh⟩ : ℂˣ) : ℂ) = 1 := by
      rw [show star _ = (starRingEnd ℂ) _ from rfl, Complex.conj_mul', hχ]; simp
    linear_combination -(star (inner ℂ a (ρ h⁻¹ (f (π h₀)))) * inner ℂ a' (ρ h⁻¹ (f' (π h₀)))) * hn
  have hsq : ∀ x : W, ‖inner ℂ x x‖ = ‖x‖ ^ 2 := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; simp
  refine Integrable.mono' ((hi.norm.add hi'.norm).const_mul (‖a‖ * ‖a'‖)) hcont.aestronglyMeasurable.restrict ?_
  refine Filter.Eventually.of_forall fun h => ?_
  simp only [Pi.add_apply, hsq, norm_mul, norm_star]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) a (ρ h⁻¹ (f (π h)))
  have h2 := norm_inner_le_norm (𝕜 := ℂ) a' (ρ h⁻¹ (f' (π h)))
  have hx := norm_nonneg (ρ h⁻¹ (f (π h)))
  have hy := norm_nonneg (ρ h⁻¹ (f' (π h)))
  have ha := norm_nonneg a
  have ha' := norm_nonneg a'
  have hxy : ‖ρ h⁻¹ (f (π h))‖ * ‖ρ h⁻¹ (f' (π h))‖ ≤ ‖ρ h⁻¹ (f (π h))‖ ^ 2 + ‖ρ h⁻¹ (f' (π h))‖ ^ 2 := by
    nlinarith [sq_nonneg (‖ρ h⁻¹ (f (π h))‖ - ‖ρ h⁻¹ (f' (π h))‖)]
  calc ‖inner ℂ a (ρ h⁻¹ (f (π h)))‖ * ‖inner ℂ a' (ρ h⁻¹ (f' (π h)))‖
      ≤ (‖a‖ * ‖ρ h⁻¹ (f (π h))‖) * (‖a'‖ * ‖ρ h⁻¹ (f' (π h))‖) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖a‖ * ‖a'‖ * (‖ρ h⁻¹ (f (π h))‖ * ‖ρ h⁻¹ (f' (π h))‖) := by ring
    _ ≤ ‖a‖ * ‖a'‖ * (‖ρ h⁻¹ (f (π h))‖ ^ 2 + ‖ρ h⁻¹ (f' (π h))‖ ^ 2) := by gcongr

end GlobalTheory.AdelicL2Norm

noncomputable section

namespace GlobalTheory.AdelicL2Norm

set_option maxHeartbeats 2000000 in

theorem norm_eq_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), ∃ c : ℝ, 0 < c ∧ ∀ u u' : (R.HV i t).H, ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h in R.fdV i t, ⟪R.extV i t u h, R.extV i t u' h⟫_ℂ ∂(R.νV i t) ∧ ∀ a a' : (R.cV i).W, IntegrableOn (fun h => star ⟪a, R.extV i t u h⟫_ℂ * ⟪a', R.extV i t u' h⟫_ℂ) (R.fdV i t) (R.νV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t
  have hν := hL.models.νV i t
  have hH := hL.models.HV i t
  have hc := hL.models.cV i
  haveI : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Vc D i).gram
  haveI := hν.1.1
  have ho : IsOpen (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).J.comap (finHom (Vc D i)).rangeRestrict :
      Subgroup (GA D (Vc D i))) : Set (GA D (Vc D i))) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level (Vc D i) (R.βV i) (R.datVt i t)] with κ hκ
    exact hκ.1
  have h1 : R.νV i t ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (R.datVt i t)).comap (finHom (Vc D i)).rangeRestrict) = 1 :=
    GlobalTheory.Mass.Levels.measure_comap_finE hν.1
  have hle : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (R.datVt i t) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have e : rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) x.1) = 1 := Subgroup.mem_bot.1 hx.2
    exact e ▸ one_mem _
  have hχ : ∀ k, ‖((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂ)‖ = 1 := fun k =>
    GlobalTheory.InnerClassSum.norm_levFn (R.βV i) (flag1L (R.datVt i t)) (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k.1.1)
  obtain ⟨c, hc0, hcl⟩ := adInner_eq_mul_integral (R.νV i t) (finHom (Vc D i)).rangeRestrict
    (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i)) hν.2 _ _ hle ho h1 (R.cV i).ρ hc.2.1
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ hχ (R.B.L i t).pres.y (R.B.L i t).pres.reps
  have hmem := fun u => hH.2.1.le (LinearMap.mem_range_self (R.HV i t).e u)
  have hx : ∀ u h, R.extV i t u h = (R.cV i).ρ h⁻¹ ((R.HV i t).e u ((finHom (Vc D i)).rangeRestrict h)) :=
    fun _ _ => rfl
  refine ⟨c, hc0, fun u u' => ⟨?_, fun a a' => ?_⟩⟩
  · simp only [hx]
    exact (hH.2.2 u u').trans (hcl _ (hmem u) _ (hmem u')).2
  · simp only [hx]
    exact integrableOn_coord (R.νV i t) (finHom (Vc D i)).rangeRestrict _ ho (R.cV i).ρ hc.2.2.1 _ hχ (GQ (Vc D i)) _ _ (hmem u) (hmem u')
      (hcl _ (hmem u) _ (hmem u)).1 (hcl _ (hmem u') _ (hmem u')).1 a a'

end GlobalTheory.AdelicL2Norm
