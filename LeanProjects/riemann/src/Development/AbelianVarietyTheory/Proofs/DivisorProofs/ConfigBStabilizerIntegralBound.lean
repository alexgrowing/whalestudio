import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCharacterSeminormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeMeasSmall

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.ConeMeasV

theorem tendsto_heis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (f : SchwartzMap V ℂ) {ι : Type} {𝓕 : Filter ι} {L : ι → V →L[ℝ] ℝ} {k : ι → ℝ} {a : ι → V}
    (hL : Tendsto L 𝓕 (𝓝 0)) (hk : Tendsto k 𝓕 (𝓝 0)) (ha : Tendsto a 𝓕 (𝓝 0)) :
    Tendsto (fun i => T (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L i y + k i))
      (SchwartzMap.compSubConstCLM ℂ (-(a i)) f))) 𝓕 (𝓝 (T f)) := by
  let p : Seminorm ℂ (SchwartzMap V ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hp : Continuous p := continuous_norm.comp T.continuous
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le V p hp
  obtain ⟨q₂, M₂, -, hb₂⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le V p hp
  obtain ⟨q₃, M₃, -, hb₃⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le V q₁ hq₁
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hLn : Tendsto (fun i => ‖L i‖) 𝓕 (𝓝 0) := by simpa using hL.norm
  have hkn : Tendsto (fun i => |k i|) 𝓕 (𝓝 0) := by simpa using hk.abs
  have han : Tendsto (fun i => ‖a i‖) 𝓕 (𝓝 0) := by simpa using ha.norm
  have lim : Tendsto (fun i => (‖L i‖ + |k i|) * (1 + ‖L i‖) ^ M₁ * (‖a i‖ * (1 + ‖a i‖) ^ M₃ * q₃ f + q₁ f) +
      ‖a i‖ * (1 + ‖a i‖) ^ M₂ * q₂ f) 𝓕 (𝓝 0) := by
    have := (((hLn.add hkn).mul ((hLn.const_add 1).pow M₁)).mul
      (((han.mul ((han.const_add 1).pow M₃)).mul_const (q₃ f)).add_const (q₁ f))).add
      ((han.mul ((han.const_add 1).pow M₂)).mul_const (q₂ f))
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) lim
  set g := SchwartzMap.compSubConstCLM ℂ (-(a i)) f with hg
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L i y + k i)) g - g) (g - f)
  rw [sub_add_sub_cancel] at h1
  rw [← map_sub]
  refine le_trans h1 (add_le_add ((hb₁ _ _ g).trans ?_) (hb₂ _ f))
  have h2 := map_add_le_add q₁ (g - f) f
  rw [sub_add_cancel] at h2
  have h3 := hb₃ (a i) f
  gcongr
  linarith

theorem eventually_fixed {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ : Type} [Fintype κ]
    (χ : AddChar R ℂ) (hχ : IsLocallyConstant χ) {g : (κ → R) → ℂ} (hg : g ∈ SB (κ → R)) :
    ∀ᶠ w : (κ → R) × (κ → R) × R in 𝓝 0, ∀ z, χ (z ⬝ᵥ w.1 + w.2.2) * g (z + w.2.1) = g z := by
  have hK : IsCompact (tsupport g) := hg.2.isCompact
  have key : ∀ᶠ w : (κ → R) × (κ → R) × R in 𝓝 0, ∀ z ∈ tsupport g,
      χ (z ⬝ᵥ w.1 + w.2.2) = 1 ∧ g (z + w.2.1) = g z ∧ g (z - w.2.1) = g z := by
    refine hK.eventually_forall_of_forall_eventually fun z₀ _ => ?_
    have c1 : IsLocallyConstant fun p : ((κ → R) × (κ → R) × R) × (κ → R) => χ (p.2 ⬝ᵥ p.1.1 + p.1.2.2) :=
      hχ.comp_continuous ((continuous_snd.dotProduct (by fun_prop)).add (by fun_prop))
    have c2 : IsLocallyConstant fun p : ((κ → R) × (κ → R) × R) × (κ → R) => g (p.2 + p.1.2.1) :=
      hg.1.comp_continuous (by fun_prop)
    have c3 : IsLocallyConstant fun p : ((κ → R) × (κ → R) × R) × (κ → R) => g (p.2 - p.1.2.1) :=
      hg.1.comp_continuous (by fun_prop)
    have c4 : IsLocallyConstant fun p : ((κ → R) × (κ → R) × R) × (κ → R) => g p.2 :=
      hg.1.comp_continuous (by fun_prop)
    filter_upwards [c1.eventually_eq (0, z₀), c2.eventually_eq (0, z₀), c3.eventually_eq (0, z₀),
      c4.eventually_eq (0, z₀)] with p h1 h2 h3 h4
    refine ⟨by simpa using h1, ?_, ?_⟩
    · rw [h2, h4]; simp
    · rw [h3, h4]; simp
  filter_upwards [key] with w hw z
  by_cases hz : z ∈ tsupport g
  · rw [(hw z hz).1, (hw z hz).2.1, one_mul]
  · have h0 : g z = 0 := image_eq_zero_of_notMem_tsupport hz
    have h1 : g (z + w.2.1) = 0 := by
      by_contra h
      have := (hw _ (subset_tsupport _ h)).2.2
      rw [add_sub_cancel_right, h0] at this
      exact h this.symm
    rw [h1, h0, mul_zero]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def qA : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1

theorem continuous_qA : Continuous (qA (F := F)) :=
  (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp continuous_fst

theorem continuous_p2 : Continuous (p2 (F := F)) := continuous_snd

theorem schr_pureA_eq {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    (f : SInf F κ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    schr ψ w (pureA F f g) = pureA F
      (archS f (fun i => qA (w.2 i)) (fun i => qA (w.1 i))
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (qA (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)))))
      (finS ψ g (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)))) := by
  classical
  let q := qA (F := F)
  let h : AF F := ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  funext x
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (GlobalTheory.HeisSchA.mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add, RingHom.map_dotProduct]
        rfl
      rw [e1, map_add, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add, RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

open scoped Classical in
theorem continuous_trL {κ : Type} [Fintype κ] :
    Continuous (trL : (κ → mixedEmbedding.mixedSpace F) → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) := by
  let A : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
    { toFun := trL
      map_add' := fun c c' => by ext y; simp only [trL_apply, dotProduct_add, map_add, ContinuousLinearMap.add_apply]
      map_smul' := fun r c => by
        ext y; simp only [trL_apply, dotProduct_smul, map_smul, ContinuousLinearMap.smul_apply, RingHom.id_apply] }
  exact A.continuous_of_finiteDimensional

theorem tendsto_schr_zero {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Tendsto (fun w => l (schrLin ψ w Φ)) (𝓝 0) (𝓝 (l Φ)) := by
  classical
  induction hΦ using Submodule.span_induction with
  | zero => simpa using tendsto_const_nhds
  | add Φ Ψ _ _ h1 h2 => simpa only [map_add] using h1.add h2
  | smul c Φ _ h => simpa only [map_smul] using h.const_smul c
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨T, hT⟩ := hl g hg
    have hh : Continuous fun w : (κ → AF F) × (κ → AF F) => ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2) :=
      continuous_const.mul (continuous_fst.dotProduct continuous_snd)
    have cfin : Continuous fun w : (κ → AF F) × (κ → AF F) =>
        ((fun i => p2 (w.2 i), fun i => p2 (w.1 i), p2 (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) :
          (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) × FiniteAdeleRing (𝓞 F) F) :=
      (continuous_pi fun i => continuous_p2.comp ((continuous_apply i).comp continuous_snd)).prodMk
        ((continuous_pi fun i => continuous_p2.comp ((continuous_apply i).comp continuous_fst)).prodMk
          (continuous_p2.comp hh))
    have hfin := (cfin.tendsto' 0 0 (by
      refine Prod.ext (funext fun i => map_zero _) (Prod.ext (funext fun i => map_zero _) ?_)
      simp)).eventually (eventually_fixed (finChar ψ) (finChar_isLocallyConstant ψ hψ.1) hg)
    have c1 : Continuous fun w : (κ → AF F) × (κ → AF F) => fun i => qA (w.1 i) :=
      continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp continuous_fst)
    have c2 : Continuous fun w : (κ → AF F) × (κ → AF F) => -trL fun i => qA (w.2 i) :=
      (continuous_trL.comp (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp continuous_snd))).neg
    have c3 : Continuous fun w : (κ → AF F) × (κ → AF F) =>
        -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (qA (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) :=
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional.comp (continuous_qA.comp hh)).neg
    have := tendsto_heis T f (c2.tendsto' 0 0 (by ext y; simp [trL_apply, dotProduct])) (c3.tendsto' 0 0 (by simp))
      (c1.tendsto' 0 0 (funext fun i => map_zero _))
    rw [hT]
    refine this.congr' (hfin.mono fun w hw => ?_)
    have e : finS ψ g (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) = g := funext hw
    show _ = l (schr ψ w (pureA F f g))
    rw [schr_pureA_eq hψ, e, hT]
    rfl

theorem continuous_schr {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Continuous fun w => l (schr ψ w Φ) := by
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  have h1 := tendsto_schr_zero hψ (comp_schr_mem_adm hψ w₀ hl) hΦ
  let c : (κ → AF F) × (κ → AF F) → ℂ := fun u => ψ (⅟(2 : AF F) * (u.1 ⬝ᵥ w₀.2 + w₀.1 ⬝ᵥ u.2) - w₀.1 ⬝ᵥ u.2)
  have hc : Continuous c := hψ.1.comp ((continuous_const.mul ((continuous_fst.dotProduct continuous_const).add
    (continuous_const.dotProduct continuous_snd))).sub (continuous_const.dotProduct continuous_snd))
  have e : ∀ u, schr ψ (w₀ + u) Φ = c u • schr ψ w₀ (schr ψ u Φ) := fun u => funext fun x => by
    simp only [schr, c, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul,
      add_assoc, add_dotProduct, dotProduct_add]
    congr 2
    ring
  have h2 := (hc.tendsto' 0 1 (by simp [c])).mul h1
  have h3 : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0) := (continuous_sub_right w₀).tendsto' _ _ (sub_self _)
  have h4 := h2.comp h3
  rw [one_mul] at h4
  refine h4.congr fun w => ?_
  have := e (w - w₀)
  rw [add_sub_cancel] at this
  rw [this, map_smul]
  rfl

theorem metrizable_group (G : Type) [Group G] [TopologicalSpace G] (_ : IsTopologicalGroup G) (_ : T2Space G)
    (_ : SecondCountableTopology G) : TopologicalSpace.MetrizableSpace G :=
  TopologicalSpace.metrizableSpace_of_t3_secondCountable G

theorem sfinite_restrict {X : Type} [MeasurableSpace X] (μ : Measure X) (_ : SigmaFinite μ) (s : Set X) :
    SFinite (μ.restrict s) := inferInstance

theorem idele_top : SecondCountableTopology (AE F E)ˣ ∧ TopologicalSpace.MetrizableSpace (AE F E)ˣ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  exact ⟨inferInstance, TopologicalSpace.metrizableSpace_of_t3_secondCountable _⟩

theorem coneIntegrand_aestronglyMeasurable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, AEStronglyMeasurable (fun p : K × (AE F E)ˣ =>
      G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2) (om' (p.1.1, h) Φ'))) 1) (μK.prod μ) := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' _ e' hE K μK μ _ _ _ X om om' om₁ om₁' hT hT₁ Φ' hΦ h
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hS₁ := IsUWeilPair.isUSplitting hT₁.weil'
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin b × Fin (a + b))
  have hΦA := polData_le_schA hM hΦ.1
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V'.J
  obtain ⟨u1, u2, u3, u4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G₁.V'.J
  obtain ⟨v1, v2⟩ := idele_top (F := F) (E := E)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G₁.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : TopologicalSpace.MetrizableSpace (UA σ G.V'.J) := metrizable_group _ t1 t4 t3
  haveI : TopologicalSpace.MetrizableSpace (UA σ G₁.V'.J) := metrizable_group _ u1 u4 u3
  haveI := hM₁.haar
  haveI : SigmaCompactSpace (UA σ G₁.V'.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite (G₁.M'.μ.restrict G₁.M'.dom) := sfinite_restrict _ (Measure.IsHaarMeasure.sigmaFinite _) _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (a + (b + 2)) → AE F E))
  have hco : Continuous G.M'.co.e := IsModuleTopology.continuous_of_linearMap G.M'.co.e.toLinearMap
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hsh : Continuous (shiftB σ H H') := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (hcA.comp Units.continuous_val).mul continuous_const

  let u : UA σ G₁.V'.J → UA σ G.V'.J → (AE F E)ˣ → ℂ := fun g k l =>
    l₀ (om₁' (g, 1) (e' (schr B.ψ (G.M'.co.e (shiftB σ H H' l)) (om' (k, h) Φ'))))
  have hmem : ∀ k l, e' (schr B.ψ (G.M'.co.e (shiftB σ H H' l)) (om' (k, h) Φ')) ∈ schA F _ := fun k l =>
    hE.maps _ (GlobalTheory.ConeMeasV.schr_mem_schA hψ _ (hS.pres _ _ hΦA))
  have hadm : ∀ g, (l₀ ∘ₗ om₁' (g, 1)) ∘ₗ e' ∈ (adeleClass F).adm _ := fun g =>
    comp_ev_mem_adm hM hM₁ hE (hS₁.adm _ _ hl₀)
  have cg : ∀ k l, Continuous fun g => u g k l := fun k l =>
    (hS₁.cont _ hl₀ _ (hmem k l)).comp (continuous_id.prodMk continuous_const)
  have ck : ∀ g l, Continuous fun k => u g k l := fun g l =>
    (hS.cont _ (comp_schr_mem_adm hψ (G.M'.co.e (shiftB σ H H' l)) (hadm g)) _ hΦA).comp
      (continuous_id.prodMk continuous_const)
  have cl : ∀ g k, Continuous (u g k) := fun g k =>
    (continuous_schr hψ (hadm g) (hS.pres (k, h) _ hΦA)).comp (hco.comp hsh)
  have m1 : ∀ g, Measurable (Function.uncurry (u g)) := fun g =>
    measurable_uncurry_of_continuous_of_measurable (ck g) fun k => (cl g k).measurable
  have m2 : Measurable (Function.uncurry fun g (p : UA σ G.V'.J × (AE F E)ˣ) => u g p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable (fun p => cg p.1 p.2) m1
  have m3 : Measurable fun x : (K × (AE F E)ˣ) × UA σ G₁.V'.J => u x.2 x.1.1.1 x.1.2 :=
    m2.comp (measurable_snd.prodMk ((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)))
  have m4 := m3.stronglyMeasurable.integral_prod_right' (ν := G₁.M'.μ.restrict G₁.M'.dom)
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine cast (congrArg StronglyMeasurable (funext fun p => ?_)) m4
  refine congrArg (integral (G₁.M'.μ.restrict G₁.M'.dom)) (funext fun g => ?_)
  exact (hl₀eq _ (hS₁.pres _ _ (hmem _ _)))

end GlobalTheory.ConeMeasSmall
