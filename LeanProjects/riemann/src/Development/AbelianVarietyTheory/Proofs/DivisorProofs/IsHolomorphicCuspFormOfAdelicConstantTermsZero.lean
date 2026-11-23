import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAdelicFormOfBoundedSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDomaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CompactEntryBounds

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.IntoCusp

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity

theorem const_mean_eq_zero {A Z : Type} [TopologicalSpace A] [SecondCountableTopology A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure A) (μ : Measure Z) [IsFiniteMeasure ν] [IsFiniteMeasure μ] (hμ : μ Set.univ ≠ 0)
    (F : A → Z → ℂ) (hc : Continuous (Function.uncurry F)) (C : ℝ) (hb : ∀ s z, ‖F s z‖ ≤ C)
    (h0 : ∀ s, ∫ z, F s z ∂μ = 0) (a : ℂ) (ha : ∀ z, ∫ s, F s z ∂ν = a) : a = 0 := by
  have hi : Integrable (Function.uncurry F) (ν.prod μ) :=
    Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hb p.1 p.2)
  have h := integral_integral_swap hi
  simp only [h0, ha, integral_zero, integral_const] at h
  have h2 : μ.real Set.univ ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨hμ, measure_ne_top _ _⟩
  exact (smul_eq_zero.1 h.symm).resolve_left h2

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lact_flow (X : Data E r) {a : GL (Fin r) E} (ha : a ∈ X.Γ) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    lact a (X.flow ξ s x) = X.flow ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) s (lact a x) := by
  funext τ
  have he : Data.emb τ.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ Data.emb τ.1 ξ := by
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have key : (a : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ τ (s τ) =
      X.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s τ) * (a : Matrix (Fin r) (Fin r) E).map τ.1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flowMat_mulVec, flowMat_mulVec, he,
      CompactEntryBounds.hermC_stab X (X.Γ_stab a ha).1, Matrix.mulVec_add, Matrix.mulVec_smul]
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ τ (s τ) * mat x τ) =
    X.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s τ) * ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key]

theorem rmul_flow (X : Data E r) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x b : Frame X.Ψ r) :
    rmul (X.flow ξ s x) b = X.flow ξ s (rmul x b) := by
  funext τ
  show (X.flowMat ξ τ (s τ) * mat x τ) * mat b τ = X.flowMat ξ τ (s τ) * (mat x τ * mat b τ)
  rw [Matrix.mul_assoc]

theorem lact_mem (X : Data E r) {a : GL (Fin r) E} (ha : a ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a x ∈ X.dom := by
  intro τ
  have hm : mat (lact a x) τ = (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    refine mul_ne_zero ?_ (hx τ).1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).ne_zero
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [hm, CompactEntryBounds.gram_stab X (X.Γ_stab a ha).1]

theorem bchar_ne (X : Data E r) (la : Wt X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : bchar la b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)] at h
  exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ _)

theorem c_ne (X : Data E r) (τ : X.Ψ) : X.c τ ≠ 0 := by
  unfold Data.c
  exact mul_ne_zero two_ne_zero (norm_ne_zero_iff.2 ((map_ne_zero _).2 X.ξ0_ne))

theorem flowMat_eq_transv (X : Data E r) {H : Matrix (Fin r) (Fin r) E} (hG : X.Gm = -Hᵀ) (ξ : Fin r → E) (τ : X.Ψ)
    (s : ℝ) : X.flowMat ξ τ s = 1 + (((X.c τ * s : ℝ) : ℂ) * Complex.I) •
      vecMulVec (fun i => τ.1 (ξ i)) (star (fun i => τ.1 (ξ i)) ᵥ* H.map τ.1) := by
  rw [flowMat_eq]
  congr 1
  ext a b
  simp only [Matrix.smul_apply, vecMulVec_apply, wv, Data.emb, smul_eq_mul, hG, Matrix.neg_apply, transpose_apply,
    map_neg, vecMul, dotProduct, Pi.star_apply, RCLike.star_def, map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem inZe_iff (X : Data E r) {H : Matrix (Fin r) (Fin r) E} (hG : X.Gm = -Hᵀ) (ξ : Fin r → E) (τ : X.Ψ) (m : Mt r) :
    InZe (H.map τ.1) (fun i => τ.1 (ξ i)) m ↔ ∃ s : ℝ, m = X.flowMat ξ τ s := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t / X.c τ, ?_⟩
    rw [flowMat_eq_transv X hG, mul_div_cancel₀ _ (c_ne X τ)]
  · rintro ⟨s, rfl⟩
    exact ⟨_, flowMat_eq_transv X hG ξ τ s⟩

end

theorem archM_mul {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem det_archM_conj {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h v : GA D V) :
    (archM V θ (h⁻¹ * v * h)).det = (archM V θ v).det := by
  rw [archM_mul, Matrix.det_mul_comm, ← archM_mul, ← mul_assoc, mul_inv_cancel, one_mul]

set_option maxHeartbeats 1000000 in

theorem isHolCusp_of_zCusp : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ P : FDSec X, (∀ k, (X k).IsBddSec (la k) (P k)) → ZCusp V (adel V dict (muPin V dict mu c) P) → IsHolCusp X la P := by
  intro D θ V S M w r hr Comp X la dict mu c Kf hM hG P hP hZ k
  have hF := GlobalTheory.T.holomorphicAdelicForm_of_boundedSection D θ V S M w r hr Comp X la dict mu c Kf hM hG P hP
  obtain ⟨e, he, -, -⟩ := GlobalTheory.HolDict.FdDom.dom_iff_frDoms D θ V S M w r hr Comp X la dict mu c Kf hM hG k
  subst hr
  haveI : IsTopologicalGroup (GA D V) := by
    haveI : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  refine ⟨hP k, fun ξ hξ x hx => ?_⟩
  set φ := adel V dict (muPin V dict mu c) P with hφ
  have hGm : (X k).Gm = -V.gramᵀ := (hG.model k).1
  obtain ⟨th, -, -, -, -, hdom, hsurj, -⟩ := hG.unif
  obtain ⟨g, γ₀, hγ₀, b, hb, hg⟩ := hsurj k x hx
  obtain ⟨γ, hγ, hfr, hu⟩ := hG.base.2.2 g
  have hy := hdom g
  unfold FrAt at hfr
  rw [hg] at hfr hu hy
  simp only at hfr hu hy
  set y := rmul (lact γ₀ x) b with hydef
  set η : Fin V.rank → D.host.E := (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ ξ with hη
  have hη0 : herm (X k).Gm η η = 0 := by rw [hη, ((X k).Γ_stab γ₀ hγ₀).1, hξ.2.1]
  have hiso : IsoVec V η := by
    refine ⟨fun h0 => hξ.2.2 ?_, ?_⟩
    · have : ((γ₀⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ η = ξ := by
        rw [hη, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [← this, h0, Matrix.mulVec_zero]
    · rw [← neg_eq_zero, ← hη0, hGm]
      simp only [herm, dotProduct, mulVec, Matrix.neg_apply, transpose_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
      have : (D.sp.cm.sig : D.host.E →+* D.host.E) (η a') = cc (η a') := rfl
      rw [this]
      ring
  have hZe : ∀ ρ (m : Mt V.rank), InZe (gramAt D V ρ) (fun i => tauE D ρ (η i)) m ↔
      ∃ s : ℝ, m = (X k).flowMat η (e ρ) s := by
    intro ρ m
    rw [← inZe_iff (X k) hGm η (e ρ) m, he ρ]
    rfl
  obtain ⟨L, hL1, -, hLc, hLm, hLi, -, -, hcomm, -⟩ := GlobalTheory.T.exists_archimedean_lift_unitaryGroupProduct D θ V hG.inf
  obtain ⟨-, -, hZa, hZb, -⟩ := GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hG.inf η hiso
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, hfin, hdec⟩ := GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hG.inf η hiso
  obtain ⟨ex, hex, -⟩ := hG.wt
  set f : ((X k).Ψ → ℝ) → ℂ := fun s => P k ((X k).flow ξ (fun τ => (s τ : ℂ)) x) with hf
  set C₀ : ℂ := c k * mu g * bchar (la k) b with hC₀
  have hC₀ne : C₀ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (hG.cNe k) ?_) (bchar_ne (X k) (la k) hb)
    rw [← norm_ne_zero_iff, hG.muUnit.2.1 g]
    exact one_ne_zero

  have key : ∀ (s : (X k).Ψ → ℝ), ∀ v ∈ GinfC V, (∀ ρ, archM V (θ ρ) v = (X k).flowMat η (e ρ) (s (e ρ))) →
      φ (v * (γ * g)) = C₀ * f s := by
    intro s v hv hvs
    have hu' : (γ * g)⁻¹ * v * (γ * g) ∈ GinfC V := by
      have := (MonoidHom.normal_ker (finHom V)).conj_mem v hv (γ * g)⁻¹
      rwa [inv_inv] at this
    obtain ⟨γ', hγ', x', hd, hx'⟩ := hu _ hu'
    have e1 : v * (γ * g) = γ * (g * ((γ * g)⁻¹ * v * (γ * g))) := by group
    have e2 : γ * g * ((γ * g)⁻¹ * v * (γ * g)) = v * (γ * g) := by group
    have e3 : x' = (X k).flow η (fun τ => (s τ : ℂ)) y := by
      funext τ
      obtain ⟨ρ, rfl⟩ := e.surjective τ
      have h1 := hx' ρ (e ρ) (he ρ)
      have h2 := hfr ρ (e ρ) (he ρ)
      rw [e2, archM_mul, hvs] at h1
      show mat x' (e ρ) = (X k).flowMat η (e ρ) (s (e ρ)) * mat y (e ρ)
      rw [h1, h2, Matrix.mul_assoc]
      rfl
    have e4 : mu ((γ * g)⁻¹ * v * (γ * g)) = 1 := by
      rw [hex _ hu']
      refine Finset.prod_eq_one fun ρ _ => ?_
      rw [det_archM_conj, hvs, det_flowMat _ hη0, _root_.one_zpow]
    have hxs : (X k).flow ξ (fun τ => (s τ : ℂ)) x ∈ (X k).dom := flow_real_mem_dom (X k) hξ.2.1 s x hx
    have hys : (X k).flow η (fun τ => (s τ : ℂ)) y ∈ (X k).dom := flow_real_mem_dom (X k) hη0 s y hy
    rw [e1, hF.aut.left γ hγ, hφ, adel_muPin, hd, hG.muUnit.1, e4, e3]
    simp only
    rw [(hP k).1.2.2 γ' hγ' _ hys, hG.chi k γ' hγ', hydef, ← rmul_flow, hη, ← lact_flow (X k) hγ₀,
      (hP k).1.2.1 _ (lact_mem (X k) hγ₀ hxs) b hb, (hP k).1.2.2 γ₀ hγ₀ _ hxs, hG.chi k γ₀ hγ₀, hC₀, hf]
    ring

  set m : ((X k).Ψ → ℝ) → D.what₂.Tau → Mt V.rank := fun s ρ => (X k).flowMat η (e ρ) (s (e ρ)) with hm
  have hmU : ∀ s, m s ∈ UG (gramAt D V) := by
    intro s
    obtain ⟨z, -, -, hz⟩ := hZb (m s) fun ρ => (hZe ρ _).2 ⟨_, rfl⟩
    have := hLm z
    rwa [funext hz] at this
  have hmc : Continuous m := by
    refine continuous_pi fun ρ => ?_
    simp only [hm, flowMat_eq]
    fun_prop
  have hιc : Continuous fun s => L (m s) := hLc.comp_continuous hmc hmU

  obtain ⟨U₀, hU₀, hlev⟩ := hF.aut.level
  let U : Subgroup (GA D V) := U₀.comap (MulAut.conj (γ * g)⁻¹).toMonoidHom
  have hUo : IsOpen (U : Set (GA D V)) := by
    have : Continuous fun a : GA D V => (γ * g)⁻¹ * a * (γ * g)⁻¹⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
    exact hU₀.preimage this
  have hval : ∀ z ∈ ZI V η, ∃ t : (X k).Ψ → ℝ, ∀ s, φ (z * (L (m s) * (γ * g))) = C₀ * f (t + s) := by
    intro z hz
    obtain ⟨q, -, hq, u, huZ, huI, a, -, haF, haU, rfl⟩ := hdec U hUo z hz
    choose t ht using fun ρ => (hZe ρ _).1 (hZa u huZ ρ)
    refine ⟨fun τ => t (e.symm τ), fun s => ?_⟩
    obtain ⟨hI, hA⟩ := hL1 _ (hmU s)
    have e1 : q * u * a * (L (m s) * (γ * g)) = q * ((u * L (m s) * (γ * g)) * ((γ * g)⁻¹ * a * (γ * g)⁻¹⁻¹)) := by
      rw [mul_assoc (q * u) a, ← mul_assoc a, hcomm a haF _ hI]
      group
    rw [e1, hF.aut.left q hq, hlev ((γ * g)⁻¹ * a * (γ * g)⁻¹⁻¹) haU ((MonoidHom.normal_ker (infHom V)).conj_mem a haF _)]
    refine key _ _ (mul_mem huI hI) fun ρ => ?_
    rw [archM_mul, hA, ht, hm]
    simp only
    rw [flowMat_mul _ hη0]
    simp
  have hper : ∀ p ∈ (X k).periods (la k), ∀ s, f (p + s) = f s := by
    intro p hp s
    have h1 : (X k).flow ξ (fun τ => ((p + s) τ : ℂ)) x =
        (X k).flow ξ (fun τ => (p τ : ℂ)) ((X k).flow ξ (fun τ => (s τ : ℂ)) x) := by
      rw [flow_flow (X k) hξ.2.1]
      congr 1
      funext τ
      simp
    simp only [hf]
    rw [h1]
    exact sec_periodic (X k) (la k) (P k) (hP k).1 hξ.1 hξ.2.1 hp _ (flow_real_mem_dom (X k) hξ.2.1 s x hx)
  unfold Data.fj
  split_ifs with h1 h2
  swap
  · rfl
  swap
  · rfl
  obtain ⟨-, hD, -, hDf⟩ := h2.choose_spec
  obtain ⟨hμ0, hμt⟩ := hfin μ 𝓕 hμ h𝓕
  obtain ⟨C, hC⟩ := hF.bdd
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hμt.lt_top⟩
  haveI : IsFiniteMeasure (volume.restrict h2.choose) := ⟨by rw [Measure.restrict_apply_univ]; exact hDf⟩
  have h0 : C₀ * ∫ s in h2.choose, f s = 0 := by
    refine const_mean_eq_zero (volume.restrict h2.choose) (μ.restrict 𝓕) (by rwa [Measure.restrict_apply_univ])
      (fun s z => φ ((z : GA D V) * (L (m s) * (γ * g)))) ?_ C (fun _ _ => hC _) (fun s => hZ η hiso μ 𝓕 hμ h𝓕 _) _ ?_
    · exact hF.aut.cont.comp ((continuous_subtype_val.comp continuous_snd).mul
        ((hιc.comp continuous_fst).mul continuous_const))
    · intro z
      obtain ⟨t, ht⟩ := hval z z.2
      simp only [ht]
      rw [integral_const_mul, FundamentalDomainTranslate.fd_translate _ _ hD f hper t]
  have h3 := (mul_eq_zero.1 h0).resolve_left hC₀ne
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one]
  exact mul_eq_zero_of_right _ h3

end GlobalTheory.HolDict.IntoCusp
