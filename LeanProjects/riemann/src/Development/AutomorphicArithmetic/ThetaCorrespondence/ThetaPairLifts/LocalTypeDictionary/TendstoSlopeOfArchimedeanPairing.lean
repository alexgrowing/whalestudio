import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MetaplecticScalarDerivativeNonempty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomialStatement

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory Filter Topology
open scoped SchwartzMap Classical Matrix
noncomputable section
namespace GlobalTheory.ArchLinePair
theorem tendsto_slope_of_archimedean_pairing (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (P : V → V → ℝ) (hp : IsPairing P)
    (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
    (hAc : ∀ v, Continuous fun t => A t v) (hA0 : ∀ v, A 0 v = v) (hAm : ∀ s t v, A (s + t) v = A s (A t v))
    (hAo : ∀ t v v', omega P (A t v) (A t v') = omega P v v')
    (hT0 : ∀ f, T 0 f = f) (hTm : ∀ s t f, T (s + t) f = T s (T t f))
    (hTi : ∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f))
    (hTu : ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ t f, ∫⁻ x, ‖T t f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ)
    (hTc : ∀ f y, Continuous fun t => T t f y) (f : 𝓢(V, ℂ)) :
    ∃ g : 𝓢(V, ℂ), Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 g) := by
  set n := Module.finrank ℝ V with hn
  obtain ⟨C, φ, hφ, hC⟩ := exists_pairing_coords V P hp n rfl
  let a : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have ha : ∀ t v, a t (φ v) = φ (A t v) := fun t v => by simp [a]
  let g : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fun t => LinearMap.toMatrix' (a t)
  have hg : ∀ t w, g t *ᵥ w = a t w := fun t w => LinearMap.toMatrix'_mulVec _ _
  have hext : ∀ M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, (∀ v, M *ᵥ φ v = N *ᵥ φ v) → M = N := by
    intro M N h
    refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
    obtain ⟨v, rfl⟩ := φ.surjective w
    simpa using h v
  have hgc : Continuous g := by
    refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun t => φ (A t (φ.symm (Pi.single j 1))) :=
      φ.toLinearMap.continuous_of_finiteDimensional.comp (hAc _)
    have h2 := (continuous_apply i).comp h1
    refine h2.congr fun t => ?_
    simp only [g, a, Function.comp_apply, LinearMap.toMatrix'_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hg0 : g 0 = 1 := hext _ _ fun v => by rw [hg, ha, hA0, Matrix.one_mulVec]
  have hgm : ∀ s t, g (s + t) = g s * g t := fun s t => hext _ _ fun v => by
    rw [← Matrix.mulVec_mulVec, hg, hg, hg, ha, ha, ha, hAm]
  have hgs : ∀ t, g t ∈ Matrix.symplecticGroup (Fin n) ℝ := fun t => by
    obtain ⟨M, hM⟩ := GlobalTheory.exists_symplecticGroup_of_sympl (Fin n) (a t) fun w w' => by
      obtain ⟨v, rfl⟩ := φ.surjective w
      obtain ⟨v', rfl⟩ := φ.surjective w'
      rw [ha, ha, hφ, hφ, hAo]
    rw [hext (g t) M fun v => by rw [hg, hM]]
    exact M.2
  obtain ⟨Z, hZ, hgZ⟩ := GlobalTheory.T.exists_symplecticLie_eq_exp_oneParam (Fin n) g hgc hg0 hgm hgs
  let B : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  let Bi : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  have hB : ∀ h, ⇑(B h) = ⇑h ∘ ⇑C := fun h => rfl
  have hBi : ∀ h, ⇑(Bi h) = ⇑h ∘ ⇑C.symm := fun h => rfl
  have hBBi : ∀ h, B (Bi h) = h := fun h => by ext x; simp [hB, hBi]
  have hBiB : ∀ h, Bi (B h) = h := fun h => by ext x; simp [hB, hBi]
  let S : ℝ → GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := fun t =>
    Bi.toLinearMap ∘ₗ T t ∘ₗ B.toLinearMap
  have hS : ∀ t h, S t h = Bi (T t (B h)) := fun t h => rfl
  have hint : ∀ h : 𝓢(V, ℂ), ∫⁻ x, ‖Bi h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 ∂(Measure.map C.symm volume) := fun h =>
    (lintegral_map_equiv (fun x => ‖h x‖ₑ ^ 2) C.symm.toHomeomorph.toMeasurableEquiv).symm
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq hP (Fin n) Z hZ S (LinearMap.ext fun h => by rw [hS, hT0, hBiB]; rfl)
    (fun s t => LinearMap.ext fun h => by
      show S (s + t) h = S s (S t h)
      rw [hS, hS, hS, hBBi, hTm])
    (fun t w h h₁ e => by
      obtain ⟨v, rfl⟩ := φ.surjective w
      have h1 : ⇑(B h₁) = schrF P v ⇑(B h) := by rw [hB, hB, hC, e]
      have h2 := hTi t v _ _ h1
      rw [← hgZ t, hg, ha, hS, hS, hBi, h2, ← hBBi (T t (B h)), hB, hC, hBiB]
      funext x; simp)
    (fun t h => by
      rw [hS, hint, hTu _ (C.symm.isAddHaarMeasure_map volume), ← hint, hBiB])
    (fun h x => hTc (B h) (C.symm x))
  refine ⟨_, ((B.continuous.tendsto _).comp (hc (Bi f))).congr fun t => ?_⟩
  simp only [Function.comp_apply, ← Complex.coe_smul, map_smul, map_sub, hS, hBBi]
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
theorem exists_orbit_pair_archimedean_line (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E)
    (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (δ : ℝ → UA σ X.J × UA σ W.J) (hδc : Continuous δ)
    (hδ0 : δ 0 = 1) (hδm : ∀ s t, δ (s + t) = δ s * δ t) (hδ1 : ∀ t, (δ t).1 ∈ UAt σ X (evI F))
    (hδ2 : ∀ t, (δ t).2 ∈ UAt σ W (evI F)) (f : SInf F (Fin n × Fin d)) :
    ∃ (c : ℝ → SInf F (Fin n × Fin d)) (g : SInf F (Fin n × Fin d)), c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 g) ∧ ∀ t, Acts (evI F) (om (δ t)) ⇑f ⇑(c t) := by
  have hs := IsUWeilPair.isUSplitting hW
  have hex : ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (δ t)) ⇑f ⇑f₁ := by
    intro t f
    refine acts_of_comm ψ hψ (om (δ t)) (fun Φ hΦ => hs.pres _ Φ hΦ) (fun u hu p q Φ hΦ => ?_) f
    have he : M.co.e (u • M.co.e.symm (p, q)) = (u • p, u • q) := by
      rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := hs.impl (δ t) (u • M.co.e.symm (p, q)) Φ hΦ
    simp only [Darboux.rho, he, actAB_fin (hδ1 t) (hδ2 t) u hu] at h2
    exact h2
  choose S hS using hex
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  have hr0 : r₀ 0 ≠ 0 := by
    show g₀ 0 ≠ 0
    rw [hg₀0]; exact one_ne_zero
  have hinj : ∀ f₁ f₂ : SInf F (Fin n × Fin d), tens (evI F) ⇑f₁ r₀ = tens (evI F) ⇑f₂ r₀ → f₁ = f₂ :=
    fun f₁ f₂ h => DFunLike.coe_injective (GlobalTheory.ArchFam.tens_inj r₀ hrr 0 hr0 _ _ h)
  have key : ∀ t (f : SInf F (Fin n × Fin d)), om (δ t) (tens (evI F) ⇑f r₀) = tens (evI F) ⇑(S t f) r₀ :=
    fun t f => hS t f r₀ (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r₀ = tens (evI F) ⇑f r₀ + tens (evI F) ⇑g r₀ := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) ⇑(c • f) r₀ = c • tens (evI F) ⇑f r₀ := by
    intro c f; funext x; simp [tens, mul_assoc]
  let T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := S t
      map_add' := fun f g => hinj _ _ (by rw [← key, tadd, map_add, key, key, tadd])
      map_smul' := fun c f => hinj _ _ (by rw [← key, tsmul, map_smul, key, RingHom.id_apply, tsmul]) }
  have hT : ∀ t f, T t f = S t f := fun t f => rfl
  have hT0 : ∀ f, T 0 f = f := fun f => hinj _ _ (by rw [hT, ← key, hδ0, map_one, Module.End.one_apply])
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := inferInstance
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.ArchLinePair.tendsto_slope_of_archimedean_pairing hP (trP F (Fin n × Fin d)) (Coord.isPairing_trP _)
    (fun t => amap M (δ t)) T (fun v => (continuous_amap M v).comp hδc)
    (fun v => by
      obtain ⟨w, rfl⟩ : ∃ w, Coord.coordI M w = v := ⟨_, Coord.coordI_lift M v⟩
      rw [amap_coordI, hδ0, actAB_one])
    (fun s t v => by
      obtain ⟨w, rfl⟩ : ∃ w, Coord.coordI M w = v := ⟨_, Coord.coordI_lift M v⟩
      rw [amap_coordI, amap_coordI, amap_coordI, hδm, actAB_mul])
    (fun t v v' => by
      obtain ⟨w, rfl⟩ : ∃ w, Coord.coordI M w = v := ⟨_, Coord.coordI_lift M v⟩
      obtain ⟨w', rfl⟩ : ∃ w, Coord.coordI M w = v' := ⟨_, Coord.coordI_lift M v'⟩
      rw [amap_coordI, amap_coordI, Coord.omega_coordI, Coord.omega_coordI]
      simp only [Coord.sympM, symp, hTens_actAB])
    hT0
    (fun s t f => hinj _ _ (by rw [hT, hT, hT, ← key, hδm, map_mul, Module.End.mul_apply, key, key]))
    (fun t v f f₁ hf => by
      have hc : (locV (M.co.e (GlobalTheory.ArchFam.wv M v)).1, locV (M.co.e (GlobalTheory.ArchFam.wv M v)).2) = v :=
        Coord.coordI_lift M v
      have e1 : tens (evI F) ⇑f₁ r₀ = M.co.rho ψ (GlobalTheory.ArchFam.wv M v) (tens (evI F) ⇑f r₀) := by
        rw [GlobalTheory.ArchFam.rho_tens ψ hψ M.co _ (GlobalTheory.ArchFam.at_wv M v) _ _ hrr, hc, ← hf]
      have e2 := hs.impl (δ t) (GlobalTheory.ArchFam.wv M v) _ (hR f).2
      have hat : At (evI F) (actAB (cA σ) (δ t) (GlobalTheory.ArchFam.wv M v)) := fun u hu => by
        rw [← actAB_smul, GlobalTheory.ArchFam.at_wv M v u hu, actAB, Matrix.mul_zero, Matrix.zero_mul]
      apply GlobalTheory.ArchFam.tens_inj r₀ hrr 0 hr0
      rw [hT, hT, ← key, e1, e2, key, GlobalTheory.ArchFam.rho_tens ψ hψ M.co _ hat _ _ hrr]
      rfl)
    (fun μ hμ t f => by
      obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := GlobalTheory.ArchimedeanUnitaryL2.exists_haar F _ μ g₀ hg₀ hr0
      have hU := hs.unit μA hμA (δ t) (tens (evI F) f r₀) (hR f).2
      rw [key] at hU
      exact (ENNReal.mul_right_inj hc0 hct).1 (((hc (S t f)).symm.trans hU).trans (hc f)))
    (fun f y => by
      let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (liftV y)
      have hpure : ∀ (f' : SInf F (Fin n × Fin d)) g', l (pureA F (⇑f') g') = g' 0 * f' y := fun f' g' => by
        show f' (locV (liftV y)) * g' 0 = _
        rw [Coord.loc_lift, mul_comm]
      have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := fun g' _ =>
        ⟨g' 0 • ((BoundedContinuousFunction.evalCLM ℂ y).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f' => hpure f' g'⟩
      refine ((hs.cont l hl _ (hR f).2).comp hδc).congr fun t => ?_
      rw [Function.comp_apply, key]
      exact (hpure (S t f) g₀).trans (by rw [hg₀0, one_mul, hT]))
    f
  exact ⟨fun t => T t f, g, hT0 f, hg, fun t => hS t f⟩
theorem exists_curve_along_archimedean_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (c t) r) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ _ hW γ hγ f r hr
  obtain ⟨c, g, hc0, hg, hc⟩ := _root_.GlobalTheory.ArchLinePair.exists_orbit_pair_archimedean_line hP M ψ χX χW om hψ hW (fun t => (γ (Multiplicative.ofAdd t), 1))
    ((hγ.1.comp continuous_ofAdd).prodMk continuous_const) (by rw [ofAdd_zero, map_one]; rfl)
    (fun s t => by rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]) (fun t => hγ.2 _)
    (fun t u _ => by simp [mat]) f
  exact ⟨c, g, fun t => hc t r hr, by rw [hc0]; exact hg⟩
end GlobalTheory.ArchLinePair
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_line_pairing_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (c t) r) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  first | exact @_root_.GlobalTheory.ArchLinePair.exists_curve_along_archimedean_line | exact _root_.GlobalTheory.ArchLinePair.exists_curve_along_archimedean_line | (intros; apply _root_.GlobalTheory.ArchLinePair.exists_curve_along_archimedean_line <;> assumption)
end
