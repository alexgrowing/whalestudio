import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLaplacianPolData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeAlongLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar GlobalTheory.ThK.TowerInt
open GlobalTheory.ThK.LiftConst GlobalTheory.ThK.SplitInv GlobalTheory.ThKLiftCusp GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace UpperTheory.LiftDer

open GlobalTheory.ArchUniq
open scoped SchwartzMap Classical

private theorem hasDerivAt_exp_lin {K ι m G : Type} [RCLike K] [Fintype ι] [Fintype m] [DecidableEq m]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : (ι → Matrix m m K) →ₗ[ℝ] G) (Y : ι → Matrix m m K) :
    HasDerivAt (fun t : ℝ => L fun w => NormedSpace.exp (t • Y w)) (L Y) 0 := by
  letI : NormedRing (Matrix m m K) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m K) := Matrix.linftyOpNormedAlgebra
  haveI : FiniteDimensional ℝ (Matrix m m K) := inferInstance
  haveI : CompleteSpace (Matrix m m K) := FiniteDimensional.complete ℝ _
  have h : HasDerivAt (fun t : ℝ => fun w => NormedSpace.exp (t • Y w)) Y 0 := by
    refine hasDerivAt_pi.2 fun w => ?_
    have h0 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Y w) (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h0
    exact h0
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

private def quadL (l : Type) [Fintype l] [DecidableEq l] :
    Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] (GlobalTheory.RealWeil.Sch l →L[ℂ] GlobalTheory.RealWeil.Sch l) where
  toFun := GlobalTheory.RealWeil.quad
  map_add' X Y := by
    simp only [GlobalTheory.RealWeil.quad, Matrix.add_mul, Matrix.add_apply, add_div, Complex.ofReal_add, add_smul,
      Finset.sum_add_distrib, smul_add]
    abel
  map_smul' r X := by
    simp only [GlobalTheory.RealWeil.quad, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_div_assoc, Complex.ofReal_mul,
      mul_smul, RingHom.id_apply, ← Finset.smul_sum]
    rw [smul_comm, Complex.coe_smul]

private theorem slope_lin (hP : GlobalTheory.FunPr.Hypotheses₂) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (P : V → V → ℝ) (hp : IsPairing P) :
    ∃ Q : ((V × V) →ₗ[ℝ] (V × V)) →ₗ[ℝ] Module.End ℂ 𝓢(V, ℂ),
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
    (_ : ∀ v, Continuous fun t => A t v) (_ : ∀ v, A 0 v = v) (_ : ∀ s t v, A (s + t) v = A s (A t v))
    (_ : ∀ t v v', omega P (A t v) (A t v') = omega P v v')
    (_ : ∀ f, T 0 f = f) (_ : ∀ s t f, T (s + t) f = T s (T t f))
    (_ : ∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f))
    (_ : ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ t f, ∫⁻ x, ‖T t f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ)
    (_ : ∀ f y, Continuous fun t => T t f y) (A' : (V × V) →ₗ[ℝ] (V × V))
    (_ : ∀ v, HasDerivAt (fun t => A t v) (A' v) 0),
    ∃ a : ℂ, ∀ f : 𝓢(V, ℂ), Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 (a • f + Q A' f)) := by
  set n := Module.finrank ℝ V with hn
  obtain ⟨C, φ, hφ, hC⟩ := exists_pairing_coords V P hp n rfl
  let B : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  let Bi : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let G : ((V × V) →ₗ[ℝ] (V × V)) →ₗ[ℝ] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    LinearMap.toMatrix'.toLinearMap ∘ₗ φ.conj.toLinearMap
  have hG : ∀ N v, G N *ᵥ φ v = φ (N v) := fun N v => by
    simp [G, LinearMap.toMatrix'_mulVec, LinearEquiv.conj_apply]
  refine ⟨{ toFun := fun N => B.toLinearMap ∘ₗ (quadL (Fin n) (G N)).toLinearMap ∘ₗ Bi.toLinearMap
            map_add' := fun N N' => by ext f x; simp
            map_smul' := fun r N => by ext f x; simp [B] }, ?_⟩
  intro A T hAc hA0 hAm hAo hT0 hTm hTi hTu hTc A' hA'
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
  have hZG : Z = G A' := hext _ _ fun v => by
    let L : (Unit → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
      { toFun := fun N => N () *ᵥ φ v
        map_add' := fun N N' => Matrix.add_mulVec _ _ _
        map_smul' := fun r N => Matrix.smul_mulVec r (N ()) (φ v) }
    have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z) *ᵥ φ v) (Z *ᵥ φ v) 0 :=
      hasDerivAt_exp_lin L fun _ => Z
    have h2 : HasDerivAt (fun t : ℝ => φ (A t v)) (φ (A' v)) 0 :=
      (LinearMap.toContinuousLinearMap φ.toLinearMap).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hA' v)
    simp only [← hgZ, hg, ha] at h1
    rw [hG]
    exact h1.unique h2
  have hB : ∀ h, ⇑(B h) = ⇑h ∘ ⇑C := fun h => rfl
  have hBi : ∀ h, ⇑(Bi h) = ⇑h ∘ ⇑C.symm := fun h => rfl
  have hBBi : ∀ h, B (Bi h) = h := fun h => by ext x; simp [hB, hBi]
  have hBiB : ∀ h, Bi (B h) = h := fun h => by ext x; simp [hB, hBi]
  let S : ℝ → GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := fun t =>
    Bi.toLinearMap ∘ₗ T t ∘ₗ B.toLinearMap
  have hS : ∀ t h, S t h = Bi (T t (B h)) := fun t h => rfl
  have hint : ∀ h : 𝓢(V, ℂ), ∫⁻ x, ‖Bi h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 ∂(Measure.map C.symm volume) := fun h =>
    (lintegral_map_equiv (fun x => ‖h x‖ₑ ^ 2) C.symm.toHomeomorph.toMeasurableEquiv).symm
  obtain ⟨c, hc⟩ := GlobalTheory.T.schwartz_one_parameter_group_formula hP (Fin n) Z hZ S (LinearMap.ext fun h => by rw [hS, hT0, hBiB]; rfl)
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
  refine ⟨c, fun f => ?_⟩
  have h := (B.continuous.tendsto _).comp (hc (Bi f))
  rw [map_add, map_smul, hBBi, hZG] at h
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, ← Complex.coe_smul, map_smul, map_sub, hS, hBBi]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

open GlobalTheory.ArchLinePair in

private theorem orbit_lin (hP : GlobalTheory.FunPr.Hypotheses₂) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E)
    (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) :
    ∃ Q : (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) →ₗ[ℝ]
        Module.End ℂ (SInf F (Fin n × Fin d)),
    ∀ (δ : ℝ → UA σ X.J × UA σ W.J) (_ : Continuous δ)
    (_ : δ 0 = 1) (_ : ∀ s t, δ (s + t) = δ s * δ t) (_ : ∀ t, (δ t).1 ∈ UAt σ X (evI F))
    (_ : ∀ t, (δ t).2 ∈ UAt σ W (evI F)) A' (_ : ∀ v, HasDerivAt (fun t => amap M (δ t) v) (A' v) 0),
    ∃ a : ℂ, ∀ f : SInf F (Fin n × Fin d), ∃ c : ℝ → SInf F (Fin n × Fin d), c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (a • f + Q A' f)) ∧
        ∀ t, Acts (evI F) (om (δ t)) ⇑f ⇑(c t) := by
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := inferInstance
  obtain ⟨Q, hQ⟩ := slope_lin hP (trP F (Fin n × Fin d)) (Coord.isPairing_trP _)
  refine ⟨Q, fun δ hδc hδ0 hδm hδ1 hδ2 A' hA' => ?_⟩
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
  obtain ⟨a, hg⟩ := hQ
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
    A' hA'
  exact ⟨a, fun f => ⟨fun t => T t f, hT0 f, hg f, fun t => hS t f⟩⟩

open GlobalTheory.ArchLinePair GlobalTheory.RealLift.OneParam in

private theorem amap_lin (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (M : Model σ X W) :
    ∃ N : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ]
      (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))),
    ∀ (γ : ℝ → UA σ X.J) (Y : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ), (∀ t, At (evI F) (mat (γ t) - 1)) →
      (∀ t w, (mat (γ t)).map (piInf (τ w)) = NormedSpace.exp (t • Y w)) →
      ∀ v, HasDerivAt (fun t => amap M (γ t, 1) v) (N Y v) 0 := by
  have := hcm.1
  obtain ⟨ξ, hξ⟩ := exists_moved hcm
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hcm hξ (τ w).1
  have hadd : ∀ Y Y' : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ,
      GlobalTheory.RealLift.OneParam.liftM τ ξ (Y + Y') = GlobalTheory.RealLift.OneParam.liftM τ ξ Y + GlobalTheory.RealLift.OneParam.liftM τ ξ Y' := fun Y Y' => by
    refine eq_of_at hcm τ (at_sub (at_liftM _ _ _) (at_add (at_liftM _ _ _) (at_liftM _ _ _))) fun w => ?_
    rw [Matrix.map_add _ (map_add _), GlobalTheory.RealLift.OneParam.liftM_map τ hξ', GlobalTheory.RealLift.OneParam.liftM_map τ hξ', GlobalTheory.RealLift.OneParam.liftM_map τ hξ', Pi.add_apply]
  have hsmul : ∀ (r : ℝ) (Y : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ),
      GlobalTheory.RealLift.OneParam.liftM τ ξ (r • Y) = realAd F r • GlobalTheory.RealLift.OneParam.liftM τ ξ Y := fun r Y => by
    refine eq_of_at hcm τ (at_sub (at_liftM _ _ _) fun u hu => ?_) fun w => ?_
    · rw [smul_comm, at_liftM _ _ _ u hu, smul_zero]
    · rw [GlobalTheory.RealScalar.realAd_smul_map σ τ hcm, GlobalTheory.RealLift.OneParam.liftM_map τ hξ', GlobalTheory.RealLift.OneParam.liftM_map τ hξ', Pi.smul_apply, Complex.coe_smul]
  let N₀ : Matrix (Fin n) (Fin n) (AE F E) →
      (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) := fun m =>
    { toFun := fun v => Coord.coordI M (m * GlobalTheory.ArchFam.wv M v)
      map_add' := fun v v' => by
        simp only [GlobalTheory.ArchFam.wv, Prod.fst_add, Prod.snd_add, Coord.lift_add, ← Prod.mk_add_mk, map_add,
          Matrix.mul_add, Coord.coordI_add]
      map_smul' := fun c v => by
        simp only [GlobalTheory.ArchFam.wv, Prod.smul_fst, Prod.smul_snd, Coord.lift_smul, ← Prod.smul_mk, map_smul,
          Matrix.mul_smul, Coord.coordI_smul, RingHom.id_apply] }
  have hN₀ : ∀ m v, N₀ m v = Coord.coordI M (m * GlobalTheory.ArchFam.wv M v) := fun m v => rfl
  let N : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] _ :=
    { toFun := fun Y => N₀ (GlobalTheory.RealLift.OneParam.liftM τ ξ Y)
      map_add' := fun Y Y' => LinearMap.ext fun v => by
        rw [LinearMap.add_apply, hN₀, hN₀, hN₀, hadd, Matrix.add_mul, Coord.coordI_add]
      map_smul' := fun r Y => LinearMap.ext fun v => by
        rw [LinearMap.smul_apply, hN₀, hN₀, hsmul, Matrix.smul_mul, Coord.coordI_smul, RingHom.id_apply] }
  refine ⟨N, fun γ Y hat hY v => ?_⟩
  have h1 := (hasDerivAt_exp_lin (LinearMap.applyₗ v ∘ₗ N) Y).add_const (v - N (fun _ => 1) v)
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  have e : mat (γ t) = 1 + GlobalTheory.RealLift.OneParam.liftM τ ξ ((fun w => NormedSpace.exp (t • Y w)) - fun _ => 1) := by
    refine eq_of_at hcm τ ?_ fun w => ?_
    · rw [← sub_sub]
      exact at_sub (hat t) (at_liftM _ _ _)
    · rw [hY, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), GlobalTheory.RealLift.OneParam.liftM_map τ hξ']
      simp
  have e2 : amap M (γ t, 1) v = v + N ((fun w => NormedSpace.exp (t • Y w)) - fun _ => 1) v := by
    change Coord.coordI M (mat (γ t) * GlobalTheory.ArchFam.wv M v * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ) =
      v + Coord.coordI M (_ * GlobalTheory.ArchFam.wv M v)
    rw [Matrix.transpose_one, Matrix.mul_one, e, Matrix.add_mul, Matrix.one_mul, Coord.coordI_add]
    congr 1
    exact Coord.coordI_lift M v
  show amap M (γ t, 1) v = N _ v + _
  rw [e2, map_sub, LinearMap.sub_apply]
  abel

open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH in

private theorem vac_lin (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (h : IsPair B M χX χW om r s r' s') :
    ∃ (f₀ : SInf F (Fin n × Fin d)) (Δ : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] SInf F (Fin n × Fin d)),
      f₀ ≠ 0 ∧ ∀ γ ∈ Lines σ X, ∀ Y : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ,
        (∀ (t : ℝ) w, (mat (γ (Multiplicative.ofAdd t))).map (piInf (B.emb w)) = NormedSpace.exp (t • Y w)) →
        ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f₀ (Δ Y) := by
  have hb := h.base
  choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A := ⟨mul_one _, hC1, hA1⟩
  obtain ⟨Φ₀, hΦ₀⟩ := i_fockex i_derex F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := h.weil
  obtain ⟨d', hd', hB⟩ := hwp.2.1
  have hΦ := GlobalTheory.PolActsPf.isFockMap_flip hΦ₀ hd'
  generalize Φ₀ ∘ₗ (GlobalTheory.PolActsPf.flipT (InfinitePlace F) r s r' s').toLinearMap = Φ at hΦ
  obtain ⟨c, hact⟩ := i_liescalar hP i_derex (i_vacline i_derex) F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ d' Complex.I 1 C A Φ
    (om.comp (MonoidHom.inl _ _)) hb.cm hb.std fr' hΦ hB.1
  choose A' hAA' hA'A using fun w => GlobalTheory.ThKFockDer.frame_inv (hA w)
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Tens F r' s' r s, T₀ ≠ 0 := by
    refine ⟨PiTensorProduct.tprod ℂ fun _ => 1, fun e => ?_⟩
    have e' := congrArg (PiTensorProduct.lift
      (MultilinearMap.mkPiAlgebra ℂ (InfinitePlace F) (Formalism.BasicNotions.TH.Pol r' s' r s))) e
    simp at e'
  let D : InfinitePlace F → Mat r s →ₗ[ℂ] Module.End ℂ (Tens F r' s' r s) := fun w =>
    { toFun := fun Y => atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol r' s' r s) w
        (fockAct2 r' s' r s Y + (c w * Y.trace) • 1)
      map_add' := fun Y Y' => by
        rw [← atPl_add, map_add, Matrix.trace_add, mul_add, add_smul, add_add_add_comm]
      map_smul' := fun r Y => by
        rw [RingHom.id_apply, ← atPl_smul, map_smul, Matrix.trace_smul,
          smul_add, smul_smul, smul_eq_mul, mul_left_comm] }
  let L : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Mat r s := fun w =>
    { toFun := fun Z => A' w * Z * A w
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r X => by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  refine ⟨Φ T₀, ∑ w, (Φ ∘ₗ LinearMap.applyₗ T₀ ∘ₗ D w).restrictScalars ℝ ∘ₗ L w ∘ₗ LinearMap.proj w,
    fun e => hT₀ (hΦ.1 (e.trans (map_zero Φ).symm)), fun γ hγ Y hY => ?_⟩
  have hgen : IsGen B.emb A γ fun w => L w (Y w) := by
    intro t w
    have e := hY t w
    change (mat (γ (Multiplicative.ofAdd t))).map (piInf (B.emb w)) * A w = _
    rw [e, GlobalTheory.ThKFockDer.exp_mul_frame _ _ (hAA' w) (hA'A w), ← (L w).map_smul]
    rfl
  have hsd := hact γ hγ _ hgen T₀
  have hact := (actsLaws F _ (Φ T₀) _ (Φ T₀)).1 _ (fun t => map_zero _) hsd
  have e : (∑ w, (Φ ∘ₗ LinearMap.applyₗ T₀ ∘ₗ D w).restrictScalars ℝ ∘ₗ L w ∘ₗ LinearMap.proj w) Y =
      Φ (sumPl (fun w => fockAct2 r' s' r s (L w (Y w)) + (c w * (L w (Y w)).trace) • 1) T₀) := by
    simp only [sumPl, LinearMap.sum_apply, map_sum]
    rfl
  rw [e]
  exact hact

private theorem arch_lin (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (h : IsPair B M χX χW om r s r' s') :
    ∃ Δ : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] Module.End ℂ (SInf F (Fin n × Fin d)),
      ∀ γ ∈ Lines σ X, ∀ Y : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ,
        (∀ (t : ℝ) w, (mat (γ (Multiplicative.ofAdd t))).map (piInf (B.emb w)) = NormedSpace.exp (t • Y w)) →
        ∀ f : SInf F (Fin n × Fin d), ∃ c : ℝ → SInf F (Fin n × Fin d), c 0 = f ∧
          Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (Δ Y f)) ∧
          ∀ t, Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(c t) := by
  obtain ⟨Q, hQ⟩ := orbit_lin hP M B.ψ χX χW om h.base.std h.weil
  obtain ⟨N, hN⟩ := amap_lin h.base.cm B.emb M
  obtain ⟨f₀, Δ₀, hf₀, hΔ₀⟩ := vac_lin hP h
  obtain ⟨x₀, hx₀⟩ : ∃ x, f₀ x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf₀ (SchwartzMap.ext hc)
  let ev₀ : SInf F (Fin n × Fin d) →ₗ[ℝ] ℂ :=
    { toFun := fun u => u x₀ / f₀ x₀
      map_add' := fun u u' => by rw [SchwartzMap.add_apply, add_div]
      map_smul' := fun r u => by rw [SchwartzMap.smul_apply, RingHom.id_apply, smul_div_assoc] }
  let aL : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] ℂ :=
    ev₀ ∘ₗ (Δ₀ - (LinearMap.applyₗ (R := ℂ) f₀).restrictScalars ℝ ∘ₗ Q ∘ₗ N)
  refine ⟨aL.smulRight (1 : Module.End ℂ (SInf F (Fin n × Fin d))) + Q ∘ₗ N, fun γ hγ Y hY f => ?_⟩
  obtain ⟨a, ha⟩ := hQ (fun t => (γ (Multiplicative.ofAdd t), 1))
    ((hγ.1.comp continuous_ofAdd).prodMk continuous_const) (by rw [ofAdd_zero, map_one]; rfl)
    (fun s t => by rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]) (fun t => hγ.2 _)
    (fun t u _ => by simp [mat]) (N Y) (hN (fun t => γ (Multiplicative.ofAdd t)) Y (fun t => hγ.2 _) hY)
  have hD : ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f₀ ⇑(a • f₀ + Q (N Y) f₀) := by
    obtain ⟨c, h0, hlim, hacts⟩ := ha f₀
    intro r hr x
    have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
      (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
        (fun j => evI F (x j))).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
    have h2 : HasDerivAt (fun t : ℝ => c t (fun j => evI F (x j)) * r x)
        ((a • f₀ + Q (N Y) f₀) (fun j => evI F (x j)) * r x) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      refine (((ev.tendsto _).comp hlim).mul_const _).congr' (Filter.Eventually.of_forall fun t => ?_)
      rw [slope_def_module, h0]
      simp only [Function.comp_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
      ring
    simp only [fun t => hacts t r hr]
    exact h2
  have e := (GlobalTheory.RealLift.actsLaws F _ f₀ _ _).2.2.1 _ hD (hΔ₀ γ hγ Y hY)
  have ea : (Δ₀ Y x₀ - Q (N Y) f₀ x₀) / f₀ x₀ = a := by
    rw [← e, div_eq_iff hx₀, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, add_sub_cancel_right]
  obtain ⟨c, h0, hlim, hacts⟩ := ha f
  refine ⟨c, h0, ?_, hacts⟩
  change Tendsto _ _ (𝓝 (((Δ₀ Y x₀ - Q (N Y) f₀ x₀) / f₀ x₀) • f + Q (N Y) f))
  rw [ea]
  exact hlim

private theorem lift_lin (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ Λ : Module.End ℂ (SInf F κ) →ₗ[ℝ] Module.End ℂ ((κ → AF F) → ℂ),
      ∀ δ (f : SInf F κ), ∀ φ ∈ SB (κ → Af F), Λ δ (pureA F f φ) = pureA F (δ f) φ := by
  have hex : ∀ (y : κ → Af F), ∀ Φ ∈ schA F κ, ∃ s : SInf F κ,
      ∀ x, s x = Φ fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i) : AF F) := by
    intro y Φ hΦ
    induction hΦ using Submodule.span_induction with
    | zero => exact ⟨0, fun x => rfl⟩
    | add Φ Ψ _ _ h₁ h₂ =>
      obtain ⟨s₁, h₁⟩ := h₁
      obtain ⟨s₂, h₂⟩ := h₂
      exact ⟨s₁ + s₂, fun x => by rw [SchwartzMap.add_apply, h₁, h₂]; rfl⟩
    | smul c Φ _ h₁ =>
      obtain ⟨s₁, h₁⟩ := h₁
      exact ⟨c • s₁, fun x => by rw [SchwartzMap.smul_apply, h₁]; rfl⟩
    | mem Φ hΦ =>
      obtain ⟨f, φ, -, rfl⟩ := hΦ
      refine ⟨φ y • f, fun x => ?_⟩
      change φ y * f x = f (locV (liftV x)) * φ y
      rw [Coord.loc_lift, mul_comm]
  choose sl hsl using hex
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (schA F κ)
  let P := Submodule.linearProjOfIsCompl (schA F κ) q hq
  let S : (κ → Af F) → ((κ → AF F) → ℂ) →ₗ[ℂ] SInf F κ := fun y =>
    { toFun := fun Φ => sl y (P Φ) (P Φ).2
      map_add' := fun Φ Ψ => by ext x; simp only [SchwartzMap.add_apply, hsl, map_add]; rfl
      map_smul' := fun c Φ => by ext x; simp only [SchwartzMap.smul_apply, hsl, map_smul]; rfl }
  refine ⟨{ toFun := fun δ =>
              { toFun := fun Φ x => δ (S (fun i => (x i).2) Φ) (locV x)
                map_add' := fun Φ Ψ => by funext x; simp
                map_smul' := fun c Φ => by funext x; simp }
            map_add' := fun δ δ' => by ext Φ x; simp
            map_smul' := fun r δ => by ext Φ x; simp }, fun δ f φ hφ => ?_⟩
  have hm : pureA F f φ ∈ schA F κ := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hP : P (pureA F f φ) = ⟨_, hm⟩ := Submodule.linearProjOfIsCompl_apply_left hq ⟨_, hm⟩
  have hS : ∀ y, S y (pureA F f φ) = φ y • f := fun y => by
    ext x
    change sl y (P _) (P _).2 x = φ y * f x
    rw [hsl, hP]
    change f (locV (liftV x)) * φ y = _
    rw [Coord.loc_lift, mul_comm]
  funext x
  change δ (S (fun i => (x i).2) _) (locV x) = δ f (locV x) * φ fun i => (x i).2
  rw [hS, map_smul, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]

end UpperTheory.LiftDer

end

open UpperTheory.LiftDer in
theorem UpperTheory.archimedean_diagonal_matrix_exists :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
                 (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
                 ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0) (w : InfinitePlace F) (τ : EmbOver E w),
                   ∃ D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Module.End ℂ ((Fin n × Fin d → AF F) → ℂ),
                     (∀ Z, ∀ Φ ∈ schA F (Fin n × Fin d), D Z Φ ∈ schA F (Fin n × Fin d)) ∧
                     ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ (c • X.J.map σ)),
                       (∀ t, embArch σ (c • X.J.map σ) w (projArch σ (c • X.J.map σ) w (γ t)) = γ t) →
                       (∀ t, GlobalTheory.Orb.archMat σ (c • X.J.map σ) τ (projArch σ (c • X.J.map σ) w (γ t)) = NormedSpace.exp (t • Z)) →
                       ∀ Φ ∈ schA F (Fin n × Fin d), ∀ (g : UA σ X.J) (h : UA σ W.J),
                         HasDerivAt (fun t : ℝ => theta om Φ (g * (toGAd hσ X.J hc).symm (γ t)) h) (theta om (D Z Φ) g h) 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair hσ c hc w τ
  classical
  have hcm := hpair.base.cm
  obtain ⟨Δ, hΔ⟩ := arch_lin hKP.base hpair
  obtain ⟨Λ, hΛ⟩ := lift_lin F (Fin n × Fin d)
  obtain ⟨κ, hκ⟩ := GlobalTheory.ThKFockDer.exists_transfer hcm (c • X.J.map σ) τ (B.emb w)
  have hmem : ∀ (u : SInf F (Fin n × Fin d)), ∀ φ ∈ SB (Fin n × Fin d → Af F), pureA F u φ ∈ schA F (Fin n × Fin d) :=
    fun u φ hφ => Submodule.subset_span ⟨u, φ, hφ, rfl⟩
  have hΛm : ∀ δ, ∀ Φ ∈ schA F (Fin n × Fin d), Λ δ Φ ∈ schA F (Fin n × Fin d) := by
    intro δ Φ hΦ
    induction hΦ using Submodule.span_induction with
    | zero => rw [map_zero]; exact zero_mem _
    | add Φ Ψ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul c Φ _ h₁ => rw [map_smul]; exact Submodule.smul_mem _ _ h₁
    | mem Φ hΦ =>
      obtain ⟨f, φ, hφ, rfl⟩ := hΦ
      rw [hΛ δ f φ hφ]
      exact hmem _ φ hφ
  refine ⟨Λ ∘ₗ Δ ∘ₗ LinearMap.single ℝ (fun _ : InfinitePlace F => Matrix (Fin n) (Fin n) ℂ) w ∘ₗ κ,
    fun Z Φ hΦ => hΛm _ Φ hΦ, fun Z γ h1 h2 Φ hΦ g h => ?_⟩
  have hRL : GlobalTheory.SiegelSet.IsRealLine σ (c • X.J.map σ) γ :=
    ⟨w, τ, Z, GlobalTheory.T.one_parameter_skew_hermitian F E σ hcm _ _ w τ Z (fun t => projArch σ (c • X.J.map σ) w (γ t)) h2,
      fun t => ⟨projArch σ (c • X.J.map σ) w (γ t), (h1 t).symm, h2 t⟩⟩
  obtain ⟨γL, hγL, eγ⟩ := GlobalTheory.T.real_line_corresponds_to_line F E σ hσ hcm X c hc γ hRL
  set Y : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ := Pi.single w (κ Z) with hYdef
  have hY : ∀ (t : ℝ) u, (mat (γL (Multiplicative.ofAdd t))).map (piInf (B.emb u)) = NormedSpace.exp (t • Y u) := by
    intro t u
    have e0 : (mat (γL (Multiplicative.ofAdd t))).map (piInf (B.emb u)) =
        GlobalTheory.Orb.archMat σ (c • X.J.map σ) (B.emb u) (projArch σ (c • X.J.map σ) u (γ t)) := by
      rw [← eγ]; rfl
    rw [e0]
    by_cases hu : u = w
    · subst hu
      rw [hκ _ _ (h2 t), map_smul, hYdef, Pi.single_eq_same]
    · rw [← h1 t, projArch_embArch_ne _ _ hu, map_one]
      simp [hYdef, Pi.single_eq_of_ne hu]
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hpair.weil
  obtain ⟨l, hl, hlt⟩ := GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact F (Fin n × Fin d)
  have key : HasDerivAt (fun t : ℝ => l (om (g, h) (om (γL (Multiplicative.ofAdd t), 1) Φ)))
      (l (om (g, h) (Λ (Δ Y) Φ))) 0 := by
    induction hΦ using Submodule.span_induction with
    | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      simp only [map_add]
      exact h₁.add h₂
    | smul r Φ₁ _ h₁ =>
      simp only [map_smul, smul_eq_mul]
      exact h₁.const_mul r
    | mem Φ hΦ =>
      obtain ⟨f, φ, hφ, rfl⟩ := hΦ
      obtain ⟨cv, h0, hlim, hacts⟩ := hΔ γL hγL Y hY f
      have hR : Rest (evI F) (⇑f) (fun x : Fin n × Fin d → AF F => φ fun i => (x i).2) := by
        refine ⟨fun x z hz => congrArg φ (funext fun i => ?_), hmem f φ hφ⟩
        show (x i).2 + (z i).2 = (x i).2
        rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
      have hcv : ∀ t : ℝ, om (γL (Multiplicative.ofAdd t), 1) (pureA F f φ) = pureA F (cv t) φ :=
        fun t => hacts t _ hR
      obtain ⟨T, hT⟩ := hS.adm (g, h) l hl φ hφ
      have hTθ : ∀ u : SInf F (Fin n × Fin d), l (om (g, h) (pureA F u φ)) = T u := fun u => hT u
      simp only [hcv, hΛ _ f φ hφ, hTθ]
      rw [hasDerivAt_iff_tendsto_slope]
      refine ((T.continuous.tendsto _).comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, slope_def_module, h0, sub_zero, ← Complex.coe_smul, map_smul, map_sub]
  have e2 : (fun t : ℝ => theta om Φ (g * (toGAd hσ X.J hc).symm (γ t)) h) =
      fun t : ℝ => l (om (g, h) (om (γL (Multiplicative.ofAdd t), 1) Φ)) := by
    funext t
    simp only [theta]
    rw [eγ, ← hlt _ (hS.pres _ _ hΦ), ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have e3 : theta om (Λ (Δ Y) Φ) g h = l (om (g, h) (Λ (Δ Y) Φ)) := by
    simp only [theta]
    rw [← hlt _ (hS.pres _ _ (hΛm _ Φ hΦ))]
  rw [e2]
  exact e3 ▸ key
