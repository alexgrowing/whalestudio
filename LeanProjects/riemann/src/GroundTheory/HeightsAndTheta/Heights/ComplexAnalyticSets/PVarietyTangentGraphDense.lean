import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyTangentGraphDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroSetOpenMass
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFramePlaneGraph
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFramePlaneGraph
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameGraphGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJacobianRankGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PConormalGenerationGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameImplicitGraph
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology Filter MeasureTheory

noncomputable section

namespace VarietyTangentGraphDense

def frameProjCLM {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) :=
  ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i)

theorem frameProjCLM_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) : frameProjCLM b I z = frameProj b I z := by
  funext i
  simp [frameProjCLM, frameProj]

theorem isClosed_zeroSetEuc {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSetEuc J) := by
  have h : zeroSetEuc J = ⋂ q ∈ J, {z : EuclideanSpace ℂ (Fin n) | eval (fun i => z i) q = 0} := by
    ext z
    simp [zeroSetEuc]
  rw [h]
  refine isClosed_biInter fun q _ => isClosed_eq ?_ continuous_const
  exact (MvPolynomial.continuous_eval q).comp (PiLp.continuous_ofLp 2 _)

theorem exists_near_off {n d : ℕ} {J J' : Ideal (MvPolynomial (Fin n) ℂ)}
    (hO : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hJ' : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') < d) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ zeroSetEuc J) {ε : ℝ} (hε : 0 < ε) :
    ∃ z₁ ∈ zeroSetEuc J \ zeroSetEuc J', dist z₁ z < ε := by
  by_contra hcon
  push Not at hcon
  set O : Set (Fin n → ℂ) := WithLp.toLp 2 ⁻¹' Metric.ball z ε with hOdef
  have hOo : IsOpen O := Metric.isOpen_ball.preimage (PiLp.continuous_toLp 2 _)
  have hxO : WithLp.ofLp z ∈ O := by simp [hOdef, hε]
  have hxZ : WithLp.ofLp z ∈ ComplexSets.zeroSet J := fun q hq => hz q hq
  have hpos := hO n d J hJ hd (WithLp.ofLp z) O hOo hxO hxZ
  have hsub : ComplexSets.zeroSet J ∩ O ⊆ WithLp.ofLp '' zeroSetEuc J' := by
    rintro y ⟨hy, hyO⟩
    refine ⟨WithLp.toLp 2 y, ?_, by simp⟩
    by_contra hnot
    have h1 : WithLp.toLp 2 y ∈ zeroSetEuc J := fun q hq => hy q hq
    have h2 := hcon _ ⟨h1, hnot⟩
    have h3 : dist (WithLp.toLp 2 y) z < ε := hyO
    linarith
  have hnull : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J') = 0 := NullSmaller.proof n d J' hJ'
  have himg : μH[((2 * d : ℕ) : ℝ)] (WithLp.ofLp '' zeroSetEuc J' : Set (Fin n → ℂ)) = 0 := by
    have := ((PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℂ)).lipschitzOnWith
      (s := zeroSetEuc J')).hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity)
    rw [hnull, mul_zero] at this
    exact nonpos_iff_eq_zero.1 this
  have := (MeasureTheory.measure_mono hsub).trans_eq himg
  exact hpos.ne' (nonpos_iff_eq_zero.1 this)

theorem analyticAt_of_differentiableOn {σ : Type} [Fintype σ] {m : ℕ} {U : Set (σ → ℂ)}
    {G : (σ → ℂ) → EuclideanSpace ℂ (Fin m)} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) {w : σ → ℂ}
    (hw : w ∈ U) : AnalyticAt ℂ G w := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let E : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : σ => ℂ) e.symm
  let P : EuclideanSpace ℂ (Fin m) ≃L[ℂ] (Fin m → ℂ) := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => ℂ)
  let H : (Fin (Fintype.card σ) → ℂ) → Fin m → ℂ := fun y => P (G (E y))
  have hV : IsOpen (E ⁻¹' U) := hU.preimage E.continuous
  have hH : DifferentiableOn ℂ H (E ⁻¹' U) :=
    P.differentiable.comp_differentiableOn
      (hG.comp E.differentiable.differentiableOn (Set.mapsTo_preimage _ _))
  have hHa : AnalyticOnNhd ℂ H (E ⁻¹' U) := by
    intro y hy
    refine AnalyticAt.pi fun s => ?_
    have hs : DifferentiableOn ℂ (fun x => H x s) (E ⁻¹' U) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) s).differentiable.comp_differentiableOn hH
    refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hV hs.continuousOn
      (fun x hx i => ?_) y hy
    have h1 : DifferentiableAt ℂ (fun x => H x s) (Function.update x i (x i)) := by
      rw [Function.update_eq_self]
      exact hs.differentiableAt (hV.mem_nhds hx)
    exact h1.comp (x i) (hasFDerivAt_update (𝕜 := ℂ) x (x i)).differentiableAt
  have hGe : G = fun x => P.symm (H (E.symm x)) := by
    funext x
    simp [H]
  have hy : E.symm w ∈ E ⁻¹' U := by simpa using hw
  have hEa : AnalyticAt ℂ (⇑E.symm) w := by
    simpa using (E.symm : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ)).analyticAt w
  have hPa : AnalyticAt ℂ (⇑P.symm) (H (E.symm w)) := by
    simpa using (P.symm : (Fin m → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin m)).analyticAt (H (E.symm w))
  rw [hGe]
  exact (hPa.comp (hHa _ hy)).comp hEa

theorem exists_tangent_frame {n : ℕ} (I₀ : Finset (Fin n))
    (L : (I₀ → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : Function.Injective L) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      (∀ j ∉ I₀, ∀ v, inner ℂ (b j) (L v) = 0) ∧
      Function.Injective fun v => frameProjCLM b I₀ (L v) := by
  classical
  set T : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := LinearMap.range (L : (I₀ → ℂ) →ₗ[ℂ] _) with hT
  have hfin : Module.finrank ℂ T = Fintype.card I₀ := by
    rw [hT]
    exact (LinearMap.finrank_range_of_inj (f := L.toLinearMap) (by exact hL)).trans
      (Module.finrank_fintype_fun_eq_card ℂ)
  let u : OrthonormalBasis I₀ ℂ T :=
    (stdOrthonormalBasis ℂ T).reindex (Fintype.equivFinOfCardEq hfin.symm).symm
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i =>
    if h : i ∈ I₀ then (u ⟨i, h⟩ : EuclideanSpace ℂ (Fin n)) else 0
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (Fin n)) (ι := Fin n) (by rw [finrank_euclideanSpace]) (v := v)
    (s := (I₀ : Set (Fin n))) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hi' : i ∈ I₀ := hi
      have hj' : j ∈ I₀ := hj
      have h := orthonormal_iff_ite.1 u.orthonormal ⟨i, hi'⟩ ⟨j, hj'⟩
      simpa [v, hi', hj', Subtype.ext_iff] using h)
  have hbu : ∀ i : I₀, b i = (u i : EuclideanSpace ℂ (Fin n)) := fun i => by
    rw [hb i i.2]
    simp [v, i.2]
  have hTsum : ∀ x : T, (x : EuclideanSpace ℂ (Fin n)) =
      ∑ k : I₀, inner ℂ (b k) (x : EuclideanSpace ℂ (Fin n)) • b k := by
    intro x
    conv_lhs => rw [← u.sum_repr' x]
    simp [hbu, Submodule.coe_inner]
  refine ⟨b, fun j hj w => ?_, fun w w' hww => ?_⟩
  · have hx := hTsum ⟨L w, LinearMap.mem_range_self _ w⟩
    simp only at hx
    rw [hx, inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hjk : j ≠ (k : Fin n) := by
      rintro rfl
      exact hj k.2
    rw [inner_smul_right, b.orthonormal.2 hjk, mul_zero]
  · have h0 : ∀ k : I₀, inner ℂ (b k) (L (w - w')) = 0 := by
      intro k
      have h := congrFun hww k
      simp only [frameProjCLM_apply, frameProj] at h
      rw [map_sub, inner_sub_right, h, sub_self]
    have hx := hTsum ⟨L (w - w'), LinearMap.mem_range_self _ _⟩
    simp only [h0, zero_smul, Finset.sum_const_zero] at hx
    have h1 : w - w' = 0 := hL (by rw [hx, map_zero])
    exact sub_eq_zero.1 h1

end VarietyTangentGraphDense

theorem VarietyTangentGraphDense.proof_of_framePlaneGraph (hP : FramePlaneGraph.Statement)
    (hO : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) : VarietyTangentGraphDense.Statement := by
  classical
  open VarietyTangentGraphDense in
  intro n d J hJ hd z hz ε hε
  obtain ⟨I₀, J', hcard, hJ'd, hloc⟩ := hP n d J hJ hd (EuclideanSpace.basisFun (Fin n) ℂ)
  set b₀ := EuclideanSpace.basisFun (Fin n) ℂ with hb₀
  obtain ⟨z₁, hz₁, hz₁z⟩ := exists_near_off hO hJ hd hJ'd hz hε
  obtain ⟨Ω, V, g, hΩ, hV, hz₁V, hg, hpg, hgraph⟩ := hloc z₁ hz₁
  obtain ⟨w₁, hw₁, rfl⟩ : z₁ ∈ g '' Ω := by
    rw [← hgraph]
    exact ⟨hz₁, hz₁V⟩
  have hgd : ∀ w ∈ Ω, HasFDerivAt g (fderiv ℂ g w) w := fun w hw =>
    (hg.differentiableAt (hΩ.mem_nhds hw)).hasFDerivAt
  set L := fderiv ℂ g w₁ with hLdef
  set P₀ := frameProjCLM b₀ I₀ with hP₀
  have hPL : P₀.comp L = ContinuousLinearMap.id ℂ (I₀ → ℂ) := by
    have h1 : HasFDerivAt (fun w => P₀ (g w)) (P₀.comp L) w₁ := P₀.hasFDerivAt.comp w₁ (hgd w₁ hw₁)
    have h2 : HasFDerivAt (fun w => P₀ (g w)) (ContinuousLinearMap.id ℂ (I₀ → ℂ)) w₁ := by
      refine (hasFDerivAt_id w₁).congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hw₁] with w hw
      rw [hP₀, frameProjCLM_apply, hpg w hw]
      rfl
    exact h1.unique h2
  have hLinj : Function.Injective L := fun u v huv => by
    have h := congrArg P₀ huv
    rwa [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, hPL] at h
  obtain ⟨b, hbT, hbinj⟩ := exists_tangent_frame I₀ L hLinj
  set P := frameProjCLM b I₀ with hPdef
  set φ : (I₀ → ℂ) → (I₀ → ℂ) := fun w => P (g w) with hφdef
  let M₀ : (I₀ → ℂ) ≃ₗ[ℂ] (I₀ → ℂ) :=
    LinearEquiv.ofInjectiveEndo ((P.comp L : (I₀ → ℂ) →L[ℂ] (I₀ → ℂ)) : (I₀ → ℂ) →ₗ[ℂ] (I₀ → ℂ)) hbinj
  let M : (I₀ → ℂ) ≃L[ℂ] (I₀ → ℂ) := M₀.toContinuousLinearEquiv
  have hMc : (M : (I₀ → ℂ) →L[ℂ] (I₀ → ℂ)) = P.comp L := ContinuousLinearMap.ext fun v => rfl
  have hφd : HasFDerivAt φ (M : (I₀ → ℂ) →L[ℂ] (I₀ → ℂ)) w₁ := by
    rw [hMc]
    exact P.hasFDerivAt.comp w₁ (hgd w₁ hw₁)
  have hgan := analyticAt_of_differentiableOn hΩ hg hw₁
  have hφc : ContDiffAt ℂ 1 φ w₁ := ((P.analyticAt (g w₁)).comp hgan).contDiffAt
  set e := hφc.toOpenPartialHomeomorph φ hφd one_ne_zero with he
  set ψ := hφc.localInverse hφd one_ne_zero with hψ
  have hψe : ψ = e.symm := rfl
  have hw₁s : w₁ ∈ e.source := hφc.mem_toOpenPartialHomeomorph_source hφd one_ne_zero
  have hy₁t : φ w₁ ∈ e.target := hφc.image_mem_toOpenPartialHomeomorph_target hφd one_ne_zero
  have hψy₁ : ψ (φ w₁) = w₁ := hφc.localInverse_apply_image hφd one_ne_zero
  have hψc : ContDiffAt ℂ 1 ψ (φ w₁) := hφc.to_localInverse hφd one_ne_zero
  have hD : ∀ᶠ y in 𝓝 (φ w₁), DifferentiableAt ℂ ψ y :=
    (hψc.eventually (by simp)).mono fun y hy => hy.differentiableAt one_ne_zero
  set S₀ := e.target ∩ e.symm ⁻¹' Ω with hS₀def
  have hS₀ : IsOpen S₀ := e.isOpen_inter_preimage_symm hΩ
  have hy₁S₀ : φ w₁ ∈ S₀ := by
    refine ⟨hy₁t, ?_⟩
    show e.symm (φ w₁) ∈ Ω
    rw [← hψe, hψy₁]
    exact hw₁
  set Ω' := interior (S₀ ∩ {y | DifferentiableAt ℂ ψ y}) with hΩ'def
  have hΩ' : IsOpen Ω' := isOpen_interior
  have hy₁Ω' : φ w₁ ∈ Ω' := mem_interior_iff_mem_nhds.2 (Filter.inter_mem (hS₀.mem_nhds hy₁S₀) hD)
  have hΩ'sub : ∀ y ∈ Ω', y ∈ e.target ∧ ψ y ∈ Ω ∧ DifferentiableAt ℂ ψ y := fun y hy => by
    have h := interior_subset hy
    exact ⟨h.1.1, h.1.2, h.2⟩
  set Ω₁ := e.source ∩ e ⁻¹' Ω' with hΩ₁def
  have hΩ₁ : IsOpen Ω₁ := e.isOpen_inter_preimage hΩ'
  set V' := V ∩ (zeroSetEuc J')ᶜ ∩ P₀ ⁻¹' Ω₁ with hV'def
  have hV' : IsOpen V' :=
    (hV.inter (isClosed_zeroSetEuc J').isOpen_compl).inter (hΩ₁.preimage P₀.continuous)
  refine ⟨b, I₀, Ω', V', fun y => g (ψ y), φ w₁, hcard, hΩ', hV', hy₁Ω', ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨-, hψΩ, hψd⟩ := hΩ'sub y hy
    exact ((hg.differentiableAt (hΩ.mem_nhds hψΩ)).comp y hψd).differentiableWithinAt
  · intro y hy
    rw [← frameProjCLM_apply]
    exact e.right_inv (hΩ'sub y hy).1
  · ext x
    constructor
    · rintro ⟨hxZ, ⟨⟨hxV, hxZ'⟩, hxΩ₁⟩⟩
      obtain ⟨w, hw, rfl⟩ : x ∈ g '' Ω := by
        rw [← hgraph]
        exact ⟨⟨hxZ, hxZ'⟩, hxV⟩
      have hPw : P₀ (g w) = w := by
        rw [hP₀, frameProjCLM_apply]
        exact hpg w hw
      have hwΩ₁ : w ∈ Ω₁ := by
        have h : P₀ (g w) ∈ Ω₁ := hxΩ₁
        rwa [hPw] at h
      refine ⟨e w, hwΩ₁.2, ?_⟩
      show g (ψ (e w)) = g w
      rw [hψe, e.left_inv hwΩ₁.1]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyt, hψΩ, -⟩ := hΩ'sub y hy
      have hmem : g (ψ y) ∈ (zeroSetEuc J \ zeroSetEuc J') ∩ V := by
        rw [hgraph]
        exact ⟨ψ y, hψΩ, rfl⟩
      refine ⟨hmem.1.1, ⟨hmem.2, hmem.1.2⟩, ?_⟩
      show P₀ (g (ψ y)) ∈ Ω₁
      rw [hP₀, frameProjCLM_apply, hpg _ hψΩ]
      refine ⟨e.map_target hyt, ?_⟩
      show e (e.symm y) ∈ Ω'
      rw [e.right_inv hyt]
      exact hy
  · intro j hj
    have hψd : HasFDerivAt ψ (fderiv ℂ ψ (φ w₁)) (φ w₁) := (hψc.differentiableAt one_ne_zero).hasFDerivAt
    have hgd' : HasFDerivAt g L (ψ (φ w₁)) := by
      rw [hψy₁]
      exact hgd w₁ hw₁
    have hcomp := (innerSL ℂ (b j)).hasFDerivAt.comp (φ w₁) (hgd'.comp (φ w₁) hψd)
    have hzero : (innerSL ℂ (b j)).comp (L.comp (fderiv ℂ ψ (φ w₁))) = 0 :=
      ContinuousLinearMap.ext fun v => by simp [hbT j hj]
    rw [hzero] at hcomp
    have hfun : (fun y => inner ℂ (b j) (g (ψ y))) = ⇑(innerSL ℂ (b j)) ∘ g ∘ ψ := by
      funext y
      simp
    rw [hfun]
    exact hcomp.fderiv
  · show dist (g (ψ (φ w₁))) z < ε
    rw [hψy₁]
    exact hz₁z

theorem VarietyTangentGraphDense.proof (hO : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) :
    VarietyTangentGraphDense.Statement :=
  VarietyTangentGraphDense.proof_of_framePlaneGraph
    (FramePlaneGraph.proof (FrameGraphGeneric.proof
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)
      FrameImplicitGraph.proof)) hO

end

end GroundTheory.Heights₂.Heights
