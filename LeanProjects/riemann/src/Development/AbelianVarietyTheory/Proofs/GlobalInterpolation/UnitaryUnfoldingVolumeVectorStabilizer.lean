import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralTsumOrbitUnfoldStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsQuotientMeasureOfBruhatFunctionStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnfoldingKernelLevelSubgroupBruhatStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelicUnitaryComplementRangeStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinPartInvSmulMemLatHatIffStabMulLevelStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatHatStabiliserIffComplementFrameRelStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClosedEmbeddingOfIsStabilizerEmbeddingUpqStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsComplementFrameCompatibleStabilizerEmbeddiStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMeasurableRealOrbitMapOfAdelicOrbitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormAndSelfDualLatticeInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MapRestrictLatticeStabiliserMeasureEqCompactDualStatement

noncomputable section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.VolumeUnfolding

theorem exists_perp_matrix {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (W W' : HSpace E) (ι : W'.V →ₗ[E] W.V) (x : W.V)
    (hι : HSpace.IsIsomEmb W' W ι) (hr : LinearMap.range ι = LinearMap.ker (W.hT x))
    (hL : ∀ y, y ∈ W'.L0 ↔ ι y ∈ W.L0) :
    ∃ B : Matrix (Fin W.rank) (Fin W'.rank) E, Formalism.UG.cT (cm.sig : E →+* E) B * W.gram * B = W'.gram ∧
      (∀ j, hE cm.sig W.gram (coordTup W x 0) (fun i => B i j) = 0) ∧
      ∀ y, y ∈ latC W' ↔ B *ᵥ y ∈ latC W := by
  have hd := (GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords F E cm W).1
  refine ⟨Matrix.of fun i j => W.frame.repr (ι (W'.frame j)) i, ?_, fun j => ?_, fun y => ?_⟩
  · ext a b
    have := hd (ι (W'.frame a)) (ι (W'.frame b))
    rw [hι] at this
    refine Eq.trans ?_ this
    simp only [hE, Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm
  · have h : ι (W'.frame j) ∈ LinearMap.ker (W.hT x) := hr ▸ LinearMap.mem_range_self _ _
    exact (hd x (ι (W'.frame j))).trans h
  · refine (hL _).trans (iff_of_eq (congrArg (· ∈ W.L0) ?_))
    simp only [map_sum, map_smul, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← W.frame.sum_repr (ι (W'.frame j)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]

theorem perp_matrix_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M M' : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    {J' : Matrix (Fin M') (Fin M') E} {B : Matrix (Fin M) (Fin M') E} {x : Fin M → E}
    (hB : Formalism.UG.cT (σ : E →+* E) B * J * B = J') (hx : ∀ j, hE σ J x (fun i => B i j) = 0) (τ : E →+* ℂ) :
    (B.map τ)ᴴ * J.map τ * B.map τ = J'.map τ ∧ ((B.map τ)ᴴ * J.map τ) *ᵥ (fun i => τ (x i)) = 0 := by
  have e : (B.map τ)ᴴ = (Formalism.UG.cT (σ : E →+* E) B).map τ := by
    ext i j
    exact (h.2.2.2 τ _).symm
  refine ⟨by rw [e, ← hB, Matrix.map_mul, Matrix.map_mul], funext fun j => ?_⟩
  have h1 := congrArg (fun z => star (τ z)) (hx j)
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, star_sum, star_mul', map_zero, star_zero] at h1
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Finset.sum_mul, Pi.zero_apply]
  rw [← h1]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h2 : τ ((σ : E →+* E) (x a)) = star (τ (x a)) := h.2.2.2 τ _
  rw [h2, star_star, ← h.2.2.2 τ (J a b), hJ.1 b a]
  ring

section Real

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ}

omit [NumberField E] in
theorem proj_incl (hθ : IsInfEmb τ θ) (z : E) :
    (θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom) (inclR (AF F) z) = τ z := by
  rw [← hθ.1 z]
  simp [inclR]

omit [NumberField E] in
theorem infMat_fix (hθ : IsInfEmb τ θ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {x : Fin 1 → Fin M → E}
    {g : HA (AF F) σ J} (hg : g ∈ Hstab (AF F) σ J x) :
    infMat σ J θ g *ᵥ (fun i => τ (x 0 i)) = fun i => τ (x 0 i) := by
  funext i
  let p := θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have h1 := congrArg p (congrFun (congrFun hg 0) i)
  have h2 := RingHom.map_mulVec p (HA.mat _ _ _ g).1 (ratTup (F := F) (AF F) x 0) i
  have h3 : p ∘ ratTup (F := F) (AF F) x 0 = fun i => τ (x 0 i) := funext fun i => proj_incl hθ _
  rw [h3] at h2
  exact h2.symm.trans (h1.trans (proj_incl hθ _))

omit [NumberField E] in
theorem infMat_frame (hθ : IsInfEmb τ θ) {M M' : ℕ} {J : Matrix (Fin M) (Fin M) E} {J' : Matrix (Fin M') (Fin M') E}
    {B : Matrix (Fin M) (Fin M') E} {g : HA (AF F) σ J} {g' : HA (AF F) σ J'} (hg : FrameRel J J' B g g') :
    infMat σ J θ g * B.map τ = B.map τ * infMat σ J' θ g' := by
  let p := θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have h3 : (B.map (inclR (AF F))).map p = B.map τ := Matrix.ext fun _ _ => proj_incl hθ _
  rw [← h3]
  exact (Matrix.map_mul (f := p)).symm.trans ((congrArg (fun m => m.map p) hg).trans (Matrix.map_mul (f := p)))

end Real

theorem rational_orbit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (W : HSpace E) (x : W.V) {β : E} (hx : W.hT x x = β) (hβ : β ≠ 0) :
    Function.Injective (fun x' : {x' : W.V // W.hT x' x' = β} => ratTup (F := F) (AF F) (coordTup W x'.1)) ∧
    ∀ y, y ∈ Set.range (fun x' : {x' : W.V // W.hT x' x' = β} => ratTup (F := F) (AF F) (coordTup W x'.1)) ↔
      ∃ γ ∈ ratPts (AF F) cm.sig W.gram, γ • ratTup (F := F) (AF F) (coordTup W x) = y := by
  have hd := (GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords F E cm W).1
  have hxx : hE cm.sig W.gram (coordTup W x 0) (coordTup W x 0) = β := (hd x x).trans hx
  obtain ⟨hw1, hw2⟩ := GlobalTheory.T.rational_vectors_same_length_one_unitary_orbit F E cm.sig (isCMExt cm) _ W.gram (isHermND cm W) (coordTup W x) (hxx ▸ hβ)
  refine ⟨fun a b hab => ?_, fun y => Iff.trans ⟨?_, ?_⟩ (hw2 y)⟩
  · exact Subtype.ext (W.frame.repr.injective (Finsupp.ext (congrFun (congrFun (hw1 hab) 0))))
  · rintro ⟨x', rfl⟩
    exact ⟨coordTup W x'.1, ((hd x'.1 x'.1).trans x'.2).trans hxx.symm, rfl⟩
  · rintro ⟨x', h1, rfl⟩
    have e : coordTup W (W.frame.equivFun.symm (x' 0)) = x' := by
      funext a i
      rw [Subsingleton.elim a 0]
      exact congrFun (W.frame.equivFun.apply_symm_apply (x' 0)) i
    refine ⟨⟨W.frame.equivFun.symm (x' 0), ?_⟩, congrArg _ e⟩
    rw [← e] at h1
    exact (hd _ _).symm.trans (h1.trans hxx)

theorem unramified_host (D : D7) : UnramifiedAtFinite D.host.F D.host.E := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  intro P hP _
  exact Algebra.unramified_iff_forall.1 hU ⟨P, hP⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unfoldAt (hT : StabTransitive) (D : D7) (W W' : HSpace D.host.E) (P Q P' Q' : ℕ)
    (hc : P' + Q' + 1 = P + Q) (hs : W.SigOK) (hPQ : ∀ τ, W.sig τ = (P, Q)) (hs' : W'.SigOK)
    (hPQ' : ∀ τ, W'.sig τ = (P', Q')) (β : D.host.F) (hβ : β = 1 ∨ β = -1) (x : W.V)
    (hx : W.hT x x = algebraMap _ _ β) (hxL : x ∈ W.L0) (ι : W'.V →ₗ[D.host.E] W.V)
    (hι : HSpace.IsIsomEmb W' W ι) (hr : LinearMap.range ι = LinearMap.ker (W.hT x))
    (hL : ∀ y, y ∈ W'.L0 ↔ ι y ∈ W.L0) : UnfoldAt D W W' P Q P' Q' (algebraMap _ _ β) x := by
  intro μ μ' 𝓕 𝓕' hμ hμ' h𝓕 h𝓕' _ _
  have hcm := isCMExt D.sp.cm
  have hJ := isHermND D.sp.cm W
  have hJ' := isHermND D.sp.cm W'
  have hτ : IsCMFam (embOf D) := GlobalTheory.Mem.Vol.isCMFam_host D.R D.host _ D.eTau
  have hβ0 : algebraMap D.host.F D.host.E β ≠ 0 := by rcases hβ with rfl | rfl <;> simp
  obtain ⟨τ₀⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hM : W.rank = P + Q := by have := sig_sum W hs τ₀; rw [hPQ] at this; exact this.symm
  have hM' : W'.rank = P' + Q' := by have := sig_sum W' hs' τ₀; rw [hPQ'] at this; exact this.symm
  have hMM : W'.rank + 1 = W.rank := by omega
  obtain ⟨hd, L, hLs, hLc⟩ := GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords _ _ D.sp.cm W
  obtain ⟨-, L', hLs', hLc'⟩ := GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords _ _ D.sp.cm W'
  obtain ⟨B, hB, hBx, hBL⟩ := exists_perp_matrix D.sp.cm W W' ι x hι hr hL
  have hxx : hE D.sp.cm.sig W.gram (coordTup W x 0) (coordTup W x 0) = algebraMap _ _ β := (hd x x).trans hx
  have hx0 : hE D.sp.cm.sig W.gram (coordTup W x 0) (coordTup W x 0) ≠ 0 := hxx ▸ hβ0
  have hxL' : coordTup W x 0 ∈ L := by
    rw [← SetLike.mem_coe, hLc]
    change ∑ i, W.frame.repr x i • W.frame i ∈ W.L0
    rwa [W.frame.sum_repr]
  refine ⟨hμ.2.1, fun θ hθ => ⟨(hμ.2.2 θ hθ).1, fun A hA => ?_⟩⟩
  have hAx : ∀ ρ, star (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ
      (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) ≠ 0 := fun ρ h0 => by
    have := (GlobalTheory.UnfoldingCompare.norm_coords W (embOf D ρ) (GlobalTheory.UnfoldingCompare.emb_star D _) (A ρ) (hA ρ) x).symm.trans h0
    rw [hx] at this
    exact hβ0 ((map_eq_zero _).1 this)
  have hBτ := fun ρ => perp_matrix_map hcm hJ hB hBx (embOf D ρ)
  refine ⟨?_, fun j hj => ?_⟩
  · have key : ∀ ρ, ∃ j : UpqT P' Q' →* UpqT P Q,
        IsStabEmb (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) j := fun ρ => by
      have h1 := hs' (embOf D ρ)
      rw [hPQ'] at h1
      obtain ⟨A', N', hA', -, hr'⟩ := GlobalTheory.VolPairExists.exists_frame h1
      have e1 : (A ρ * B.map (embOf D ρ) * N')ᴴ * Formalism.UG.Jpq P Q * A ρ =
          N'ᴴ * ((B.map (embOf D ρ))ᴴ * W.gram.map (embOf D ρ)) := by
        rw [← hA ρ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      have e2 : (A ρ * B.map (embOf D ρ) * N')ᴴ * Formalism.UG.Jpq P Q * (A ρ * B.map (embOf D ρ) * N') =
          Formalism.UG.Jpq P' Q' := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.mul_assoc N'ᴴ, (hBτ ρ).1,
          GlobalTheory.VolPairExists.conj_frame hA' hr']
      have e3 : ((A ρ * B.map (embOf D ρ) * N')ᴴ * Formalism.UG.Jpq P Q) *ᵥ
          (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) = 0 := by
        rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, (hBτ ρ).2, Matrix.mulVec_zero]
      obtain ⟨j, hj⟩ := GlobalTheory.UnfoldingCompare.exists_stab_hom hc (hAx ρ) e2 e3
      exact ⟨j, _, e2, e3, hj⟩
    choose j hj using key
    exact ⟨j, hj⟩
  have : ∀ P Q, IsTopologicalGroup (UpqT P Q) := fun P Q => inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  have : ∀ P Q, T2Space (UpqT P Q) := fun P Q => inferInstanceAs (T2Space (Formalism.UG.Upq P Q))
  have : ∀ P Q, BorelSpace (UpqT P Q) := fun P Q => ⟨rfl⟩
  have : ∀ P Q, LocallyCompactSpace (UpqT P Q) := fun P Q =>
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : ∀ P Q, SecondCountableTopology (UpqT P Q) := fun P Q =>
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  have := D.cd.haar
  have := fun P Q => GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q (D.cd.cd P Q) (D.cd.haar P Q)
  have := fun P Q => GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant (D.cd.cd P Q)
  have hjc : IsClosedEmbedding (piEmb j) :=
    IsClosedEmbedding.piMap fun ρ => GlobalTheory.T.isClosedEmbedding_of_isStabilizerEmbeddingUpq P Q P' Q' hc _ (hAx ρ) (j ρ) (hj ρ)
  have hjm := hjc.continuous.measurable
  obtain ⟨b, hb, hb1⟩ := GlobalTheory.T.exists_bruhatFunction_of_closedEmbedding _ _ (piEmb j) hjc (Measure.pi fun _ => D.cd.cd P' Q')
  refine ⟨GlobalTheory.T.exists_isQuotientMeasure_of_bruhat _ _ (piEmb j) hjm _ _ b hb hb1, fun ν hν => ?_⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary _ _ D.sp.cm.sig W.rank W.gram
  obtain ⟨i1', i2', i3'⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary _ _ D.sp.cm.sig W'.rank W'.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig W.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W'.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig W'.gram
  have := hμ.1
  have := hμ'.1
  have hK := (isOpen_stab (σ := D.sp.cm.sig) W.gram L hLs.1 hLs.2.1).measurableSet
  have hK' := (isOpen_stab (σ := D.sp.cm.sig) W'.gram L' hLs'.1 hLs'.2.1).measurableSet
  have hdet' : ∀ ρ, (W'.gram.map (embOf D ρ)).det ≠ 0 := fun ρ => by
    have : (W'.gram.map (embOf D ρ)).det = embOf D ρ W'.gram.det := ((embOf D ρ).map_det W'.gram).symm
    rw [this]
    exact (map_ne_zero _).2 hJ'.2
  choose A' hA' hAj using fun ρ => GlobalTheory.T.exists_complement_frame_compatible_stabilizerEmbedding P Q P' Q' _ _ hc hM' _ _ _ _ (A ρ) (hA ρ) (hBτ ρ).1 (hdet' ρ)
    (hBτ ρ).2 (hAx ρ) (j ρ) (hj ρ)
  obtain ⟨⟨N, hN, hN'⟩, ψ, hψ, hψA, hψm⟩ := GlobalTheory.T.map_restrict_latticeStabiliser_measure_eq_compactDual _ _ _ hcm _ (embOf D) θ hθ _ P Q hM W.gram hJ.2 A hA L hK D.cd μ
    (by rw [hLc]; exact (hμ.2.2 θ hθ).2 A hA)
  obtain ⟨-, ψ', hψ', hψA', hψm'⟩ := GlobalTheory.T.map_restrict_latticeStabiliser_measure_eq_compactDual _ _ _ hcm _ (embOf D) θ hθ _ P' Q' hM' W'.gram hJ'.2 A' hA' L' hK' D.cd μ'
    (by rw [hLc']; exact (hμ'.2.2 θ hθ).2 A' hA')
  obtain ⟨hpt, hpt'⟩ := GlobalTheory.T.exists_measurable_realOrbitMap_of_adelicOrbit _ _ _ hcm _ (embOf D) hτ θ hθ _ P Q W.gram A N hN hN' (coordTup W x)
  refine ⟨hpt, fun pt hp Φi hΦ => ?_⟩
  obtain ⟨hpm, hpi, hph⟩ := hpt' pt hp
  obtain ⟨φ, hφc, hφi, hφr, hφB, hφΓ⟩ := GlobalTheory.T.exists_adelic_unitary_complement_range_stabiliser _ _ _ hcm _ _ W.gram W'.gram B (coordTup W x) hMM hJ hJ' hB hBx hx0
  have hφx : ∀ g, φ g ∈ Hstab (AF D.host.F) D.sp.cm.sig W.gram (coordTup W x) := fun g => hφr ▸ ⟨g, rfl⟩
  have hφψ : ∀ g, ψ (φ g) = piEmb j (ψ' g) := fun g => funext fun ρ =>
    hAj ρ _ _ _ _ (infMat_fix (hθ ρ) (hφx g)) (infMat_frame (hθ ρ) (hφB g)) (hψA (φ g) ρ) (hψA' g ρ)
  obtain ⟨u, hu, hu1, hu2⟩ := GlobalTheory.T.exists_unfoldingKernel_levelSubgroup_bruhat_alt _ _ _ _ μ μ' _ _ _ _ hK hK' φ ψ ψ' (piEmb j) hψ.measurable hψ'.measurable hjm
    (fun g => GlobalTheory.T.latHat_stabiliser_iff_complement_frameRel hT _ _ _ hcm (unramified_host D) _ _ W.gram W'.gram B (coordTup W x) hMM hJ hJ' hB hBx hx0 L L'
      hLs β hβ hxL' hxx (fun y => by rw [hLc', ← SetLike.mem_coe, hLc]; exact hBL y) _ g (hφx g) (hφB g))
    hφψ hψm hψm' b hb hb1 (fun t => Φi (pt t)) (hΦ.comp hpm)
    (fun s t => congrArg Φi (hpi _ _ fun ρ => (hj ρ).inv_mul_fix (s ρ) (t ρ))) ν hν
  obtain ⟨hw1, hw2⟩ := rational_orbit D.sp.cm W x hx hβ0
  have : Countable (ratPts (AF D.host.F) D.sp.cm.sig W.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have : Countable (ratPts (AF D.host.F) D.sp.cm.sig W'.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  rw [← hu1]
  refine GlobalTheory.T.lintegral_tsum_orbit_unfold_alt _ _ _ {x' : W.V // W.hT x' x' = algebraMap _ _ β} μ μ' (ratPts _ _ _) (ratPts _ _ _) 𝓕 𝓕' h𝓕 h𝓕' φ
    hφc.measurable hφi hφΓ _ hφr
    (fun x' => ratTup (F := D.host.F) (AF D.host.F) (coordTup W x'.1)) hw1 hw2 u hu
    (phiLat (L0c D W) Φi) fun h => ?_
  · rw [hu2, hph h (ψ h) (hψA h)]
    refine congrArg (· * _) ?_
    have h1 := GlobalTheory.T.finPart_inv_smul_mem_latHat_iff_stab_mul_level hT _ _ _ hcm (unramified_host D) _ W.gram hJ L hLs β hβ (coordTup W x) hxL' hxx h
    have h2 : (L : Set _) = L0c D W := hLc
    rw [← h2]
    refine Set.indicator_eq_indicator (h1.trans ⟨?_, ?_⟩) rfl
    · rintro ⟨a, ha, h3⟩
      obtain ⟨g, rfl⟩ : a ∈ φ.range := hφr ▸ ha
      exact ⟨g, h3⟩
    · rintro ⟨g, h3⟩
      exact ⟨_, hφx g, h3⟩

theorem unfolding : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures → GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar →
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.Unfolding D := by
  intro _ _ hT D W P Q hs hPQ _ s hs1 x hx hxL W' ι hι hr hs' hPQ' hL
  cases s
  · have h1 : 1 ≤ Q := by simpa using hs1
    have := unfoldAt hT D W W' P Q P (Q - 1) (by omega) hs hPQ hs' hPQ' (-1) (Or.inr rfl) x
      (by rw [map_neg, map_one]; exact hx) hxL ι hι hr hL
    rwa [map_neg, map_one] at this
  · have h1 : 1 ≤ P := by simpa using hs1
    have := unfoldAt hT D W W' P Q (P - 1) Q (by omega) hs hPQ hs' hPQ' 1 (Or.inl rfl) x
      (by rw [map_one]; exact hx) hxL ι hι hr hL
    rwa [map_one] at this

end GlobalTheory.VolumeUnfolding
