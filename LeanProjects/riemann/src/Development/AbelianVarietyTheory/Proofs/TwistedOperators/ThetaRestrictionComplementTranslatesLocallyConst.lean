import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.BesselDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSupport

variable {D : D7}

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) (Matrix.transpose (y.map (cA D))))
      (T.gram.map (incA D))) x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun d _ => Finset.sum_comm))

theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] {w r n : ℕ} (Gi : Matrix (Fin n) (Fin n) R) (Nt : Matrix (Fin n) (Fin r) R)
    (Tt : Matrix (Fin r) (Fin w) R) (GW : Matrix (Fin w) (Fin w) R) (a : Matrix (Fin w) (Fin r) R)
    (M : Matrix (Fin r) (Fin n) R) (hP : M * Gi * Nt = 1) :
    Matrix.trace (Gi * (Nt * Tt) * GW * (a * M)) = Matrix.trace (Tt * (GW * a)) := by
  rw [show Gi * (Nt * Tt) * GW * (a * M) = (Gi * Nt * Tt * GW * a) * M by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm, show M * (Gi * Nt * Tt * GW * a) = (M * Gi * Nt) * (Tt * (GW * a)) by
      simp only [Matrix.mul_assoc], hP, Matrix.one_mul]

theorem adj_mul_conj {r n : ℕ} (C : Matrix (Fin n) (Fin r) D.host.E) (K : Matrix (Fin r) (Fin n) D.host.E)
    (hKC : K * C = 1) : adj D C * Matrix.transpose (K.map star) = 1 := by
  have e1 : adj D C = Matrix.conjTranspose C := rfl
  have e2 : Matrix.transpose (K.map star) = Matrix.conjTranspose K := rfl
  rw [e1, e2, ← Matrix.conjTranspose_mul, hKC, Matrix.conjTranspose_one]

theorem symplO_isoPart_restEmb (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (hKC : K * C = 1) (a t : Mx D W.rank r) :
    symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C a) (restEmb V W K t) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 *
        ∑ i, ∑ j, cA D (t i j) * (HMul.hMul (W.gram.map (incA D)) a : Mx D W.rank r) i j) := by
  rw [symplO, hO_eq_trace]
  congr 2
  have hN : (restEmb V W K t).map (cA D) =
      HMul.hMul (t.map (cA D)) ((K.map star).map (incA D)) := by
    rw [restEmb, Matrix.map_mul]
    congr 1
  have hP : HMul.hMul (HMul.hMul ((adj D C * V.gram).map (incA D)) ((V.gram⁻¹).map (incA D)))
      (Matrix.transpose ((K.map star).map (incA D))) = (1 : Matrix (Fin r) (Fin r) (AE D)) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc (adj D C),
      Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit V), Matrix.mul_one, adj_mul_conj C K hKC,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart, hN, Matrix.transpose_mul]
  rw [trace_inverseGram_conj_smul_eq _ _ _ _ _ _ hP]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

theorem res_smul (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (c : ℂ) (g : WO V W → ℂ) :
    res V V' W C B μ 𝓨 (c • g) = c • res V V' W C B μ 𝓨 g := by
  funext x
  simp only [res, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem res_eq_zero_of_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V' W : HSp D} {r : ℕ}
    {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : IsIsoSplit V V' C B) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W)
    {y : Mx D W.rank r} (hy : heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f = f)
    (hne : ψ (symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) w) ≠ 1) :
    res V V' W C B μ 𝓨 (heisO ψ V W w f) = 0 := by
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  have h4 := ((GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hμ).1 _ hg).2.2.2 y
  rw [GlobalTheory.SplitScalar.heisO_comm, hy, res_smul] at h4
  have h5 : (ψ (symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) w) - 1) • res V V' W C B μ 𝓨 (heisO ψ V W w f) = 0 := by
    rw [sub_smul, h4, one_smul, sub_self]
  exact (smul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hne)

theorem sum_single {m n : ℕ} (t : Mx D m n) (i : Fin m) (j : Fin n) (s : AE D) :
    ∑ k, ∑ l, cA D (t k l) * (Matrix.single i j s : Mx D m n) k l = cA D (t i j) * s := by
  simp [Matrix.single_apply, mul_ite, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem continuous_isoPart_single (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (G : Matrix (Fin W.rank) (Fin W.rank) (AE D)) (i : Fin W.rank) (j : Fin r) :
    Continuous fun s : AE D =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul G (Matrix.single i j s : Mx D W.rank r) : Mx D W.rank r) := by
  have : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  have h1 : Continuous fun s : AE D => (Matrix.single i j s : Matrix (Fin W.rank) (Fin r) (AE D)) := by
    have e : (fun s : AE D => (Matrix.single i j s : Matrix (Fin W.rank) (Fin r) (AE D))) =
        fun s => s • (Matrix.single i j 1 : Matrix (Fin W.rank) (Fin r) (AE D)) := by
      funext s; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact continuous_id.smul continuous_const
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

set_option maxHeartbeats 800000 in

theorem supp_locConst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ V W f → ∃ (L : AddSubgroup (halfMx (cA D e) W.rank r)) (Kc : Set (halfMx (cA D e) W.rank r)), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ IsCompact Kc ∧ (∀ t, t ∉ Kc → res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f) = 0) ∧ ∀ t, ∀ l ∈ L, heisO ψ V W (restEmb V W K (t + l : halfMx (cA D e) W.rank r)) f = heisO ψ V W (restEmb V W K t) f := by
  intro D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC _ e he f hf
  have : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  obtain ⟨U, hUo, hU⟩ := hf.level
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  let R : halfMx (cA D e) W.rank r →+ WO V W :=
    { toFun := fun t => restEmb V W K t
      map_zero' := Matrix.zero_mul _
      map_add' := fun x y => restEmb_add V W K x y }
  have hRc : Continuous R := continuous_subtype_val.matrix_mul continuous_const

  let Gi : Matrix (Fin W.rank) (Fin W.rank) (AE D) := (W.gram⁻¹).map (incA D)
  have hGG : HMul.hMul (W.gram.map (incA D)) Gi = (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W),
      Matrix.map_one _ (map_zero _) (map_one _)]

  have key : ∀ (i : Fin W.rank) (j : Fin r), ∃ Cij : Set (AE D), IsCompact Cij ∧ ∀ x, e * x = x →
      (∀ s ∈ (fun s : AE D => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
        (HMul.hMul Gi (Matrix.single i j s : Mx D W.rank r) : Mx D W.rank r)) ⁻¹' (U : Set (WO V W)),
        e * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (x * s)) = 1) → x ∈ Cij := fun i j => by
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
        (HMul.hMul Gi (Matrix.single i j (0 : AE D) : Mx D W.rank r) : Mx D W.rank r) = 0 := by
      rw [Matrix.single_zero, Matrix.mul_zero]
      exact Matrix.zero_mul _
    refine GlobalTheory.SplitAnnihilator.annihilator_subset_compact D ψ (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) e he _ ?_
    refine (continuous_isoPart_single V W C Gi i j).continuousAt.preimage_mem_nhds ?_
    rw [h0]
    exact hUo.mem_nhds U.zero_mem
  choose Cij hCc hCm using key
  let Kij : Fin W.rank → Fin r → Set (AE D) := fun i j =>
    (fun x => cA D (incA D D.host.xi0⁻¹ * x)) '' Cij i j
  refine ⟨U.comap R, {t | ∀ i j, (t : Mx D W.rank r) i j ∈ Kij i j}, hUo.preimage hRc, ?_, ?_, ?_⟩
  · have hK : IsCompact (Set.pi Set.univ fun i => Set.pi Set.univ fun j => Kij i j :
        Set (Fin W.rank → Fin r → AE D)) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
        (hCc i j).image (GlobalTheory.FockCompare.ThetaCont.continuous_conj.comp (continuous_const.mul continuous_id))
    have := (isClosed_halfMx (cA D e) W.rank r).isClosedEmbedding_subtypeVal.isCompact_preimage hK
    have e : {t : halfMx (cA D e) W.rank r | ∀ i j, (t : Mx D W.rank r) i j ∈ Kij i j} =
        Subtype.val ⁻¹' (Set.pi Set.univ fun i => Set.pi Set.univ fun j => Kij i j :
          Set (Fin W.rank → Fin r → AE D)) := by
      ext t
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [e]
    exact this
  · intro t ht
    by_contra hne
    apply ht
    intro i j
    have hti : cA D e * (t : Mx D W.rank r) i j = (t : Mx D W.rank r) i j := t.2 i j
    have hti' : e * cA D ((t : Mx D W.rank r) i j) = cA D ((t : Mx D W.rank r) i j) := by
      have := congrArg (cA D) hti
      rwa [map_mul, GlobalTheory.DualPairCheck.cA_cA] at this
    refine ⟨incA D D.host.xi0 * cA D ((t : Mx D W.rank r) i j), hCm i j _ (by rw [mul_left_comm, hti']) ?_, ?_⟩
    · intro s hsU hse
      by_contra hψ1
      have ha : IsHalf e (HMul.hMul Gi (Matrix.single i j s : Mx D W.rank r) : Mx D W.rank r) := by
        refine mul_isHalf (fun k l => ?_) Gi
        simp only [Matrix.single_apply]
        split_ifs
        · exact hse
        · exact mul_zero e
      have hfin := GlobalTheory.SplitScalar.half_fin he (isHalf_mul ha ((adj D C * V.gram).map (incA D)))
      apply hne
      refine res_eq_zero_of_ne hψ hs hμ hf _ (hU _ hsU hfin) ?_
      rw [symplO_isoPart_restEmb V W C K hKC, ← Matrix.mul_assoc, hGG, Matrix.one_mul, sum_single, ← mul_assoc]
      exact hψ1
    · show cA D (incA D D.host.xi0⁻¹ * (incA D D.host.xi0 * cA D ((t : Mx D W.rank r) i j))) = _
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.embedding_xi_zero_ne_zero D), map_one, one_mul,
        GlobalTheory.DualPairCheck.cA_cA]
  · intro t l hl
    have hl' : restEmb V W K l ∈ U := hl
    have hlh : IsHalf (cA D e) (restEmb V W K l) := isHalf_mul l.2 _
    have hth : IsHalf (cA D e) (restEmb V W K t) := isHalf_mul t.2 _
    have hfin := GlobalTheory.SplitScalar.half_fin he' hlh
    rw [AddSubgroup.coe_add, restEmb_add, GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W
      (GlobalTheory.SplitScalar.symplO_eq_zero V W (by rw [GlobalTheory.DualPairCheck.cA_cA, he.2.1]) hth hlh), hU _ hl' hfin]

end GlobalTheory.HalfSupport

end
