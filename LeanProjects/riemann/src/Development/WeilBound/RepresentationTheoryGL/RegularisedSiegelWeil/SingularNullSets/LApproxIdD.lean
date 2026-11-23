import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MemOfCoord

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem small_eventually {ι A M : Type} [Finite ι] [TopologicalSpace A] [Zero A] [TopologicalSpace M]
    (R : (ι → A) → M) (hR : Continuous R) (U : Set M) (hU : IsOpen U) (h0 : R 0 ∈ U) (Sp : ℕ → Set A)
    (hSp : Tendsto Sp atTop (𝓝 0).smallSets) : ∀ᶠ k in atTop, ∀ w : ι → A, (∀ i, w i ∈ Sp k) → R w ∈ U := by
  have hW : R ⁻¹' U ∈ 𝓝 (0 : ι → A) := hR.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, tt, htt, hsub⟩ := hW
  have hN : (⋂ i, tt i) ∈ 𝓝 (0 : A) := Filter.iInter_mem.mpr htt
  filter_upwards [tendsto_smallSets_iff.mp hSp _ hN] with k hk w hw
  exact hsub (fun i _ => Set.mem_iInter.mp (hk (hw i)) i)

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem approxId_of (h1 : OneD) : ApproxId := by
  classical
  intro D t ψ hψ S e he lam hlam
  have hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_eq_succ (n := 1) hCM.2.2.1
  have : BorelSpace (AF D.host.F) := ⟨rfl⟩
  have : BorelSpace (Mx D t t) := ⟨rfl⟩
  obtain ⟨eA, heA⟩ := GlobalTheory.T.exists_homeomorph_hermR_coordinates D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  obtain ⟨-, hBd⟩ := GlobalTheory.T.coordinate_form_symmetric_nondegenerate D.host.F D.host.E D.sp.cm.sig hCM _ (Module.finBasis D.host.F D.host.E) t
  have hpair := GlobalTheory.T.hermitian_pairing_in_coordinates D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  generalize Module.finBasis D.host.F D.host.E = b at heA hBd hpair
  have hε0 : IsIdF S ((1, LIdemEx.indS S) : AF D.host.F) := ⟨rfl, fun v => rfl⟩
  obtain ⟨ε, hε, heS⟩ : ∃ ε : AF D.host.F, IsIdF S ε ∧ e = algebraMap (AF D.host.F) (AE D) ε :=
    ⟨_, hε0, e_eq D S e he⟩
  have hcA : cA D e = e := (LIdemEx.idem_props S e he).2
  obtain ⟨Θ, hΘ⟩ := exTheta' D t e ε heS hcA b eA heA
  have hcl : IsClosed ((fixE ε : AddSubgroup (AF D.host.F)) : Set (AF D.host.F)) :=
    isClosed_eq (continuous_const.mul continuous_id) continuous_id
  have : LocallyCompactSpace (fixE ε) := hcl.locallyCompactSpace
  have : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨g1, G1, Sp, hg, hlim, hsupp, hSp⟩ := h1 D.host.F hCM.1 ψ hψ S ε hε (Measure.addHaar) inferInstance
  obtain ⟨c, -, hTr⟩ := transfer Θ lam (Measure.addHaar : Measure (fixE ε))
  set Bm := (coordForm D.sp.cm.sig b t).map (algebraMap D.host.F (AF D.host.F)) with hBm
  let sT : Mx D t t → _ := fun T => if hT : T ∈ hermA D t then
    Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hT⟩ else 0
  refine ⟨fun k x => ∏ i, g1 k (Θ x i), fun k T => if T ∈ hermA D t then (c : ℝ) * ∏ i, G1 k (sT T i) else 0,
    fun k => ⟨?_, ?_, fun T hT => ⟨?_, ?_⟩⟩, fun x => ?_, ?_⟩
  · exact (hTr (fun _ => g1 k)).2 (fun _ => (hg k).1)
  · intro x
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => (hg k).2.1 _)
  · beta_reduce
    rw [if_pos hT]
    exact mul_nonneg c.2 (Finset.prod_nonneg fun i _ => ((hg k).2.2 _).1)
  · beta_reduce
    have hpt : ∀ x : hermS D t e, pch ψ x.1.1 T = ∏ i, ψ ((Θ x i).1 * sT T i) := by
      intro x
      rw [pch_eq D t ψ x.1.1 T x.1.2 hT, hpair, dotProduct, char_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [sT, dif_pos hT, hΘ, heA]
    calc ∫ x, (∏ i, g1 k (Θ x i)) * pch ψ x.1.1 T ∂lam
        = ∫ x, ∏ i, (fun i h => g1 k h * ψ (h.1 * sT T i)) i (Θ x i) ∂lam := by
          congr 1; funext x; rw [hpt, ← Finset.prod_mul_distrib]
      _ = (c : ℂ) * ∏ i, ∫ h, g1 k h * ψ (h.1 * sT T i) ∂(Measure.addHaar : Measure (fixE ε)) :=
          (hTr (fun i h => g1 k h * ψ (h.1 * sT T i))).1
      _ = _ := by
          rw [if_pos hT]
          push_cast
          congr 1
          exact Finset.prod_congr rfl fun i _ => ((hg k).2.2 _).2
  · have := tendsto_finsetProd Finset.univ (fun i _ => hlim (Θ x i))
    simpa using this
  · intro C hC hCT ε' hε'
    have hunit : IsUnit Bm.det := by
      have h := (RingHom.map_det (algebraMap D.host.F (AF D.host.F)) (coordForm D.sp.cm.sig b t)).symm
      rw [hBm]
      exact h ▸ (isUnit_iff_ne_zero.mpr hBd).map _
    let R : (Idx t (Module.finrank D.host.F D.host.E) → AF D.host.F) → Mx D t t := fun w => (eA.symm (Bm⁻¹ *ᵥ w)).1
    have hRc : Continuous R :=
      continuous_subtype_val.comp (eA.symm.continuous.comp (continuous_const.matrix_mulVec continuous_id))
    have hU : IsOpen {M : Mx D t t | -M ∉ C} := hC.isOpen_compl.preimage continuous_neg
    have h0 : R 0 ∈ {M : Mx D t t | -M ∉ C} := by
      have : R 0 = 0 := by simp [R, Matrix.mulVec_zero]
      simp only [Set.mem_ofPred_eq, this, neg_zero]
      exact fun h => (hCT 0 h).2.2 rfl
    filter_upwards [small_eventually R hRc _ hU h0 Sp hSp] with k hk T hTC
    obtain ⟨hTA, heT, -⟩ := hCT T hTC
    by_contra hlt
    have hpos := lt_trans hε' (not_le.mp hlt)
    beta_reduce at hpos
    rw [if_pos hTA] at hpos
    have hprod : ∀ i, G1 k (sT T i) ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hpos.ne') i (Finset.mem_univ i)
    have hfixT : ∀ i, ε * sT T i = sT T i := by
      intro i
      simp only [sT, dif_pos hTA, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, coord_fix D t e ε heS b _ heT j]
    have hw : ∀ i, -(sT T i) ∈ Sp k := fun i => by
      have := hsupp k (sT T i) (hprod i)
      rwa [hfixT] at this
    have hmem := hk (fun i => -(sT T i)) hw
    have hR : R (fun i => -(sT T i)) = -T := by
      have h2 : (fun i => -(sT T i)) = -(Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hTA⟩) := by
        funext i; simp only [sT, dif_pos hTA, Pi.neg_apply]
      simp only [R, h2, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
        map_neg, ← heA, eA.symm_apply_apply]
      rfl
    simp only [hR, neg_neg] at hmem
    exact hmem hTC

end PositivityTheory.Rg.Rsw.L.LApproxId

end
