import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SmallLevel

theorem exists_open_subgroup (F : Type) [Field F] [NumberField F] (V : Set (Af F)) (hV : V ∈ 𝓝 (0 : Af F)) :
    ∃ S : AddSubgroup (Af F), IsOpen (S : Set (Af F)) ∧ (S : Set (Af F)) ⊆ V := by
  obtain ⟨M, hM, hMV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F V hV
  let S : AddSubgroup (Af F) :=
    { carrier := {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a}
      zero_mem' := ⟨0, fun v => zero_mem _, (smul_zero M).symm⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun v => add_mem (ha v) (hb v), (smul_add M a b).symm⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun v => neg_mem (ha v), (smul_neg M a).symm⟩ }
  refine ⟨S, S.isOpen_of_mem_nhds (g := 0) (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F M hM), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hMV a ha

theorem infPart_smul_eq_zero {D : D7} (y : Af D.host.F) (x : AE D) : infPart D (pairA D.host.F 0 y • x) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 y)) = 0 := by
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [this, zero_mul]

theorem exists_closed_level (D : D7) (m n : ℕ) (N : Set (Mx D m n)) (hN : N ∈ 𝓝 (0 : Mx D m n)) :
    ∃ K : AddSubgroup (Mx D m n), IsClosed (K : Set (Mx D m n)) ∧ (K : Set (Mx D m n)) ⊆ N ∧
      (∀ u ∈ K, u.map (infPart D) = 0) ∧
      ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K := by
  classical
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AE D) := IsModuleTopology.topologicalAddGroup (AF D.host.F) _
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : T2Space (InfiniteAdeleRing D.host.F) := inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  let Φ : (Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) → Mx D m n :=
    fun x i j => ∑ k, pairA D.host.F 0 (x (i, j, k)) • B k
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_finset_sum _ fun k _ => ?_
    have h1 : Continuous fun x : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
        pairA D.host.F 0 (x (i, j, k)) := continuous_const.prodMk (continuous_apply _)
    exact h1.smul continuous_const
  have h0 : Φ 0 = 0 := by
    funext i j
    refine Finset.sum_eq_zero fun k _ => ?_
    exact zero_smul (AF D.host.F) (B k)
  have h1 : Φ ⁻¹' N ∈ 𝓝 0 := hΦ.continuousAt.preimage_mem_nhds (h0 ▸ hN)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, -, t, ht, hsub⟩ := h1
  obtain ⟨S, hS, hSt⟩ := exists_open_subgroup D.host.F (⋂ p, t p) (Filter.iInter_mem.mpr ht)
  let c : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Mx D m n →+ AF D.host.F := fun p =>
    { toFun := fun u => B.coord p.2.2 (u p.1 p.2.1)
      map_zero' := map_zero _
      map_add' := fun u u' => map_add _ _ _ }
  have hc : ∀ p, Continuous (c p) := fun p =>
    (IsModuleTopology.continuous_of_linearMap (B.coord p.2.2)).comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1))
  let U : AddSubgroup (Mx D m n) := ⨅ p, S.comap ((sndA D.host.F).toRingHom.toAddMonoidHom.comp (c p))
  let Z : AddSubgroup (Mx D m n) := ⨅ p, ((fstA D.host.F).toRingHom.toAddMonoidHom.comp (c p)).ker
  have hU : ∀ u, u ∈ U ↔ ∀ p, (c p u).2 ∈ S := fun u => AddSubgroup.mem_iInf
  have hZ : ∀ u, u ∈ Z ↔ ∀ p, (c p u).1 = 0 := fun u => AddSubgroup.mem_iInf
  have hUe : (U : Set (Mx D m n)) = ⋂ p, (fun u => (c p u).2) ⁻¹' S := by
    ext u; rw [Set.mem_iInter]; exact hU u
  have hZe : (Z : Set (Mx D m n)) = ⋂ p, {u | (c p u).1 = 0} := by
    ext u; rw [Set.mem_iInter]; exact hZ u
  have hrec : ∀ u ∈ Z, Φ (fun p => (c p u).2) = u := by
    intro u hu
    funext i j
    conv_rhs => rw [← B.sum_repr (u i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact Prod.ext ((hZ u).mp hu (i, j, k)).symm rfl
  refine ⟨U ⊓ Z, ?_, ?_, ?_, U, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf, hUe, hZe]
    exact (isClosed_iInter fun p => (S.isClosed_of_isOpen hS).preimage (continuous_snd.comp (hc p))).inter
      (isClosed_iInter fun p => isClosed_eq (continuous_fst.comp (hc p)) continuous_const)
  · intro u hu
    have h4 : (fun p => (c p u).2) ∈ I.pi t := fun p _ => Set.mem_iInter.mp (hSt ((hU u).mp hu.1 p)) p
    have h5 := hsub h4
    rwa [Set.mem_preimage, hrec u hu.2] at h5
  · intro u hu
    funext i j
    have h4 : ∑ k, pairA D.host.F 0 (c (i, j, k) u).2 • B k = u i j := congrFun (congrFun (hrec u hu.2) i) j
    rw [Matrix.map_apply, ← h4]
    exact (infPart D).toAddMonoidHom.ker.sum_mem fun k _ => infPart_smul_eq_zero _ _
  · rw [hUe]
    exact isOpen_iInter_of_finite fun p => hS.preimage (continuous_snd.comp (hc p))
  · intro u hu hu'
    refine ⟨hu, (hZ u).mpr fun p => ?_⟩
    have h2 := GlobalTheory.FinTranslate.smul_eq_zero_of_inf (congrFun (congrFun hu' p.1) p.2.1)
    have h3 : GlobalTheory.FinTranslate.eInf D * c p u = 0 := by
      have := congrArg (B.coord p.2.2) h2
      rwa [map_smul, map_zero, smul_eq_mul] at this
    exact (one_mul _).symm.trans (congrArg Prod.fst h3)

theorem exists_small_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D), ∀ N ∈ 𝓝 (0 : WO A T), ∃ K : AddSubgroup (WO A T), IsCompact (K : Set (WO A T)) ∧ (K : Set (WO A T)) ⊆ N ∧ (∀ u ∈ K, u.map (infPart D) = 0) ∧ (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K) ∧ ∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1 := by
  intro D ψ hψ A T N hN
  haveI : LocallyCompactSpace (WO A T) := (GlobalTheory.MixModel.lattice_Mx D T.rank A.rank).2.1
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : WO A T)
  have hs : Continuous fun p : WO A T × WO A T => (symplOH A T p.1 p.2).2 :=
    continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd)
  have h2 := hs.continuousAt.preimage_mem_nhds (x := (0, 0)) (t := {a | ψ (pairA D.host.F 0 a) = 1})
    (by
      have h0 : (symplOH A T (0 : WO A T) 0).2 = 0 := congrArg Prod.snd (GlobalTheory.FinTranslate.symplOH_zero_left A T 0)
      have h1 := GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1
      rwa [← h0] at h1)
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_nhds_prod_iff.mp h2
  obtain ⟨K, hK, hKN, hKf, hKU⟩ := exists_closed_level D T.rank A.rank (N ∩ C ∩ (P ∩ Q))
    (Filter.inter_mem (Filter.inter_mem hN hC0) (Filter.inter_mem hP hQ))
  refine ⟨K, hC.of_isClosed_subset hK fun u hu => (hKN hu).1.2, fun u hu => (hKN hu).1.1, hKf, hKU,
    fun u hu u' hu' => ?_⟩
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH A T u u' = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin (hKf u' hu'),
      GlobalTheory.FinTranslate.symplOH_zero_right]
  have h4 : symplOH A T u u' = pairA D.host.F 0 (symplOH A T u u').2 :=
    Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl
  rw [h4]
  have h5 := hPQ (Set.mk_mem_prod (hKN hu).2.1 (hKN hu').2.2)
  rw [Set.mem_preimage, Set.mem_setOf_eq] at h5
  exact h5

end GlobalTheory.SmallLevel

end
