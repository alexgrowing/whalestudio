import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterAdelicGLEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantOfModular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def levPair : GA D W × GL (Fin t) (AE D) →* levM d where
  toFun p := ⟨⟨d.emb0 p.1 * d.levi p.2, mul_mem (GlobalTheory.GodementSectionReduction.wittCoreEmbedding_mem_isotropicStabilizer d _) (GlobalTheory.RegSW.levi_mem d _)⟩, p.1, p.2, rfl⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' p q := Subtype.ext (Subtype.ext (by
    show d.emb0 (p.1 * q.1) * d.levi (p.2 * q.2) = d.emb0 p.1 * d.levi p.2 * (d.emb0 q.1 * d.levi q.2)
    rw [map_mul, map_mul]
    calc d.emb0 p.1 * d.emb0 q.1 * (d.levi p.2 * d.levi q.2)
        = d.emb0 p.1 * (d.emb0 q.1 * d.levi p.2) * d.levi q.2 := by group
      _ = d.emb0 p.1 * (d.levi p.2 * d.emb0 q.1) * d.levi q.2 := by rw [d.wittHyperbolic_anisotropic_commute_levi]
      _ = _ := by group))

theorem coe_levPair (p : GA D W × GL (Fin t) (AE D)) :
    (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) = d.emb0 p.1 * d.levi p.2 := rfl

theorem mt_eq_of_levPair (p : GA D W × GL (Fin t) (AE D)) :
    d.p0 ⬝ (mt B (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.j0) = mt W p.1 := by
  rw [coe_levPair, mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul]

theorem onX_levPair (p : GA D W × GL (Fin t) (AE D)) :
    GlobalTheory.RegSW.onX d ((levPair d p : levM d) : GlobalTheory.RegSW.stab d) = p.2 := by
  have h : mt B (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.jX = d.jX ⬝ p.2.1 := by
    rw [coe_levPair, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  exact Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d _)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)

theorem levPair_bijective : Function.Bijective (levPair d) := by
  constructor
  · intro p q h
    refine Prod.ext (mt_injective W ?_) ?_
    · rw [← mt_eq_of_levPair d p, ← mt_eq_of_levPair d q, h]
    · rw [← onX_levPair d p, ← onX_levPair d q, h]
  · rintro ⟨⟨q, hq⟩, g, a, e⟩
    exact ⟨(g, a), Subtype.ext (Subtype.ext e.symm)⟩

def levEquiv : (GA D W × GL (Fin t) (AE D)) ≃* levM d := MulEquiv.ofBijective (levPair d) (levPair_bijective d)

theorem continuous_levEquiv : Continuous (levEquiv d) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have h : Continuous fun p : GA D W × GL (Fin t) (AE D) => d.emb0 p.1 * d.levi p.2 :=
    (d.continuous_embed.comp continuous_fst).mul (d.continuous_levi.comp continuous_snd)
  exact (h.subtype_mk _).subtype_mk _

theorem continuous_levEquiv_symm : Continuous (levEquiv d).symm := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hv : Continuous fun m : levM d => ((m : GlobalTheory.RegSW.stab d) : GA D B) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine Continuous.prodMk (continuous_of_mt W ?_) ?_
  · have hc : Continuous fun m : levM d => d.p0 ⬝ (mt B ((m : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.j0) :=
      continuous_const.matrix_mul (((continuous_mt B).comp hv).matrix_mul continuous_const)
    refine hc.congr fun m => ?_
    have := mt_eq_of_levPair d ((levEquiv d).symm m)
    rwa [show levPair d ((levEquiv d).symm m) = m from (levEquiv d).apply_symm_apply m] at this
  · refine ((GlobalTheory.RegSW.continuous_onX d).comp continuous_subtype_val).congr fun m => ?_
    have := onX_levPair d ((levEquiv d).symm m)
    rwa [show levPair d ((levEquiv d).symm m) = m from (levEquiv d).apply_symm_apply m] at this

end GlobalTheory.CompanionTheory.QKAvg

theorem GlobalTheory.CompanionTheory.QKAvg.exists_haar_of_prod {G₁ G₂ M : Type} [Group G₁] [Group G₂] [Group M] [TopologicalSpace G₁]
    [TopologicalSpace G₂] [TopologicalSpace M] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [IsTopologicalGroup M]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂] [SecondCountableTopology G₁] [SecondCountableTopology G₂]
    [T2Space G₂] [MeasurableSpace G₁] [BorelSpace G₁] [MeasurableSpace M] [BorelSpace M]
    (e : (G₁ × G₂) ≃* M) (he : Continuous e) (he' : Continuous e.symm)
    (h₁ : ∀ μ : Measure G₁, μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (h₂ : ∀ a : G₂, Measure.modularCharacterFun a = 1) :
    ∃ νM : Measure M, νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  borelize G₂
  haveI hr1 : (Measure.haar : Measure G₁).IsMulRightInvariant := h₁ _ inferInstance
  haveI hr2 : (Measure.haar : Measure G₂).IsMulRightInvariant := GlobalTheory.ParAvg.isMulRightInvariant_of_modular _ h₂
  obtain ⟨ν, hνH, hνR⟩ : ∃ ν : Measure (G₁ × G₂), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant :=
    ⟨(Measure.haar : Measure G₁).prod Measure.haar, inferInstance, inferInstance⟩
  refine ⟨Measure.map e ν, MulEquiv.isHaarMeasure_map ν e he he', ⟨fun m => ?_⟩⟩
  obtain ⟨p, rfl⟩ := e.surjective m
  rw [Measure.map_map (measurable_mul_const _) he.measurable]
  have h : (fun x => x * e p) ∘ e = e ∘ fun x => x * p := by
    funext x; simp [map_mul]
  rw [h, ← Measure.map_map he.measurable (measurable_mul_const _), map_mul_right_eq_self]

set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.CompanionTheory.QKAvg.top_GL (D : D7) (t : ℕ) : LocallyCompactSpace (GL (Fin t) (AE D)) ∧
    SecondCountableTopology (GL (Fin t) (AE D)) ∧ T2Space (GL (Fin t) (AE D)) := by
  obtain ⟨-, m2, m3, m4, -⟩ := lattice_Mx D t t
  haveI : LocallyCompactSpace (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : T2Space (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  haveI : T1Space (Mx D t t) := @T2Space.t1Space _ _ m4
  exact ⟨(Units.isClosedEmbedding_embedProduct (α := Mx D t t)).locallyCompactSpace,
    (Units.isEmbedding_embedProduct (M := Mx D t t)).secondCountableTopology,
    (Units.isEmbedding_embedProduct (M := Mx D t t)).t2Space⟩

theorem GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (levM d)],
    ∃ νM : Measure (levM d), νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  intro D B W t d _
  obtain ⟨g1, g2, g3, g4, g5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨l1, l2, l3⟩ := GlobalTheory.CompanionTheory.QKAvg.top_GL D t
  exact GlobalTheory.CompanionTheory.QKAvg.exists_haar_of_prod (levEquiv d) (continuous_levEquiv d) (continuous_levEquiv_symm d)
    (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W) (GlobalTheory.T.modularCharacter_adelic_GL_eq_one D t)
