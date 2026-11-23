import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNeLam
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.OrbTupFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Unimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensPos

noncomputable section

namespace PI.VolStabS.OrbProperW

open PI.VolStabS Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  PI.VolFromSW Set Topology
open scoped TensorProduct Pointwise

section Abstract

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
  [MulAction G X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [ContinuousSMul G X]

theorem orbMk (x0 : X) (k : G) :
    ((k : G ⧸ MulAction.stabilizer G x0)).out • x0 = k • x0 := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer G x0) k
  rw [hh, mul_smul, (MulAction.mem_stabilizer_iff.1 h.2)]

theorem orbInj (x0 : X) :
    Function.Injective (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by
  intro q q' h
  simp only at h
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
    MulAction.mem_stabilizer_iff, mul_smul, ← h, inv_smul_smul]

theorem orbit_proper (x0 : X) (hcl : IsClosed (MulAction.orbit G x0)) (K : Set X)
    (hK : IsCompact K) :
    IsCompact ((fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) ⁻¹' K) := by
  let O := MulAction.orbit G x0
  have : LocallyCompactSpace O := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul G O := ⟨continuous_induced_rng.2
    (continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  let o0 : O := ⟨x0, MulAction.mem_orbit_self x0⟩
  have hopen : IsOpenMap (fun g : G => g • o0) := isOpenMap_smul_of_sigmaCompact o0
  let φ : G ⧸ MulAction.stabilizer G x0 → O := fun q => ⟨q.out • x0, MulAction.mem_orbit x0 q.out⟩
  have hφmk : ∀ g : G, φ (g : G ⧸ MulAction.stabilizer G x0) = g • o0 := fun g =>
    Subtype.ext (orbMk x0 g)
  have hφc : Continuous φ := by
    rw [(QuotientGroup.isQuotientMap_mk (MulAction.stabilizer G x0)).continuous_iff]
    have : φ ∘ QuotientGroup.mk = fun g : G => g • o0 := funext hφmk
    rw [this]
    exact continuous_id.smul continuous_const
  have hφo : IsOpenMap φ := by
    intro U hU
    have : φ '' U = (fun g : G => g • o0) '' (QuotientGroup.mk ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        refine ⟨q.out, ?_, ?_⟩
        · simp only [mem_preimage, QuotientGroup.out_eq']
          exact hq
        · show q.out • o0 = φ q
          rw [← hφmk q.out, QuotientGroup.out_eq']
      · rintro ⟨g, hg, rfl⟩
        exact ⟨_, hg, hφmk g⟩
    rw [this]
    exact hopen _ (hU.preimage QuotientGroup.continuous_mk)
  have hφi : Function.Injective φ := fun q q' h => orbInj (G := G) x0 (congrArg Subtype.val h)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, g, rfl⟩
    exact ⟨(g : G ⧸ MulAction.stabilizer G x0), hφmk g⟩
  let e : (G ⧸ MulAction.stabilizer G x0) ≃ₜ O :=
    (Equiv.ofBijective φ ⟨hφi, hφs⟩).toHomeomorphOfContinuousOpen hφc hφo
  have hpre : (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) ⁻¹' K =
      e ⁻¹' (Subtype.val ⁻¹' K) := Set.ext fun q => Iff.rfl
  rw [hpre, e.isCompact_preimage]
  exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK

end Abstract

theorem orbProper_holds : OrbProper := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet K hK
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J ha
  have : ContinuousSMul (HA (AF F) σ J) (Fin a → Fin M → AF F ⊗[F] E) := by
    refine ⟨?_⟩
    have hmat : Continuous (fun g : HA (AF F) σ J =>
        ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) :=
      Units.continuous_val.comp continuous_subtype_val
    show Continuous (fun p : HA (AF F) σ J × (Fin a → Fin M → AF F ⊗[F] E) =>
      actTup (AF F) (HA.mat (AF F) σ J p.1) p.2)
    unfold actTup
    exact continuous_pi fun i => (hmat.comp continuous_fst).matrix_mulVec
      ((continuous_apply i).comp continuous_snd)
  have hgp := gramPres_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have hot := orbTup_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have horb : MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) X0) =
      (fun y => gramR (AF F) σ J y) ⁻¹' {(gramE σ J X0).map (inclR (AF F))} := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      simp only [mem_preimage, mem_singleton_iff]
      show gramR (AF F) σ J (g • ratTup (F := F) (AF F) X0) = _
      rw [hgp, LocPosW.gramR_ratTup]
    · intro hy
      obtain ⟨g, hg⟩ := hot y hy
      exact ⟨g, hg⟩
  have hcl : IsClosed (MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) X0)) := by
    rw [horb]
    exact isClosed_singleton.preimage (continuous_gramR (AF F) σ J)
  exact orbit_proper (G := HA (AF F) σ J) (ratTup (F := F) (AF F) X0) hcl K hK

end PI.VolStabS.OrbProperW
