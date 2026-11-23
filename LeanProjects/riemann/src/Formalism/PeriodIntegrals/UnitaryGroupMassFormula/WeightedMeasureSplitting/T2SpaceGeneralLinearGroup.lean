import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Closed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosed_uniFlag {m : ℕ} (Y : Fin m → Fin n → E) :
    IsClosed (uniFlag R σ J Y : Set (HA R σ J)) := by
  have : (uniFlag R σ J Y : Set (HA R σ J)) =
      ⋂ b, (fun g => lin R σ J g (ratV (F := F) R (Y b)) - ratV (F := F) R (Y b)) ⁻¹'
        (spanR (F := F) R Y {a | a < b} : Set (Fin n → R ⊗[F] E)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  rw [this]
  exact isClosed_iInter fun b =>
    (PI.VolSemiDirect.W.isClosed_spanR _ _).preimage
      ((PI.VolSemiDirect.W.continuous_lin R σ J _).sub continuous_const)

theorem isClosed_Hsub {r : ℕ} (P : Frame E n r) : IsClosed (Hsub R σ J P : Set (HA R σ J)) :=
  PI.VolSemiDirect.W.isClosed_stabT (R := R) (σ := σ) (J := J) _

theorem isClosed_Nsub {r : ℕ} (P : Frame E n r) : IsClosed (Nsub R σ J P : Set (HA R σ J)) := by
  have hset : (Nsub R σ J P : Set (HA R σ J)) = (uniFlag R σ J P.e : Set (HA R σ J)) ∩
      ⋂ v ∈ {v : Fin n → R ⊗[F] E | InXperp R σ J P v},
        (fun g : HA R σ J => lin R σ J g v - v) ⁻¹'
          (spanR (F := F) R P.e Set.univ : Set (Fin n → R ⊗[F] E)) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
    rfl
  rw [hset]
  refine (isClosed_uniFlag R σ J P.e).inter (isClosed_biInter fun v _ => ?_)
  exact (PI.VolSemiDirect.W.isClosed_spanR (R := R) P.e _).preimage
    ((PI.VolSemiDirect.W.continuous_lin (R := R) (σ := σ) (J := J) v).sub continuous_const)

theorem isClosed_Ssub {r : ℕ} (P : Frame E n r) : IsClosed (Ssub R σ J P : Set (HA R σ J)) :=
  isClosed_uniFlag R σ J (F0 P)

instance lc_Hsub {r : ℕ} (P : Frame E n r) : LocallyCompactSpace (Hsub R σ J P) :=
  (isClosed_Hsub R σ J P).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance lc_Nsub {r : ℕ} (P : Frame E n r) : LocallyCompactSpace (Nsub R σ J P) :=
  (isClosed_Nsub R σ J P).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance lc_Ssub {r : ℕ} (P : Frame E n r) : LocallyCompactSpace (Ssub R σ J P) :=
  (isClosed_Ssub R σ J P).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance t2Space_general_linear_group : T2Space (GL (Fin n) (R ⊗[F] E)) := Units.isEmbedding_embedProduct.t2Space

instance t2Space_hermitian_adeles : T2Space (HA R σ J) := inferInstanceAs (T2Space (HR R σ J))

end Gen

section NF

variable (F : Type) [Field F] [NumberField F]

instance lc_Fv (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (Fv F v) :=
  (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((PI.VolStabSW.TopoAF.isOpen_integers F v).mem_nhds (zero_mem _))

variable {F} {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

instance sc_HAinf : SecondCountableTopology (HA (Ainf F) σ J) :=
  PI.VolStabSW.TopoAF.secondCountable_HA_of (Ainf F) σ J

instance sc_HAf : SecondCountableTopology (HA (Af F) σ J) :=
  PI.VolStabSW.TopoAF.secondCountable_HA_of (Af F) σ J

example (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) :
    LocallyCompactSpace (Ssub (Fv F v) σ J P) := inferInstance

instance sc_subInf (K : Subgroup (HA (Ainf F) σ J)) : SecondCountableTopology K :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance sc_subF (K : Subgroup (HA (Af F) σ J)) : SecondCountableTopology K :=
  TopologicalSpace.Subtype.secondCountableTopology _

example {r : ℕ} (P : Frame E n r) : SigmaCompactSpace (Hsub (Ainf F) σ J P) := inferInstance
example {r : ℕ} (P : Frame E n r) : SigmaCompactSpace (Nsub (Af F) σ J P) := inferInstance

end NF

end PI.UnitaryGroupMassFormula.MeasWCore
