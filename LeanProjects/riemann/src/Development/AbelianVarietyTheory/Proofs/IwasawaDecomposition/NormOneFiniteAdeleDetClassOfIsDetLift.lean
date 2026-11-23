import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90USurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetMulConjDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
import Formalism.LocalToGlobal.Columns.RecLevelTop

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def detU : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* U1 (host_cmData R H).sig :=
  (Matrix.GeneralLinearGroup.det.comp (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)).subtype).codRestrict _ fun x =>
    Units.ext (DetLift.det_mul_conj_det _ _ x.2)

def u1Dt (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* DtQ H SQ :=
  (normOneIdeleToFinerDeterminantClass H SQ (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
    (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).comp (detU H)

theorem normOneFiniteAdeleDetClass_of_isDetLift (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E)
    (ha : IsDetLift (host_cmData R H) x.1 a) : u1Dt H SQ x = QuotientGroup.mk a := by
  have e : detU H x = ⟨h90 (host_cmData R H).sig (finAf H.F H.E a), by
      rw [ha]; exact (detU H x).2⟩ := Subtype.ext ha.symm
  show normOneIdeleToFinerDeterminantClass H SQ _ _ _ _ _ (detU H x) = _
  rw [e]
  exact normOneIdeleToFinerDeterminantClass_eq_mk H SQ _ _ _ _ _ _ _ _ (afIso_finAf H.F H.E a).symm

theorem exists_lift (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) : ∃ a : GlobalTheory.Mem.Chr.Ideles H.E, IsDetLift (host_cmData R H) x.1 a :=
  DetLift.exists_isDetLift R H 1 x.1 x.2

theorem exists_of_idele (a : GlobalTheory.Mem.Chr.Ideles H.E) : ∃ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), IsDetLift (host_cmData R H) x.1 a := by
  have hu : h90 (host_cmData R H).sig (finAf H.F H.E a) ∈ U1 (host_cmData R H).sig :=
    (DetClass.exists_detClass R H (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
      (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).1.le ⟨_, rfl⟩
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 1) (h90 (host_cmData R H).sig (finAf H.F H.E a)), ?_⟩, ?_⟩
  · show Formalism.UG.cT _ _ * _ * _ = _
    have hz := congrArg Units.val (show (h90 (host_cmData R H).sig (finAf H.F H.E a)) * conjId (host_cmData R H).sig (h90 (host_cmData R H).sig (finAf H.F H.E a)) = 1 from hu)
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Formalism.UG.cT, Matrix.mul_apply]
    exact (mul_comm _ _).trans hz
  · exact Units.ext (by simp)

theorem normOneFiniteAdeleDetClass_surjective (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Function.Surjective (u1Dt H SQ) := fun t => by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨x, hx⟩ := exists_of_idele H a
  exact ⟨x, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩

end GlobalTheory.Mem.Col2.FullDt

end
