import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.DetLift

theorem det_mul_conj_det {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (ι : B →+* A) {n : ℕ} {g : GL (Fin n) A}
    (hg : g ∈ Formalism.UG.UJ σ ((1 : Matrix (Fin n) (Fin n) B).map ι)) :
    (g : Matrix (Fin n) (Fin n) A).det * σ (g : Matrix (Fin n) (Fin n) A).det = 1 := by
  have h : Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * (1 : Matrix (Fin n) (Fin n) B).map ι * (g : Matrix (Fin n) (Fin n) A) =
      (1 : Matrix (Fin n) (Fin n) B).map ι := hg
  rw [Matrix.map_one _ (map_zero ι) (map_one ι), mul_one] at h
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, Matrix.det_one] at h2
  rw [mul_comm, RingHom.map_det]
  exact h2

theorem exists_isDetLift : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (g : GL (Fin n) (AfE H.F H.E)), g ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → ∃ a : Ideles H.E, IsDetLift (host_cmData R H) g a := by
  intro R H n g hg
  have hr := (DetClass.exists_detClass R H (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
    (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).1
  have hd : Matrix.GeneralLinearGroup.det g ∈ U1 (host_cmData R H).sig :=
    Units.ext (det_mul_conj_det _ _ hg)
  obtain ⟨x, hx⟩ := hr.ge hd
  obtain ⟨a, rfl⟩ := finAf_surjective H.F H.E x
  exact ⟨a, hx⟩

end GlobalTheory.Mem.DetLift
