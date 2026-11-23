import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetCharacterAverageVectorIndep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.MirAvg

theorem bc_ringEquiv_eq_one_iff {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K) :
    Formalism.UG.bc (e : K →+* K') h = 1 ↔ h = 1 := by
  refine ⟨fun H => ?_, fun H => by rw [H, map_one]⟩
  ext i j
  have := congrArg (fun u : GL (Fin r) K' => (u : Matrix (Fin r) (Fin r) K') i j) H
  apply e.injective
  have h1 : ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K') i j
      = e ((h : Matrix (Fin r) (Fin r) K) i j) := rfl
  simp only [h1] at this
  rw [this]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem bc_ringEquiv_mulVec {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K)
    (x : Fin r → K) :
    ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K').mulVec (fun j => e (x j)) =
      fun j => e ((h : Matrix (Fin r) (Fin r) K).mulVec x j) := by
  funext j
  have h1 : ∀ i j, ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K') i j
      = e ((h : Matrix (Fin r) (Fin r) K) i j) := fun _ _ => rfl
  simp only [Matrix.mulVec, dotProduct, h1, map_sum, map_mul]

theorem det_bc_ringEquiv {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K) :
    Matrix.GeneralLinearGroup.det (Formalism.UG.bc (e : K →+* K') h) =
      Units.map (e : K →* K') (Matrix.GeneralLinearGroup.det h) := by
  ext
  exact ((e : K →+* K').map_det (h : Matrix (Fin r) (Fin r) K)).symm

theorem mirSet_iff_bc {g : ℕ} [Fact g.Prime] {r : ℕ} {K' : Type} [CommRing K'] (e : ZMod g ≃+* K')
    (h : GL (Fin r) (ZMod g)) (a : Fin r → K') (b : Bool) :
    (if b then ∀ x, ∃ c : K', ((Formalism.UG.bc (e : ZMod g →+* K') h : GL (Fin r) K') :
        Matrix (Fin r) (Fin r) K').mulVec x - x = c • a
      else ∀ x, a ⬝ᵥ x = 0 → ((Formalism.UG.bc (e : ZMod g →+* K') h : GL (Fin r) K') :
        Matrix (Fin r) (Fin r) K').mulVec x = x) ↔ mirSet (fun j => e.symm (a j)) b h := by
  have hs : Function.Surjective (fun (x : Fin r → ZMod g) j => e (x j)) :=
    fun x => ⟨fun j => e.symm (x j), by funext j; simp⟩
  cases b with
  | true =>
    simp only [mirSet, if_true]
    rw [hs.forall]
    refine forall_congr' fun x => ?_
    rw [bc_ringEquiv_mulVec, e.surjective.exists]
    refine exists_congr fun c => ?_
    simp only [funext_iff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun j => ?_
    rw [← e.injective.eq_iff (a := _ - _), map_sub, map_mul, e.apply_symm_apply]
  | false =>
    simp only [mirSet, Bool.false_eq_true, if_false]
    rw [hs.forall]
    refine forall_congr' fun x => ?_
    rw [bc_ringEquiv_mulVec]
    refine imp_congr ?_ ?_
    · rw [← e.injective.eq_iff (b := 0), map_zero]
      simp only [dotProduct, map_sum, map_mul, e.apply_symm_apply]
    · simp only [funext_iff, e.injective.eq_iff]

theorem mirC_eq_coeff_mirEl : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eR : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) →
    ∀ (i : Fin D.R.m) (kv0 : Σ k : Fin 2, D.nd.PlG k) (a : Fin D.R.r → kP (plg kv0).1) (b : Bool) (ε : ℤ) (y : G),
    haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
    GlobalTheory.DownLift.mirC R i (plg kv0) a b ε y = (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then
      (GlobalTheory.MirAvg.mirEl ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) (plg kv0).1).comp
        (Units.map (iso kv0 : ZMod (D.host.g kv0.1) →* kP (plg kv0).1))))
        (fun j => (iso kv0).symm (a j)) b).coeff (eR y kv0) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R eR plg iso hrec i kv0 a b ε y
  haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
  have h1 : (∀ PP', PP' ≠ plg kv0 → R.eG y PP' = 1) ↔ ∀ kv, kv ≠ kv0 → eR y kv = 1 := by
    rw [plg.surjective.forall]
    refine forall_congr' fun kv => imp_congr plg.injective.ne_iff ?_
    rw [hrec]
    exact bc_ringEquiv_eq_one_iff _ _
  have h2 := mirSet_iff_bc (iso kv0) (eR y kv0) a b
  have h3 := det_bc_ringEquiv (iso kv0) (eR y kv0)
  rw [← hrec] at h2 h3
  rw [mirEl_coeff]
  unfold GlobalTheory.DownLift.mirC
  by_cases hA : ∀ kv, kv ≠ kv0 → eR y kv = 1
  · rw [if_pos hA]
    by_cases hB : mirSet (fun j => (iso kv0).symm (a j)) b (eR y kv0)
    · rw [if_pos hB, if_pos ⟨h1.2 hA, h2.2 hB⟩, h3]
      rfl
    · rw [if_neg hB, if_neg fun H => hB (h2.1 H.2)]
  · rw [if_neg hA, if_neg fun H => hA (h1.1 H.1)]

end GlobalTheory.MirAvg

end
