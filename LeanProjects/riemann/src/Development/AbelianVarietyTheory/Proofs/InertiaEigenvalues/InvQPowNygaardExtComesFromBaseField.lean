import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SepOfHausdorff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.TransitionThirdCase

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem jD_Qpow (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (m : ℕ)
    (x : ((HW l).W K s LL h).DD T) :
    ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).Q ^ m • x) =
      (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ)) ^ m • ((F l).E K s LL h).tie.jD T x := by
  have hQ := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  rw [← algebraMap_smul ((HW l).W K s LL h).EE (((HW l).W K s LL h).Q ^ m) x,
    ((F l).E K s LL h).tie.jD_smul, ((F l).E K s LL h).tie.ioE_ext, map_pow, hQ, map_pow]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (m : ℕ) (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m) → ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m), ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT m y' hy'
  have hB := GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0
  have hB3 := hB.2.2 T (resLt (K := K) (K' := K') (LL := LL) hle T) (LinearEquiv.refl (↥(OL LL)) ↥T.L.T)
    (fun g t => rfl)
  have hid : (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap) = LinearMap.id := TensorProduct.map_id
  have hR := hB3.1
  have hN := hB3.2 hT (restrict_crys D hle T hT)
  have hy1 : TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap
      (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') ∈
      Set.range (((F l).E K s LL h).tie.jD T) := hR ▸ ⟨_, ⟨y', rfl⟩, rfl⟩
  have hy2 : TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap
      (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T)
      (((HW l).W K' s LL h').Q ^ m • y')) ∈
      ((F l).E K s LL h).tie.jD T '' (((HW l).W K s LL h).N T : Set (((HW l).W K s LL h).DD T)) :=
    hN ▸ ⟨_, ⟨_, hy', rfl⟩, rfl⟩
  have hm1 := LinearMap.congr_fun hid (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y')
  have hm2 := LinearMap.congr_fun hid (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T)
      (((HW l).W K' s LL h').Q ^ m • y'))
  refine hy1.elim fun y hy => hy2.elim fun z hz => ⟨y, ?_, hy.trans hm1⟩
  show ((HW l).W K s LL h).Q ^ m • y ∈ ((HW l).W K s LL h).N T
  have e : z = ((HW l).W K s LL h).Q ^ m • y := by
    apply ((F l).E K s LL h).tie.jD_inj T
    rw [hz.2, hm2, jD_Qpow, jD_Qpow, hy, hm1]
    rfl
  exact e ▸ hz.1

end GlobalTheory.NL.TransitionThirdCase
