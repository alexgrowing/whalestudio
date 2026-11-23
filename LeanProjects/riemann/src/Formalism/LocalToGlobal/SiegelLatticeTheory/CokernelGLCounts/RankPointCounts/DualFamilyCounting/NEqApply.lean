import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsoGenLeft

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

theorem nL_isom (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs)
    (x y : (VS D).V) : (VS D).hT (nL X X0 xs M x) (nL X X0 xs M y) = (VS D).hT x y := by
  have he : ∀ a y, (VS D).hT (nL X X0 xs M (X.eX a)) (nL X X0 xs M y) = (VS D).hT (X.eX a) y := fun a y =>
    iso_gen_left X X0 xs M hinv hxs hM (X.eX a)
      (fun c => ⟨by rw [nL_e, nL_e]; exact g_ee X X0 a c, by rw [nL_e, nL_f]; exact g_ef X X0 xs M hinv hxs a c⟩)
      (fun w hw => by rw [nL_e]; exact g_ew X X0 xs M hxs hw a) y
  have hf : ∀ a y, (VS D).hT (nL X X0 xs M (X.fY a)) (nL X X0 xs M y) = (VS D).hT (X.fY a) y := fun a y =>
    iso_gen_left X X0 xs M hinv hxs hM (X.fY a)
      (fun c => ⟨by
          rw [nL_f, nL_e, h_symm, g_ef X X0 xs M hinv hxs c a, ← h_symm],
        by rw [nL_f, nL_f]; exact g_ff X X0 xs M hinv hxs hM a c⟩)
      (fun w hw => by rw [nL_f]; exact g_fw X X0 xs M hxs hw a) y
  have hw : ∀ w, InW X w → ∀ y, (VS D).hT (nL X X0 xs M w) (nL X X0 xs M y) = (VS D).hT w y := fun w hw y =>
    iso_gen_left X X0 xs M hinv hxs hM w
      (fun c => ⟨by rw [nL_e, h_symm, g_ew X X0 xs M hxs hw c, ← h_symm],
        by rw [nL_f, h_symm, g_fw X X0 xs M hxs hw c, ← h_symm]⟩)
      (fun w' hw' => g_ww X X0 xs M hxs hw hw') y
  conv_lhs => rw [decomp X x]
  conv_rhs => rw [decomp X x]
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul]
  simp only [he, hf, hw _ (inW_pW X x)]

theorem nL_inj (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs) :
    Function.Injective (nL X X0 xs M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine (VS D).nondeg.1 x fun y => ?_
  rw [← nL_isom X X0 xs M hinv hxs hM x y, hx, map_zero, LinearMap.zero_apply]

def nEq (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs) :
    (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofInjectiveEndo (nL X X0 xs M) (nL_inj X X0 xs M hinv hxs hM)

theorem nEq_apply (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs) (y : (VS D).V) :
    nEq X X0 xs M hinv hxs hM y = nL X X0 xs M y := rfl

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
