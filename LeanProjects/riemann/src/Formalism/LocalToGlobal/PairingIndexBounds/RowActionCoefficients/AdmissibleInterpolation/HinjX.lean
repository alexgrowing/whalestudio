import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ProdRowAct

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem hinjX : Function.Injective (algebraMap X.G.O X.G.Kf) := IsFractionRing.injective X.G.O X.G.Kf

theorem phi_mem (hS : XShape) (hBrS : XBrS) (hInj : XInj) (j : ℕ) (L : (X.Pj j).Tup)
    (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (hg : ∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v)))
    (M : AddSubgroup Kc) (hM : ∀ (o : X.G.O), ∀ a ∈ M, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) * a ∈ M)
    (Φ : (X.Pj j).Xsp →ₗ[X.G.Kf] Kc) (A : MvPolynomial (X.FrI j) Kc) (hA : ∀ m, coeff m A ∈ M)
    (hnum : ∀ x : X.FrI j → X.G.Kf, Φ (sX X j (fun v => g v) • ∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
      (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b)))) = eval (fun t => algebraMap X.G.Kf Kc (x t)) A) :
    ∀ G ∈ (X.Pj j).HtupW L, Φ G ∈ M := by
  have : CharZero X.G.Kf := (algebraMap X.G.Kf Kc).charZero
  let T : Submodule X.G.O (X.Pj j).Xsp :=
    { carrier := {G | Φ G ∈ M}
      add_mem' := fun {a b} ha hb => by
        show Φ (a + b) ∈ M
        rw [map_add]; exact M.add_mem ha hb
      zero_mem' := by show Φ 0 ∈ M; rw [map_zero]; exact M.zero_mem
      smul_mem' := fun o G hG => by
        show Φ (o • G) ∈ M
        rw [← algebraMap_smul X.G.Kf o G, map_smul, Algebra.smul_def]
        exact hM o _ hG }
  refine hBrS p X (hinjX X) j L (fun v => g v) (fun v => (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit) hg T ?_
  intro F hF
  let Φ' : (X.Pj j).Xsp →ₗ[X.G.Kf] Kc := Φ ∘ₗ (LinearMap.lsmul X.G.Kf (X.Pj j).Xsp (sX X j fun v => g v))
  exact src_abs (O := X.G.O) (emX X j) (xmX X j) (hInj p X j).2 (nuM X j) (fun b => mF X j b (g b.1))
    (fun b => mF X j b ((g b.1)⁻¹ : GL _ _)) (fun b => mF_inv_mul X j b (g b.1)) M hM (HgX X X.G.Kf j) (hQX X hS j) Φ' A hA hnum
    interpolation_holds coefficient_product_holds F hF

theorem xSpan (hS : XShape) (hBrS : XBrS) (hInj : XInj) (hSp : XSpanN) (j : ℕ) (L : (X.Pj j).Tup)
    (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (hg : ∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v)))
    (f : MvPowerSeries (X.ZA j) Kc) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).HtupW L) : delF X Kc j G f ∈ WT X Kc j := by
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_le_ker_of_notMem hne
  have h0 := phi_mem X Kc hS hBrS hInj j L g hg ⊥ (fun o a ha => by
    rw [AddSubgroup.mem_bot] at ha ⊢; rw [ha, mul_zero]) (PhiX X Kc j l 1 f) 0 (fun m => by rw [coeff_zero]; exact AddSubgroup.zero_mem _)
    (fun x => by
      obtain ⟨a, x'', hx⟩ := prod_rowAct X j g x
      rw [hx, map_zero, PhiX_apply, one_mul, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
      have h1 : delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x'' b))) f ∈ WT X Kc j := hSp p X Kc j x'' f
      have h2 : l (delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x'' b))) f) = 0 := hl2 h1
      rw [← algebraMap_smul Kc (sX X j fun v => g v), ← algebraMap_smul Kc a, map_smul, map_smul, h2, smul_zero, smul_zero]) G hG
  rw [AddSubgroup.mem_bot, PhiX_apply, one_mul] at h0
  exact hl1 h0

end Formalism.L2.PairingIndexBounds.Ent
