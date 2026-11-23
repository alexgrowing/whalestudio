import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LiftRepMem

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
include hcj

theorem form_pair (ht : cj (t : E) = t) (ht' : cj (t' : E) = t')
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)
    (p : PairSet O cj hO Z₁ Z₂) (Y W : Ix r → O) :
    formC O cj (Z₂.map O.subtype) t t'
        (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
          (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)))
        (Sum.elim (liftOf O p.1.1.toLinearMap fun j => W (Sum.inl j))
          (liftOf O p.1.2.toLinearMap fun j => W (Sum.inr j))) -
      formC O cj (Z₁.map O.subtype) t t' Y W ∈ O := by
  have hl : ∀ y : Fin (r + 1) → O, (Submodule.Quotient.mk (liftOf O p.1.1.toLinearMap y) : MbMod Z₂) =
      p.1.1.toLinearMap (Submodule.Quotient.mk y) := fun y => liftOf_spec O _ y
  have hr : ∀ y : Fin (r + 1) → O, (Submodule.Quotient.mk (liftOf O p.1.2.toLinearMap y) : MbMod (cjT O cj hO Z₂)) =
      p.1.2.toLinearMap (Submodule.Quotient.mk y) := fun y => liftOf_spec O _ y
  have hb : ∀ y y' : Fin (r + 1) → O,
      bRaw O cj Z₂ (liftOf O p.1.1.toLinearMap y) (liftOf O p.1.2.toLinearMap y') - bRaw O cj Z₁ y y' ∈ O :=
    fun y y' => p.2.2.2 y y' _ _ (hl y).symm (hr y').symm
  have hL : ∀ y : Fin (r + 1) → O,
      lamC (Z₂.map O.subtype) (fun j => ((liftOf O p.1.1.toLinearMap y j : O) : E)) =
        lamC (Z₁.map O.subtype) (fun j => ((y j : O) : E)) := by
    intro y
    have key := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y _ (hl y).symm
    simpa [lamL_apply] using key
  have hS : ∀ y : Fin (r + 1) → O,
      lamStarC cj (Z₂.map O.subtype) (fun j => ((liftOf O p.1.2.toLinearMap y j : O) : E)) =
        lamStarC cj (Z₁.map O.subtype) (fun j => ((y j : O) : E)) :=
    fun y => p.2.2.1 y _ (hr y).symm
  rw [formC_eq O cj hcj Z₂ hu₂ hκ₂ _ _ hG₂, formC_eq O cj hcj Z₁ hu₁ hκ₁ _ _ hG₁]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hL, hL, hS, hS]
  have key := O.add_mem (hb (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)))
    (hO _ (hb (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))))
  rw [map_sub] at key
  convert key using 1
  ring

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
