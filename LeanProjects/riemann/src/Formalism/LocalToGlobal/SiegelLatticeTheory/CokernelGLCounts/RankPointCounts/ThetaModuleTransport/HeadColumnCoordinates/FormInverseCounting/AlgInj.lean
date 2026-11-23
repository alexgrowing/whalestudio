import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgDefs

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem bRaw_sub_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y a c : Fin (r + 1) → O) :
    bRaw O cj Z y (a - c) = bRaw O cj Z y a - bRaw O cj Z y c := by
  unfold bRaw
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.sub_apply]
  push_cast
  rw [map_sub, sub_mul]

theorem lamS_sub (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (a c : Fin (r + 1) → O) :
    lamS O cj Z (a - c) = lamS O cj Z a - lamS O cj Z c := by
  unfold lamS
  have h := lamStarC_add cj (Z.map O.subtype) (fun b => (((a - c) b : O) : E)) (fun b => ((c b : O) : E))
  have e : ((fun b => (((a - c) b : O) : E)) + fun b => ((c b : O) : E)) = fun b => ((a b : O) : E) := by
    funext b
    simp
  rw [e] at h
  exact eq_sub_of_add_eq h.symm

theorem coe_single (a : Fin (r + 1)) :
    (fun j => (((Pi.single a (1 : O) : Fin (r + 1) → O) j : O) : E)) = Pi.single a 1 := by
  funext j
  by_cases h : j = a
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem mk_eq_zero_of (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (y' : Fin (r + 1) → O) (hB : ∀ y, bRaw O cj Z y y' ∈ O) (hl : lamS O cj Z y' = 0) :
    (Submodule.Quotient.mk y' : MbMod (cjT O cj hO Z)) = 0 := by
  set Ze := Z.map O.subtype with hZe
  let w' : Fin (r + 1) → E := fun a => ∑ j, cj (Ze⁻¹ j a) * (y' j : E)
  have hB1 : ∀ a, bRaw O cj Z (Pi.single a 1) y' = cj (w' a) := by
    intro a
    simp only [bRaw, w', map_sum, map_mul, hcj]
    rw [coe_single, Matrix.mulVec_single_one]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]; rfl
  have hw : ∀ a, w' a ∈ O := by
    intro a
    have := hO _ (hB1 a ▸ hB (Pi.single a 1))
    rwa [hcj] at this
  have hlast : w' (Fin.last r) = 0 := hl
  have hinv : Ze⁻¹ * Ze = 1 := Matrix.nonsing_inv_mul _ hu
  have key : ∀ b, (y' b : E) = ∑ a, cj (Ze a b) * w' a := by
    intro b
    simp only [w', Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ j, ∑ a, cj (Ze a b) * (cj (Ze⁻¹ j a) * (y' j : E)) =
        cj ((Ze⁻¹ * Ze) j b) * (y' j : E) := by
      intro j
      rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul]; ring
    simp only [h2, hinv, Matrix.one_apply]
    simp
  let wO : Fin (r + 1) → O := fun a => ⟨w' a, hw a⟩
  have hwO : wO (Fin.last r) = 0 := Subtype.ext hlast
  have hy : y' = (cjT O cj hO Z).mulVec wO := by
    funext b
    apply Subtype.ext
    rw [key b]
    simp [Matrix.mulVec, dotProduct, cjT, wO, Ze]
  rw [Submodule.Quotient.mk_eq_zero, hy]
  exact mulVec_mem_headCols _ _ hwO

theorem stepInj : StepInj := by
  intro E _ O cj hcj hO r Z₁ Z₂ hu₁ hu₂ p q hpq
  obtain ⟨⟨γ, γs⟩, hp⟩ := p
  obtain ⟨⟨γ', γs'⟩, hq⟩ := q
  have h1 : γ = γ' := congrArg (fun x : IsoMbe Z₁ Z₂ => x.1) hpq
  subst h1
  have hs : γs = γs' := by
    apply LinearEquiv.ext
    intro ms
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ ms
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (γs (Submodule.Quotient.mk y'))
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (γs' (Submodule.Quotient.mk y'))
    rw [← ha, ← hc, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
    apply mk_eq_zero_of O cj hcj hO Z₂ hu₂
    · intro y
      obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (γ.symm (Submodule.Quotient.mk y))
      have e1 : γ (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y := by
        rw [hy₁]; exact γ.apply_symm_apply _
      have A := hp.2.2 y₁ y' y a e1 ha.symm
      have B := hq.2.2 y₁ y' y c e1 hc.symm
      have := O.sub_mem A B
      rw [sub_sub_sub_cancel_right] at this
      rw [bRaw_sub_right]
      exact this
    · rw [lamS_sub, hp.2.1 y' a ha.symm, hq.2.1 y' c hc.symm, sub_self]
  subst hs
  rfl

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
