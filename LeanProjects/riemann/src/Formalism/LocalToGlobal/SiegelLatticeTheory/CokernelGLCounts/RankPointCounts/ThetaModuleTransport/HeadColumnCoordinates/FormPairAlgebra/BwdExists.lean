import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LiftRepMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.LamSZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.MulVecSingleApply

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

private theorem exists_cj_combination_of_isUnit_det (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (y' : Fin (r + 1) → O) :
    ∃ w : Fin (r + 1) → E, ∀ b, (y' b : E) = ∑ a, cj (Z.map O.subtype a b) * w a := by
  set N : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (Z.map O.subtype).transpose.map cj with hN
  have hdet : IsUnit N.det := by
    have h1 : N.det = cj (Z.map O.subtype).det := by
      rw [hN, ← Matrix.det_transpose (Z.map O.subtype)]
      exact (RingHom.map_det cj _).symm
    rw [h1]
    exact hu.map cj
  refine ⟨N⁻¹.mulVec (fun j => (y' j : E)), fun b => ?_⟩
  have h2 : N.mulVec (N⁻¹.mulVec (fun j => (y' j : E))) = fun j => (y' j : E) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  have h3 := congrFun h2 b
  rw [← h3]
  simp [Matrix.mulVec, dotProduct, hN]

theorem pair_eG (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ : kap O Z₂ = kap O Z₁) (p : PairSet O cj hO Z₁ Z₂) :
    p.1.2 (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂) := by
  obtain ⟨y₂', hy₂'⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (eCl (cjT O cj hO Z₁)))
  have hlam : lamS O cj Z₂ y₂' = lamS O cj Z₁ (Pi.single (Fin.last r) 1) :=
    p.2.2.1 (Pi.single (Fin.last r) 1) y₂' hy₂'.symm
  set d : Fin (r + 1) → O := y₂' - Pi.single (Fin.last r) 1 with hd
  obtain ⟨w, hw⟩ := exists_cj_combination_of_isUnit_det O cj Z₂ hu₂ d
  have hlast : w (Fin.last r) = 0 := by
    rw [← lamS_cjT O cj Z₂ hu₂ d w hw, hd, lamS_sub, hlam, lamS_e', lamS_e', hκ, sub_self]
  have hmem : ∀ a, w a ∈ O := by
    intro a
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
      (p.1.1.symm (Submodule.Quotient.mk (Pi.single a 1)))
    have h1 : p.1.1 (Submodule.Quotient.mk c) = Submodule.Quotient.mk (Pi.single a 1) := by
      rw [hc]
      simp
    have hB := p.2.2.2 c (Pi.single (Fin.last r) 1) (Pi.single a 1) y₂' h1 hy₂'.symm
    have hL := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 c (Pi.single a 1) h1
    have hsplit : y₂' = d + Pi.single (Fin.last r) 1 := by
      rw [hd]
      abel
    rw [hsplit, bRaw_add_right, bRaw_e, bRaw_e, hL, add_sub_cancel_right,
      bRaw_cjT O cj hcj Z₂ hu₂ _ d w hw] at hB
    have hs : (∑ b : Fin (r + 1), cj (w b) * ((Pi.single a (1 : O) : Fin (r + 1) → O) b : E)) = cj (w a) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [hs] at hB
    have := hO _ hB
    rwa [hcj] at this
  have hdmem : d ∈ headCols (cjT O cj hO Z₂) := by
    rw [mem_headCols_iff]
    refine ⟨fun a => ⟨w a, hmem a⟩, Subtype.ext hlast, ?_⟩
    funext b
    apply Subtype.ext
    rw [cjT_mulVec_coe]
    exact hw b
  rw [← hy₂']
  exact (Submodule.Quotient.eq _).2 hdmem

section Bwd

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
  (hcT : cj (t : E) = t) (hcT' : cj (t' : E) = t') {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
  (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
  (hκ : kap O Z₂ = kap O Z₁)
  (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
  (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)

include hcj hu₁ hu₂ hκ hG₁ hG₂ in

theorem form_diff (p : PairSet O cj hO Z₁ Z₂) (Y Y₂ W W₂ : Ix r → O)
    (hy : p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)) = Submodule.Quotient.mk fun j => Y₂ (Sum.inl j))
    (hy' : p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)) = Submodule.Quotient.mk fun j => Y₂ (Sum.inr j))
    (hw : p.1.1 (Submodule.Quotient.mk fun j => W (Sum.inl j)) = Submodule.Quotient.mk fun j => W₂ (Sum.inl j))
    (hw' : p.1.2 (Submodule.Quotient.mk fun j => W (Sum.inr j)) = Submodule.Quotient.mk fun j => W₂ (Sum.inr j)) :
    formC O cj (Z₂.map O.subtype) t t' Y₂ W₂ - formC O cj (Z₁.map O.subtype) t t' Y W ∈ O := by
  have hl : lamC (Z₂.map O.subtype) (fun j => ((Y₂ (Sum.inl j) : O) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((Y (Sum.inl j) : O) : E)) :=
    lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 _ _ hy
  have hs : lamStarC cj (Z₂.map O.subtype) (fun j => ((Y₂ (Sum.inr j) : O) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Y (Sum.inr j) : O) : E)) :=
    p.2.2.1 _ _ hy'
  have hlw : lamC (Z₂.map O.subtype) (fun j => ((W₂ (Sum.inl j) : O) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((W (Sum.inl j) : O) : E)) :=
    lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 _ _ hw
  have hsw : lamStarC cj (Z₂.map O.subtype) (fun j => ((W₂ (Sum.inr j) : O) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((W (Sum.inr j) : O) : E)) :=
    p.2.2.1 _ _ hw'
  obtain ⟨hc1, hc2⟩ := cG_transfer O cj hcj Z₁ Z₂ hu₁ hu₂ _ _ hG₁ hG₂ hκ Y Y₂ hl hs
  have hb1 := p.2.2.2 _ _ _ _ hy hw'
  have hb2 := p.2.2.2 _ _ _ _ hw hy'
  rw [formC_eqG O cj hcj Z₂ hu₂ _ _ hG₂, formC_eqG O cj hcj Z₁ hu₁ _ _ hG₁, hc1, hc2, hlw, hsw]
  have key : ∀ a b c d X X' : E,
      (a + cj b + X + X') - (c + cj d + X + X') = (a - c) + cj (b - d) := by
    intro a b c d X X'
    rw [map_sub]
    ring
  rw [key]
  exact add_mem hb1 (hO _ hb2)

end Bwd

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
