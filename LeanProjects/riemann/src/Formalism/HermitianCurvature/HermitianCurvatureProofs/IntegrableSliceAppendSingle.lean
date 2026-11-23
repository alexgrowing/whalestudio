import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem point_size_append_single (h : C.LPt) (c : ℂ) : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := by
  rw [Dx2.SL.ptSize_append]

theorem integrable_slice_append_single {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h : C.LPt) (c : ℂ)
    (hle : D.ptSize (h ++ [(1, c)]) ≤ r) (hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])))
    (γ' : B.Mat k (r - D.ptSize (h ++ [(1, c)])))
    (hI : Integrable (JCTx6.gInt k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
        (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
        (D.castF (by have := point_size_append_single h c; omega) F) γ')
      (JCTx6.muG k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h))) :
    Integrable (fun ξ : U.Xi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) =>
        U.psiStar k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) (D.castV (by omega) z)
            (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))
            (D.ptDiag (h ++ [(1, c)])) ξ (fun a => a.elim0) γ'))
      (U.muXi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))) := by
  have hP : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := point_size_append_single h c
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ (Dx2.SL.isLocPt_head hloc)).1
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) (Fin.cast hP a)).val = (D.ptPerm (h ++ [(1, c)]) a).val := by
    intro a
    rw [hspec a, Dx2.SL.partner_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      Dx2.SL.dP (n := 0) (D.ptDiag h) c (Fin.cast hP a) = D.ptDiag (h ++ [(1, c)]) a := by
    intro a
    simp only [D.ptDiag]
    rw [Dx2.SL.scal_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.dP, Fin.addCases_right]

  have hσ' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      (D.ptPerm (h ++ [(1, c)]) (Fin.cast hP.symm b)).val = ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) b).val := by
    intro b
    have := hσ (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have hd' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      D.ptDiag (h ++ [(1, c)]) (Fin.cast hP.symm b) = Dx2.SL.dP (n := 0) (D.ptDiag h) c b := by
    intro b
    have := hd (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have h1 := JCTx6.Int.orbit_slice_integrable k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z') E
    (D.castF (by have := point_size_append_single h c; omega) F) γ' hI
  have h2 := (Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(1, c)])) hP.symm _ _ hσ' _ _ hd'
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
    (D.castF (by have := point_size_append_single h c; omega) F) γ').1 h1
  simpa only [Dx2.SL.castV_castV, Dx2.SL.castF_castF] using h2

end Formalism.FourierDecayAlt.P.PBH
