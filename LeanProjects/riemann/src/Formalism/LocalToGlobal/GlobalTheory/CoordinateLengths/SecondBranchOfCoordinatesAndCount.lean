import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.CrdLBwLe
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

def OntoAt {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT)
    (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) : Prop :=
  (Submodule.pi Set.univ fun c =>
      ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))) ≤ ((D.fm u).Bw 0 w v).map (crdL T B w) ∧
  (Submodule.pi Set.univ fun _ => (intSubm D w ((D.fm u).lam 0)).map
      (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)))) ≤
    (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)).map (crdL T B w)

def SecondBranchCoordinates (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ T : Forms0 D u, admS D u → ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
    ∃ B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E,
      (∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) ∧
      (∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c)) ∧
      (∀ c, (((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
          (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
        ((D.mem u).A.T : ℂ) * ((((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) :
          Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w) ∧
      OntoAt T w v B B'

def DuCount (D : D7) (u : D.what₂.Word) : Prop :=
  D.duS u = Fintype.card ((D.mem u).C.cls 0) * ∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))

theorem lenLen2_of_coordOnto {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (hA : admS D u) (hC : SecondBranchCoordinates D u)
    (hd : DuCount D u) : SeenPlaceLatticeLengthFormula D u := by
  intro w hw hs v hb
  obtain ⟨B, B', hB, hB', hu, hO1, hO2⟩ := hC T hA w hw hs v hb
  exact lenLen2_of_coord D u T.atT T.lv0 w hw v (fun c => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.bwL_lcInt0 D u T 0 (Nat.zero_le _) rfl c) B B' hB hB' hu
    (crdL T B w) (crdL_inj T B w) (le_antisymm (crdL_Bw_le T w hw hs v B B' hB hB') hO1)
    (le_antisymm (crdL_tL_le T w hw B hB _) hO2) hd

theorem second_branch_of_coordinates_and_count (hC : ∀ (D : D7) (u : D.what₂.Word), SecondBranchCoordinates D u)
    (hd : ∀ (D : D7) (u : D.what₂.Word), Forms0 D u → admS D u → DuCount D u) :
    ∀ (D : D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u := fun D u =>
  Formalism.MainNotions.lemmaB_second_branch_of_length_formula D u fun _ hT => by
    obtain ⟨⟨Ch, chOf, T, -⟩, hA⟩ := hT
    exact lenLen2_of_coordOnto T.to0 hA (hC D u) (hd D u T.to0 hA)

end Formalism.L2.GlobalTheoryTheory.LemB
