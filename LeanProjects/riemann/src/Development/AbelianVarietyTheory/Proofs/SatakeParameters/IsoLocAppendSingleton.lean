import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaEigenspaceImage
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftOfEachRow

noncomputable section

namespace GlobalTheory.ParUpRoad

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem spehLoc_twist (hL : ParamLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  obtain ⟨hsum, hzero, htw, -, -⟩ := hL w
  have hχ := A.locG_dim χ w
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact (hzero _ hχ).symm
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, hsum _ _ _ hχ, htw _ _ _ hχ, A.locG_tw]

theorem isoLoc_twist (hL : ParamLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w).2.1 _ hχ).symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, spehLoc_twist N A hL, (hL w).1 _ _ _ hχ]

theorem isoLoc_append_singleton (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil =>
    change A.lpSum (spehLoc N A q w) (A.lpZero w) = A.lpSum (A.lpZero w) (spehLoc N A q w)
    exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

theorem isoLoc_lift (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by
  rw [isoLoc_twist N A hL, isoLoc_append_singleton]
  rfl

theorem ptV_of_thetaOf (hL : ParamLaws N A) {i : N.Loc} (hS : SplitLift N A i) (hP : PtOfLoc N A i)
    {x : N.X i} {Sig : List (Part A.CG)} (hx : HasParamX N A i x Sig) {σ : what₂.FT}
    (hσ : ∀ w, SplitOut N i w → isoLoc N A Sig w = A.locW i σ w) {P : A.AV i}
    (hθ : thetaOf N A i σ P) : A.ptV i P = some x := by
  obtain ⟨P', hP', hbc⟩ := hx
  refine hP P P' x hP' fun w hw => ?_
  rw [hS σ P hθ w hw.1, ← hσ w hw, ← isoLoc_lift N A hL, hbc.2.2.2.1 w hw.1]

theorem thetaTMapsIntoEigOut (hθ : EachRowHasThetaLift N A) (hL : ParamLaws N A)
    (hS : ∀ i, SplitLift N A i) (hP : ∀ i, PtOfLoc N A i) : ThetaTMapsIntoEigOut N A := by
  intro i x Sig _ hx
  have key : MjSigOut N A i Sig ≤ (eigC N A i x).comap (what₂.thetaT (N.mu i) (N.j i)) := by
    unfold MjSigOut
    refine iSup₂_le fun σ hσ => ?_
    by_cases h0 : what₂.isot (N.j i) σ = ⊥
    · rw [h0]; exact bot_le
    obtain ⟨P, hPθ⟩ := hθ i σ h0
    have hpt : A.ptV i P = some x := ptV_of_thetaOf N A hL (hS i) (hP i) hx hσ hPθ
    rw [← Submodule.map_le_iff_le_comap]
    refine hPθ.2.trans ?_
    unfold eigC
    exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | A.ptV i P = some x}) => A.typeV i P) P hpt le_rfl
  exact fun f hf => key hf

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    EachRowHasThetaLift N A → ParamLaws N A → (∀ i, SplitLift N A i) → (∀ i, PtOfLoc N A i) →
      ThetaTMapsIntoEig N A :=
  fun _ _ _ N A hθ hL hS hP => thetaTMapsIntoEig_of_out N A (thetaTMapsIntoEigOut N A hθ hL hS hP)

end GlobalTheory.ParUpRoad
