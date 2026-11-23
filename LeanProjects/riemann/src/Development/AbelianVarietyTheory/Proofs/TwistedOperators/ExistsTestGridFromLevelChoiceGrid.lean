import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridPlaceDataOfLevelChoiceGridStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterGridIsAuxiliaryCharacterTestGridStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSelfDualFrameOfStandardSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelOfOrthonormalBasisCartaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridVertexRealParameterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridColumnRealParameterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridRowRealParameterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumTestGridOfLevelChoiceGridStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridRowZeroVerticesAgreeWeilDataStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

section Cast

variable {D : D7}

def hermitianOrthogonalExtensionDataCast {A A' B B' : GlobalTheory.Grid.Node D} {c : ℕ} (hA : A = A') (hB : B = B') (d : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c) :
    GlobalTheory.Grid.HermitianOrthogonalExtensionData A' B' c := hA ▸ hB ▸ d

theorem gridDecompositionCast_is_iff {A A' B B' : GlobalTheory.Grid.Node D} {c : ℕ} (hA : A = A') (hB : B = B') (d : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c)
    (g : Fin c → Fin c → D.host.E) (𝔟 : Fin c → GlobalTheory.Grid.FrId D) : (hermitianOrthogonalExtensionDataCast hA hB d).Is g 𝔟 ↔ d.Is g 𝔟 := by
  subst hA hB; rfl

def hermitianOrthogonalExtensionDataZero (A B : GlobalTheory.Grid.Node D) (c : ℕ) : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c := ⟨0, 0⟩

theorem joinStair {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (c : ℕ) :
    GlobalTheory.ChiGrid.stairId (P.stA sc) (P.stAbar sc) c = GlobalTheory.Grid.staircaseExtensionIdeal (P.modul sc) c := by
  funext p
  simp only [GlobalTheory.ChiGrid.stairId, GlobalTheory.ChiGrid.Places.stA, GlobalTheory.ChiGrid.Places.stAbar, GlobalTheory.ChiGrid.Places.modulBar,
    GlobalTheory.Grid.staircaseExtensionIdeal, mul_pow, inv_pow, mul_inv, inv_inv]

theorem joinStair_top (c : ℕ) :
    GlobalTheory.ChiGrid.stairId D.host.AA D.host.AAbar c = GlobalTheory.Grid.staircaseExtensionIdeal (D := D) ⊤ c := by
  funext p
  simp [GlobalTheory.ChiGrid.stairId, GlobalTheory.Grid.staircaseExtensionIdeal, Ideal.pointwise_smul_def, Ideal.map_top, mul_pow, inv_pow]

theorem joinGram_one : (fun p q : Fin 1 => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix 1 (1 : D.host.E) p q) = fun _ _ => 1 := by
  funext p q
  fin_cases p; fin_cases q; simp [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix]

theorem joinGram_neg (c : ℕ) : (fun p q : Fin c => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c (-1 : D.host.E) p q) = GlobalTheory.Grid.antiDiagonalSignGramMatrix D.host.E c := by
  funext p q
  rfl

end Cast

theorem exists_gridPre_spaces : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesUpqExists → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → (∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → (G'.Λ X : Set _) = L0c D (G'.V X)) → (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → (∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.grid i j)).rank → ℝ) (ε : Fin (G'.V (.grid i j)).rank → Bool), IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε ∧ (W.onb (.grid i j) τ)ᴴ * gramAt D (G'.V (.grid i j)) τ * W.onb (.grid i j) τ = Formalism.REAL.Jm ε) → (∀ i, i ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.core i)).rank → ℝ) (ε : Fin (G'.V (.core i)).rank → Bool), IsEnum (GlobalTheory.Grid.parP D i τ) lam ε ∧ (W.onb (.core i) τ)ᴴ * gramAt D (G'.V (.core i)) τ * W.onb (.core i) τ = Formalism.REAL.Jm ε) → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.top j)).rank → ℝ) (ε : Fin (G'.V (.top j)).rank → Bool), IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε ∧ (W.onb (.top j) τ)ᴴ * gramAt D (G'.V (.top j)) τ * W.onb (.top j) τ = Formalism.REAL.Jm ε) → W.cart (.top 0) = W.cart (.core D.R.m) → W.onb (.top 0) = W.onb (.core D.R.m) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ G : GlobalTheory.Grid.GridPre R, G.idem = e ∧ G.IsSpaces ∧ G.IsChars ∧ SpAgree G W := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDS hH F hR hsc G' W hW hL hPg hsplit hg hT hOV hOP hOX hcT hoT e he
  classical
  obtain ⟨Z, hZ, hq0, hw0, he0, hWZ, hlvl, hS0, hS1⟩ := GlobalTheory.T.testGridPlaceData_of_levelChoiceGrid hR hPg hsplit hg hT e he
  let Sx : GlobalTheory.ChiGrid.Node → D.what₂.Tau → SPar := fun X => match X with
    | .grid i j => GlobalTheory.Grid.parV D i j
    | .core i => GlobalTheory.Grid.parP D i
    | .top j => GlobalTheory.Grid.parXp D j
  let good : GlobalTheory.ChiGrid.Node → Prop := fun X => match X with
    | .grid i j => 1 ≤ i ∧ i ≤ D.R.m ∧ j ≤ D.R.m
    | .core i => i ≤ D.R.m
    | .top j => 1 ≤ j ∧ j ≤ D.R.m
  have hgood : ∀ X, good X → X.InRange D.R.m ∧ ∀ j, X ≠ .grid 0 j := by
    intro X hX
    rcases X with ⟨i, j⟩ | i | j
    · exact ⟨⟨hX.2.1, hX.2.2⟩, fun j' h => by cases h; exact absurd hX.1 (by omega)⟩
    · exact ⟨hX, fun j' h => GlobalTheory.ChiGrid.Node.noConfusion h⟩
    · exact ⟨hX.2, fun j' h => GlobalTheory.ChiGrid.Node.noConfusion h⟩
  have hMod : ∀ X, good X → ∃ M : DSModel (G'.V X) (Sx X), cart M = W.cart X ∧ onb M = W.onb X := by
    intro X hX
    have hv := G'.isV (hgood X hX).1 (hgood X hX).2
    refine GlobalTheory.T.exists_discreteSeriesModel_of_orthonormalBasis_cartan D hDS (G'.V X) (Sx X) (W.onb X) (W.cart X) ?_ (W.onb_is X (hgood X hX).1)
    intro τ
    rcases X with ⟨i, j⟩ | i | j
    · obtain ⟨lam, ε, h1, h2⟩ := hOV i j hX.1 hX.2.1 hX.2.2 τ
      exact ⟨lam, ε, h1, GlobalTheory.T.isHarishChandraParam_gridVertexRealParameter D hH i j hX.1 hX.2.1 hX.2.2 τ _ lam ε hv.rank h1, h2⟩
    · obtain ⟨lam, ε, h1, h2⟩ := hOP i hX τ
      exact ⟨lam, ε, h1, GlobalTheory.T.isHarishChandraParam_gridColumnRealParameter D hH i hX τ _ lam ε hv.rank h1, h2⟩
    · obtain ⟨lam, ε, h1, h2⟩ := hOX j hX.1 hX.2 τ
      exact ⟨lam, ε, h1, GlobalTheory.T.isHarishChandraParam_gridRowRealParameter D hH j hX.1 hX.2 τ _ lam ε hv.rank h1, h2⟩
  have hFr : ∀ X, good X → ∃ β, IsSDFrame (G'.V X) β (G'.Λ X) 1 := fun X hX =>
    GlobalTheory.T.exists_selfDual_frame_of_standard_selfDual_lattice D _ _ (hL X (hgood X hX).1 (hgood X hX).2) (G'.isV (hgood X hX).1 (hgood X hX).2).sd
  choose M hM using hMod
  choose β hβ using hFr
  let mk : ∀ X, good X → GlobalTheory.Grid.Node D := fun X h => ⟨G'.V X, Sx X, M X h, G'.Λ X, β X h⟩
  let node : GlobalTheory.ChiGrid.Node → GlobalTheory.Grid.Node D := fun X => if h : good X then mk X h else GlobalTheory.Grid.row0 R 0
  have node_pos : ∀ X (h : good X), node X = mk X h := fun X h => dif_pos h
  have mk_is : ∀ X (h : good X), (mk X h).Is (X.rank D) (X.neg D.R.m) (Sx X) := fun X h => by
    have hv := G'.isV (hgood X h).1 (hgood X h).2
    exact ⟨hv.rank, hv.sigOK, hv.sig, rfl, hβ X h⟩
  have mk_agree : ∀ X (h : good X), NodeAgree (mk X h) W X := fun X h =>
    ⟨rfl, HEq.rfl, heq_of_eq (hM X h).1, heq_of_eq (hM X h).2⟩
  let GS : GlobalTheory.Grid.GridSp D :=
    { toPlaceDat := Z, nV := fun i j => node (.grid (i + 1) j), P := fun i => node (.core i), nX := fun j => node (.top (j + 1)) }
  have vert_eq : ∀ n x, 1 ≤ n → GS.vert R n x = node (.grid n x) := by
    intro n x hn
    cases n with
    | zero => omega
    | succ n => rfl
  have Xp_eq : ∀ n, 1 ≤ n → GS.Xp n = node (.top n) := by
    intro n hn
    cases n with
    | zero => omega
    | succ n => rfl
  have gP : ∀ i, i ≤ D.R.m → good (.core i) := fun i h => h
  have gV : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → good (.grid i j) := fun i j h1 h2 h3 => ⟨h1, h2, h3⟩
  have gX : ∀ j, 1 ≤ j → j ≤ D.R.m → good (.top j) := fun j h1 h2 => ⟨h1, h2⟩
  have hm2 := D.R.two_le_m

  obtain ⟨dP, -, hdP⟩ := GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq (GlobalTheory.Grid.row0 R 0) (mk (.core 0) (gP 0 (by omega))) G'.sp.dec0 (fun _ => 1) (Or.inl rfl)
    G'.sp.lat0

  have exV : ∀ i (h : 1 ≤ i ∧ i ≤ D.R.m), ∃ d : GlobalTheory.Grid.HermitianOrthogonalExtensionData (mk (.core i) (gP i h.2)) (mk (.grid i 0) (gV i 0 h.1 h.2 (by omega))) (i - 1),
      d.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix (i - 1) (-1 : D.host.E) p q) (GlobalTheory.ChiGrid.stairId (G'.pl.stA sc) (G'.pl.stAbar sc) (i - 1)) :=
    fun i h => (GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq _ _ (G'.sp.colDec i h.1 h.2) _ (Or.inr rfl) (G'.sp.colLat i h.1 h.2)).imp fun _ h => h.2
  choose dV hdV using exV

  have exX : ∀ j (h : j + 1 < D.R.m), ∃ d : GlobalTheory.Grid.HermitianOrthogonalExtensionData (mk (.top (j + 1)) (gX (j + 1) (by omega) h.le))
      (mk (.grid D.R.m (j + 1)) (gV D.R.m (j + 1) (by omega) le_rfl h.le)) (D.R.m - 1 - (j + 1)),
      d.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix (D.R.m - 1 - (j + 1)) (-1 : D.host.E) p q)
        (GlobalTheory.ChiGrid.stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1))) :=
    fun j h => (GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq _ _ (G'.sp.rowDecS j h) _ (Or.inr rfl) (G'.sp.rowLat j h)).imp fun _ h => h.2
  choose dX hdX using exX

  obtain ⟨dZ, -, hdZ⟩ := GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq (mk (.grid D.R.m D.R.m) (gV D.R.m D.R.m (by omega) le_rfl le_rfl))
    (mk (.top D.R.m) (gX D.R.m (by omega) le_rfl)) G'.sp.topDec (fun _ => 1) (Or.inl rfl) G'.sp.topLat
  let G : GlobalTheory.Grid.GridPre R :=
    { toGridSp := GS
      idem := e
      chiH := G'.ch.chiH
      chi := G'.ch.chi
      decP := hermitianOrthogonalExtensionDataCast rfl (node_pos (.core 0) (gP 0 (by omega))).symm dP
      decV := fun i => if h : 1 ≤ i ∧ i ≤ D.R.m then
        hermitianOrthogonalExtensionDataCast (node_pos (.core i) (gP i h.2)).symm ((vert_eq i 0 h.1).trans (node_pos (.grid i 0) (gV i 0 h.1 h.2 (by omega)))).symm (dV i h) else hermitianOrthogonalExtensionDataZero _ _ _
      decX := fun j => if h : j + 1 < D.R.m then
        hermitianOrthogonalExtensionDataCast (node_pos (.top (j + 1)) (gX (j + 1) (by omega) h.le)).symm ((vert_eq D.R.m (j + 1) (by omega)).trans (node_pos (.grid D.R.m (j + 1)) (gV D.R.m (j + 1) (by omega) le_rfl h.le))).symm (dX j h) else hermitianOrthogonalExtensionDataZero _ _ _
      decZ := hermitianOrthogonalExtensionDataCast ((vert_eq D.R.m D.R.m (by omega)).trans (node_pos (.grid D.R.m D.R.m) (gV D.R.m D.R.m (by omega) le_rfl le_rfl))).symm
        ((Xp_eq D.R.m (by omega)).trans (node_pos (.top D.R.m) (gX D.R.m (by omega) le_rfl))).symm dZ
      X := fun _ _ => ⟨1, 0, 0⟩
      ωT := fun _ _ _ => 1
      vacT := fun _ _ => 0
      ItT := fun _ _ => 0
      ωC := fun _ _ => 1
      vacC := fun _ => 0
      ItC := fun _ => 0
      dn := fun _ => ⟨1, 0, 0⟩
      ItU := fun _ => 0
      m00 := ⟨0, ∅⟩
      mV := fun _ _ => ⟨0, ∅⟩
      mP := fun _ => ⟨0, ∅⟩
      mX := fun _ => ⟨0, ∅⟩
      vC := fun _ _ => 0 }
  refine ⟨G, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hi hj
      show (node (.grid (i + 1) j)).Is _ _ _
      rw [node_pos (.grid (i + 1) j) (gV (i + 1) j (by omega) hi hj)]
      exact mk_is _ _
    · intro i hi
      show (node (.core i)).Is _ _ _
      rw [node_pos (.core i) (gP i hi)]
      exact mk_is _ _
    · intro j hj
      show (node (.top (j + 1))).Is _ _ _
      rw [node_pos (.top (j + 1)) (gX (j + 1) (by omega) hj)]
      exact mk_is _ _
    · dsimp only [G]
      rw [gridDecompositionCast_is_iff, ← joinGram_one]
      exact hdP
    · intro i hi1 hi2
      dsimp only [G]
      rw [dif_pos ⟨hi1, hi2⟩, gridDecompositionCast_is_iff]
      have hl' : Z.ideal R.Pg = G'.pl.modul sc := hlvl
      have := hdV i ⟨hi1, hi2⟩
      rw [joinGram_neg, joinStair, ← hl'] at this
      exact this
    · intro j hj
      dsimp only [G]
      rw [dif_pos hj, gridDecompositionCast_is_iff]
      have := hdX j hj
      rw [joinGram_neg, joinStair_top] at this
      exact this
    · dsimp only [G]
      rw [gridDecompositionCast_is_iff, ← joinGram_one]
      exact hdZ
  · exact ⟨hZ, fun i h1 h2 => GlobalTheory.T.heckeCharacterGrid_isAuxiliaryCharacter_testGrid (GlobalTheory.T.gridMinimalGap_eq_chiGridGapGamma_one D) hsc Z hS0 hS1 hZ.Wd_over hw0 i h1 h2, fun i h1 h2 => G'.ch.chi_eq i h1 h2⟩
  · refine ⟨?_, ?_, ?_, hq0, hw0, he0, hWZ, hlvl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    · intro i j hi hj
      cases i with
      | zero => exact GlobalTheory.T.testGridRowZero_vertices_agree_weilData W hW j hj
      | succ i =>
        show NodeAgree (node (.grid (i + 1) j)) W (.grid (i + 1) j)
        rw [node_pos (.grid (i + 1) j) (gV (i + 1) j (by omega) hi hj)]
        exact mk_agree _ _
    · intro i hi
      show NodeAgree (node (.core i)) W (.core i)
      rw [node_pos (.core i) (gP i hi)]
      exact mk_agree _ _
    · intro j hj
      cases j with
      | zero =>
        show NodeAgree (node (.core D.R.m)) W (.top 0)
        rw [node_pos (.core D.R.m) (gP D.R.m le_rfl)]
        exact ⟨rfl, HEq.rfl, heq_of_eq ((hM _ _).1.trans hcT.symm), heq_of_eq ((hM _ _).2.trans hoT.symm)⟩
      | succ j =>
        show NodeAgree (node (.top (j + 1))) W (.top (j + 1))
        rw [node_pos (.top (j + 1)) (gX (j + 1) (by omega) hj)]
        exact mk_agree _ _

end GlobalTheory.GridJoin
