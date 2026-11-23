import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompactRealPointFockVectorSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainTopPairMovedVectorRowCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainChiPairMovedVectorColumnCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSubstitutionRowStepRenameUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSubstitutionColumnStepRenameConjStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorDefinitePairThetaFockVacuumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteNodeCartanOrthonormalBasisAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainTopRowRealPointInOrthonormalBasisStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem om_fock_chi {μ0 : T} (hL : L.Is μ0) (W : G.Weil) {U : Set T} (S : GridChoice W U)
    (g : Gc D.what₂.Tau (rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)) (hd : S.Z.HasVec d)
    (Q Q' : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (hQ : trRow G i Q' = colFock (rowEntries D sc.cGap) i g (trRow G i Q)) :
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)))
        (W.fock (.chi i D.R.m) (movedVec t S d) Q) =
      W.fock (.chi i D.R.m) (movedVec t S d) Q' := by
  have hX : DefNode D.R.m (.grid (i : ℕ) D.R.m) := ⟨i.2.le, rfl⟩
  have hY : DefNode D.R.m (.grid ((i : ℕ) + 1) D.R.m) := ⟨i.2, rfl⟩
  have hp : DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) := ⟨i.2, rfl⟩
  obtain ⟨hf, hv⟩ := GlobalTheory.T.movedVector_definitePair_theta_fockVacuum W S t (.chi i D.R.m) hp d hd
  have hc := GlobalTheory.T.compactChain_chiPair_movedVector_columnCharacter hL W S g t i d hd
  let u : UG D.what₂.Tau ((rowSizes D).nC (i : ℕ)) := g.2 ⟨(i : ℕ), Nat.lt_succ_of_lt i.2⟩
  let v : UG D.what₂.Tau ((rowSizes D).nC ((i : ℕ) + 1)) := g.2 ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.2⟩
  have c1 : ∀ τ, compAt W.θ τ (mt (G.V (.grid ((i : ℕ) + 1) D.R.m)) (ptGrid W g ((i : ℕ) + 1))) =
      W.onb (.grid ((i : ℕ) + 1) D.R.m) τ * (v τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) *
        (W.onb (.grid ((i : ℕ) + 1) D.R.m) τ)⁻¹ := fun τ => by
    rw [ptGrid_le W g (Nat.succ_lt_succ i.2)]
    exact compAt_kappa_snd g ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.2⟩ (posOnb_of_defNode W μ0 hL hY) τ
  have c1' : ∀ τ, compAt W.θ τ (mt (negSp (G.V (.grid ((i : ℕ) + 1) D.R.m)))
      (negGA (G.V (.grid ((i : ℕ) + 1) D.R.m)) (ptGrid W g ((i : ℕ) + 1)))) =
      W.onb (.grid ((i : ℕ) + 1) D.R.m) τ * (v τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) *
        (W.onb (.grid ((i : ℕ) + 1) D.R.m) τ)⁻¹ := fun τ => by
    rw [mt_negGA]; exact c1 τ
  have c2 : ∀ τ, compAt W.θ τ (mt (G.V (.grid (i : ℕ) D.R.m)) (ptGrid W g i)) =
      W.onb (.grid (i : ℕ) D.R.m) τ * (u τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) *
        (W.onb (.grid (i : ℕ) D.R.m) τ)⁻¹ := fun τ => by
    rw [ptGrid_le W g (Nat.lt_succ_of_lt i.2)]
    exact compAt_kappa_snd g ⟨(i : ℕ), Nat.lt_succ_of_lt i.2⟩ (posOnb_of_defNode W μ0 hL hX) τ
  have key := GlobalTheory.T.weil_compactRealPoint_fockVector_substitution W (.chi i D.R.m) ⟨i.2, le_rfl⟩ (fun _ => 0) (fun _ => (G.V (.grid (i : ℕ) D.R.m)).rank)
    (fun _ => Nat.zero_le _) (fun _ => le_rfl) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.2.1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).1)
    (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.2.2) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).2.1) _ hf hv
    (fun τ => (v τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)))
    (fun τ => (u τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)))
    (fun ρ => isKMat_cast _ _ (Or.inr rfl)) (fun ρ => isKMat_cast _ _ (Or.inl rfl))
    (negGA _ (ptGrid W g ((i : ℕ) + 1))) (ptGrid W g i) (GlobalTheory.FockReal.negGA_mem_GinfC _ (ptGrid_mem W g _)) (ptGrid_mem W g _)
    c1' c2 _ hc Q
  have hQ' : Q' = colScal (rowEntries D sc.cGap) i g • fockSubAll (fun _ => 0)
      (fun _ => (G.V (.grid (i : ℕ) D.R.m)).rank)
      (fun τ => (v τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)))
      (fun τ => (u τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)))
      Q := by
    apply trRow_injective G i
    rw [hQ, map_smul, GlobalTheory.T.fockSubstitution_columnStep_rename_conj G i u v Q]
    rfl
  exact key.trans (by rw [hQ', LinearMap.map_smul])

end GlobalTheory.RowReal
