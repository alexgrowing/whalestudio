import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.LastRowVac

open GlobalTheory.LastVertexMove GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem eq_smul_vac (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (S.N.latS p : Set _) (S.N.latT p : Set _) f) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ f = c • S.Z.vac p := by
  have hv := S.Z.vac_is p hp
  obtain ⟨h1, h2⟩ := hp.nodes
  rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
  · exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _
      (GlobalTheory.ChiGrid.WeilOver.sigOK_negSp (h2.sigOK G)) (h1.sigOK G)
      (fun τ => isCartanInv_neg (W.cart_is _ h2.inRange τ)) (fun τ => W.cart_is _ h1.inRange τ) _ _
      (isSelfDualC_neg (S.N.selfDual h2)) (S.N.selfDual h1) _ _ hv hf
  · exact hp.elim
  · exact hp.elim
  · exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ (h1.sigOK G) (h2.sigOK G)
      (fun τ => W.cart_is _ h1.inRange τ) (fun τ => W.cart_is _ h2.inRange τ) _ _ (S.N.selfDual h1) (S.N.selfDual h2)
      _ _ hv hf

theorem negGA_mem (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem rowPt_mem (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    (rowPt S k).1 ∈ GfC _ ∧ (rowPt S k).2 ∈ GfC _ :=
  ⟨negGA_mem _ (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).2, one_mem _⟩

theorem vac_row_scalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)),
    (∀ x, actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔
      x ∈ stdLat S (.chi (lastIx D) D.R.m)) →
    ∃ c : ℂ, rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = c • S.Z.vac (.chi (lastIx D) D.R.m) := by
  intro D T L sc G W U S k hlat
  have hp : DefPair D.R.m (Pair.chi ((lastIx D : ℕ)) D.R.m : Pair T) := defPair_chi (lastIx D)
  have hom := W.om_is _ (inRange_chi (T := T) (lastIx D))
  obtain ⟨m1, m2⟩ := rowPt_mem S k
  have hΛ : ∀ u, u ∈ stdLat S (.chi (lastIx D) D.R.m) ↔
      ∃ u₀ ∈ stdLat S (.chi (lastIx D) D.R.m), u = actO _ _ (rowPt S k).1 (rowPt S k).2 u₀ := by
    intro u
    constructor
    · intro hu
      refine ⟨actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ u, (hlat u).2 hu, ?_⟩
      have e := GlobalTheory.WeilVacMove.actO_inv_actO (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ u
      rw [inv_inv, inv_inv] at e
      exact e.symm
    · rintro ⟨u₀, hu₀, rfl⟩
      refine (hlat _).1 ?_
      rw [GlobalTheory.WeilVacMove.actO_inv_actO]
      exact hu₀
  have hv' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ _ _ _ _ _ (rowPt S k).1 (rowPt S k).2
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m2, Matrix.mul_one, Matrix.one_mul])
    hΛ _ (S.Z.vac_is _ hp)
  obtain ⟨c, -, hc⟩ := eq_smul_vac S hp _ hv'
  exact ⟨c, by rw [rowShift_eq]; exact hc⟩

end GlobalTheory.LastRowVac

end
