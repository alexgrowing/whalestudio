import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefPerEqGenPer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefOfNode
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenConvProof

variable {D : D7}

theorem invCont_cast {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hc : Continuous φ) (hl : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    Continuous (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
        φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact ⟨hc, hl⟩

theorem genPer_conv : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t a, ch.S.SumOK t (ch.Phi a) →
    ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M →
      ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y Q ξ η, GenConv ch t a M d y Q ξ η := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro t a hOK β hβ M hM τ hτ d hd y Q ξ η
  have hL := s.core.lev
  have hm := s.core.models
  have hcol : GlobalTheory.DefConv.IsInvCont (.top 0) (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) :=
    ⟨GlobalTheory.RowBplus.pairVec_cont ch.G ch.W.θ ch.W.θ_is ξ (col_mem ch a),
      fun γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g⟩
  have hx := (hm.HX t).2.1.le (LinearMap.mem_range_self (R.HX t).e y)
  have hform : GlobalTheory.DefConv.IsInvCont (.grid 0 D.R.m) (formGen ch t y η) := by
    have k := invCont_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
      ((LinearMap.continuous_of_finiteDimensional η).comp
        (GlobalTheory.ThetaIntegrand.ext_continuous R.cX hm.cX R.βX (R.datXt t) hx))
      (fun γ hγ g => by simp only [GlobalTheory.ThetaIntegrand.ext_invariant R.cX hx γ hγ g])
    exact ⟨k.1, k.2⟩
  have hv := hOK.vec β τ hτ d hd
  have hcG : Path.Fam.All (fun a f => GlobalTheory.DefConv.Good ch.W M a f)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j)) :=
    GlobalTheory.DefConv.all_colFam t _ _ fun j => GlobalTheory.DefConv.good_col ch.W M j.2 _
      (GlobalTheory.DefConv.theta_fock ch.W ch.S.toGridChoice (p := .top t j) (by show (j : ℕ) + 1 ≤ D.R.m; omega)
        (by show (j : ℕ) + 1 ≤ D.R.m; omega) (d.1 j) (hv.1 j) (Q.1 j))
      (GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .top j) (show (j : ℕ) ≤ D.R.m by omega) rfl) (hM.1 j j.2)
  have hrG : Path.Fam.All (fun a f => GlobalTheory.DefConv.Good ch.W M a f)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) :=
    GlobalTheory.DefConv.all_rowFam D.R.m _ _ fun i => GlobalTheory.DefConv.good_row ch.W M i.2 _
      (GlobalTheory.DefConv.theta_fock ch.W ch.S.toGridChoice (p := .chi i D.R.m)
        (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨by omega, rfl⟩)
        (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) (d.2 i) (hv.2 i) (Q.2 i))
      (GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .grid i D.R.m) ⟨by omega, le_rfl⟩ (by simp [Node.neg]))
      (hM.2 i (by omega))
  obtain ⟨hc1, hc2⟩ := GlobalTheory.DefConv.path ch.W M hcol _ _ hcG
  obtain ⟨hr1, hr2⟩ := GlobalTheory.DefConv.path ch.W M hform _ _ hrG
  refine ⟨hc1, hr1, ?_⟩
  obtain ⟨hac, hamul, haQ⟩ := GlobalTheory.T.unitaryEmbedding_continuous_mul_rational ch.G.sp.topDec
  have hpos := GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by simp [Node.neg])
  obtain ⟨Cc, hCc, hcov⟩ := GlobalTheory.definite_unitary_cocompact _ hpos
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.grid D.R.m D.R.m))
  obtain ⟨hH, hfd⟩ := (hM.2 D.R.m le_rfl).haar_fund
  refine GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact _ _ _ Cc hfd hCc hcov _
    ((hc2.1.comp hac).mul hr2.1) fun γ hγ g => ?_
  simp only [hamul, hc2.2 _ (haQ γ hγ), hr2.2 γ hγ]

end GlobalTheory.GenConvProof

end
