import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SideTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {y : Hd R} {b : Bool}
  {rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {S : RowSide D EE} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE} {ty : Fin n → D.what₂.FT}
  {jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)}

def ids (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowIds S (y.C F) b where
  jE := (LinearEquiv.ofInjective t.jE t.jE_inj).trans (LinearEquiv.ofEq _ _ t.jE_range)
  jM μ hμ j h1 h2 := (LinearEquiv.ofInjective (t.jM μ j) (t.jM_inj μ ((hU μ).1 hμ) j h1 h2)).trans
    (LinearEquiv.ofEq _ _ (t.jM_range μ ((hU μ).1 hμ) j h1 h2))
  jX μ hμ := (S.multTop μ).toLinearEquiv.trans ((LinearEquiv.ofInjective (t.jX μ) (t.jX_inj μ ((hU μ).1 hμ))).trans
    (LinearEquiv.ofEq _ _ (t.jX_range μ ((hU μ).1 hμ))))
  prt π := y.prtE F b (rep π)

theorem real (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowSideReal S (y.C F) b (ids hU t) bs ty where
  parY j hj := by
    show Mult.parB (Ptw D) (min j D.R.m) = Mult.parB (Ptw D) j
    rw [min_eq_left (by have := y.hm; omega)]
  lvl μ _ := GlobalTheory.HilbertLevels.eec_le_cc R F y.tupT y.hm y.hTop b μ
  lvlP μ _ j _ h2 := GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := y.hm; omega)
  lvlX μ _ := GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ
  ee x x' := t.jE_ip x x'
  mult μ hμ j h1 h2 x x' := t.jM_ip μ ((hU μ).1 hμ) j h1 h2 x x'
  multX _ μ hμ x x' := by
    rw [← (S.multTop μ).inner_map_map x x']
    exact t.jX_ip μ ((hU μ).1 hμ) _ _
  io0 _ μ hμ _ x v := by
    have hmem : t.jM μ 1 v ∈ (y.C F).CC b μ 1 :=
      GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := D.R.two_le_m; omega) ((ids hU t).jM μ hμ 1 le_rfl (by have := D.R.two_le_m; omega) v).2
    have e := t.io0 μ ((hU μ).1 hμ) x v hmem
    refine e.trans ?_
    rfl
  io0X h := absurd h (by have := D.R.two_le_m; omega)
  io μ hμ _ j h1 h2 x v := by
    have hmem : t.jM μ (j + 1) v ∈ (y.C F).CC b μ (j + 1) :=
      GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by omega) ((ids hU t).jM μ hμ (j + 1) (by omega) h2 v).2
    exact (t.io μ ((hU μ).1 hμ) j h1 h2 x v hmem).trans rfl
  ioTop h μ hμ _ x v := by
    have hmem : t.jX μ (S.multTop μ v) ∈ (y.C F).CCX b μ :=
      GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ ((ids hU t).jX μ hμ v).2
    exact (t.ioTop μ ((hU μ).1 hμ) x v _ (cast_heq _ _) hmem).trans rfl
  ft σ := by
    have h := t.ft (ty σ)
    have hs : bs σ ∈ Submodule.span ℂ (bs '' {σ' | ty σ' = ty σ}) := Submodule.subset_span ⟨σ, rfl, rfl⟩
    rw [h] at hs
    exact hs
  prt_disj π π' h := t.disj π π' h

end GlobalTheory.Mem.R3.Rw.SideTie

open GlobalTheory.Mem.R3.Rw.SideTie in

theorem GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y _ _ hU b rep EE _ _ _ S n bs ty jA t
  exact ⟨ids hU t, real hU t, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
