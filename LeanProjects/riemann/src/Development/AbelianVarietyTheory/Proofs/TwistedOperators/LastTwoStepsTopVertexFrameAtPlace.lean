import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastBiExpand
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsModelChg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem pr_eq_algebraMap_of_isPlc {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) :
    (p.pr : D.host.E → Kw w) = algebraMap D.host.E (Kw w) := funext fun a => by
  show p.π (incA D a) = _
  rw [hp.2.1]
  exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z w) (GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) a)

theorem topVertexFrame_renumbered_cast (ch : Choice R) (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (n : ℕ) (hn : D.R.m = n) (hle : n ≤ D.R.m) :
    ∃ e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) n),
      (∀ i, (e (Sum.inl i)).val = i.val) ∧ (e (Sum.inr ())).val = topRank (locGrid ch.G t w) n - 1 ∧
      ∃ FX : Frame (Kw w) (ch.G.V (.top n)).rank (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit),
        FX.β = fromCols ((topOrthAt ch.G hn).iA.map p.pr * (frRow ch.S.B t w D.R.m le_rfl).β)
          (Matrix.of fun r _ => ((topOrthAt ch.G hn).iB.map p.pr *ᵥ fun _ => (1 : Kw w)) r) ∧
        ∀ r z, FX.β r z = (frTop ch.S.toGridChoice t w n hle).β r (e z) := by
  subst hn
  have hL := ch.S.last t (Set.mem_univ t) w hw
  unfold IsSumFrame at hL
  rw [pr_eq_algebraMap_of_isPlc hp]
  set d := ch.G.sp.topDec with hd
  have h1 : (locGrid ch.G t w).rank (D.R.m, D.R.m) = (ch.G.V (.grid D.R.m D.R.m)).rank :=
    rank_vertex ch.G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩
  have h2 : topRank (locGrid ch.G t w) D.R.m = (ch.G.V (.top D.R.m)).rank := topRank_eq ch.G t w hle
  have h3 : (ch.G.V (.grid D.R.m D.R.m)).rank + 1 = (ch.G.V (.top D.R.m)).rank := d.rank
  let e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) D.R.m) :=
    ((Equiv.sumCongr (finCongr h1) (⟨fun _ => 0, fun _ => (), fun _ => rfl, fun x => Subsingleton.elim _ _⟩ : Unit ≃ Fin 1)).trans (frame h3)).trans (finCongr h2.symm)
  refine ⟨e, fun i => rfl, ?_, ?_⟩
  · simp [e, frame]
    omega
  let F := frTop ch.S.toGridChoice t w D.R.m hle
  refine ⟨⟨F.β.submatrix id e, F.γ.submatrix e id, ?_, ?_⟩, ?_, fun r z => rfl⟩
  · rw [submatrix_mul_equiv, submatrix_id_id, F.βγ]
  · rw [← submatrix_mul _ _ _ id _ Function.bijective_id, F.γβ, submatrix_one_equiv]
  · refine Matrix.ext fun r z => ?_
    rcases z with i | u
    · have := congrFun (congrFun hL r) (Sum.inl (Fin.cast h1 i))
      refine Eq.trans ?_ (this.trans ?_)
      · rfl
      · simp only [fromCols_apply_inl]
        rfl
    · have := congrFun (congrFun hL r) (Sum.inr 0)
      refine Eq.trans ?_ (this.trans ?_)
      · rfl
      · simp only [fromCols_apply_inr, of_apply, Matrix.mul_diagonal, Matrix.map_apply, mul_one]
        rw [Pi.one_apply, mul_one]
        symm
        show ∑ k : Fin 1, (_ : Kw w) = _
        rw [Fin.sum_univ_one]
        exact mul_one _

theorem frame_top_last : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (j : ℕ) (hj : j + 2 = D.R.m),
    ∃ e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) (j + 1 + 1)),
      (∀ i, (e (Sum.inl i)).val = i.val) ∧ (e (Sum.inr ())).val = topRank (locGrid ch.G t w) (j + 1 + 1) - 1 ∧
      ∃ FX : Frame (Kw w) (ch.G.V (.top (j + 1 + 1))).rank (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit),
        FX.β = fromCols ((topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)).iA.map p.pr * (frRow ch.S.B t w D.R.m le_rfl).β)
          (Matrix.of fun r _ => ((topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)).iB.map p.pr *ᵥ fun _ => (1 : Kw w)) r) ∧
        ∀ r z, FX.β r z = (frTop ch.S.toGridChoice t w (j + 1 + 1) (by omega)).β r (e z) :=
  fun ch t w hw p hp j _ => topVertexFrame_renumbered_cast ch t w hw p hp (j + 1 + 1) (by omega) (by omega)

end GlobalTheory.FlatPlace
