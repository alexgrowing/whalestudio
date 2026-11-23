import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.SymRes

theorem exists_red_iff_isPat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {O : Type} [CommRing O] (I : Ideal O) (π : O →+* k) (h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk I) π)
    {s κ r : ℕ} (hr : r = κ + (s + 1)) (S : GlobalTheory.SymChain.SymData k s κ) (g : GL (Fin r) (O ⧸ I)) :
    (∃ x : S.P.J, ∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
      b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O, Ideal.Quotient.mk I z = g.val a' b' →
      valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - π z) < 1) ↔ IsPat S.ρ κ g := by
  subst hr
  let e : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have he : ∀ a, (e a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
    rintro (a | a) <;> simp [e, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  have hfree : ∀ a b, FreePos S.ρ κ (e a).val (e b).val ↔ GlobalTheory.SymChain.FreeTop S.ρ a b := by
    intro a b
    rw [he, he]
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl, Sum.elim_inr, GlobalTheory.SymChain.FreeTop, FreePos, Fin.lt_def] <;>
      have := a.2 <;> have := b.2 <;> omega
  choose l hl using fun a b => Ideal.Quotient.mk_surjective (I := I) (g.val (e a) (e b))
  have key : ∀ a b, g.val (e a) (e b) = (1 : Matrix _ _ (O ⧸ I)) (e a) (e b) ↔
      valuation k (π (l a b) - (1 : Matrix _ _ k) a b) < 1 := by
    intro a b
    have h4 := h.ker (l a b - if a = b then 1 else 0)
    rw [map_sub, map_sub, sub_eq_zero, apply_ite (Ideal.Quotient.mk I), apply_ite π, map_one, map_one, map_zero,
      map_zero, hl] at h4
    rw [Matrix.one_apply, Matrix.one_apply]
    simp only [e.apply_eq_iff_eq]
    convert h4
  constructor
  · rintro ⟨x, hx⟩ i j hij
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    have h1 := hx a b _ _ (he a) (he b) _ (hl a b)
    have h2 := ((GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x.1).1 x.2).2 a b (fun h' => hij ((hfree a b).2 h'))
    have h3 := (valuation k).map_sub_lt h2 h1
    rw [sub_sub_sub_cancel_left] at h3
    exact (key a b).2 h3
  · intro hg
    have hM : (Matrix.of l).map (Ideal.Quotient.mk I) = g.val.submatrix e e := Matrix.ext hl
    have hu : IsUnit ((Matrix.of l).map (Ideal.Quotient.mk I)).det := by
      rw [hM, det_submatrix_equiv_self]
      convert (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    obtain ⟨x, hx1, hx2⟩ := (h.isUnit_det_iff _).1 hu
    have hx3 : ∀ a b, x.val a b = π (l a b) := fun a b => congrFun (congrFun hx2 a) b
    refine ⟨⟨x, (GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x).2 ⟨by convert hx1, fun a b hab => ?_⟩⟩, ?_⟩
    · rw [hx3]
      exact (key a b).1 (hg _ _ fun h' => hab ((hfree a b).1 h'))
    · intro a b a' b' ha hb z hz
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      change valuation k (x.val a b - π z) < 1
      rw [hx3, ← map_sub, ← h.ker, map_sub, hl, hz, sub_self]

theorem exists_red_iff : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)), (∃ x, G.Red x g) ↔ GlobalTheory.SymRes.IsPat D.R.rS D.R.k g := by
  intro D u d τ PP G g
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP G.idem
  have hr : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hρ : D.R.rS = G.S.ρ := by
    have := G.hs
    have := G.S.odd
    unfold Ranks.rS
    omega
  let π : 𝓞 D.host.E →+* G.k :=
    (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).comp (oToS D.host.F D.host.E)
  have hπ : ∀ z : 𝓞 D.host.E, π z = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := fun z =>
    h1 (incA D (z : D.host.E))
  have h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk PP.asIdeal) π :=
    ⟨h2.field, fun z => h2.int _, fun z => (iff_of_eq (congrArg (· = 0) (resS_oToS (F := D.host.F) PP z).symm)).trans (h2.ker _)⟩
  have := exists_red_iff_isPat PP.asIdeal π h hr G.S g
  simp only [hπ] at this
  rw [hρ]
  exact this

end GlobalTheory.SymRes
