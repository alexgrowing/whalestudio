import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)

theorem cond_powers {D : D7} {C : NChoice D} {I : TwIn D} (h : DQ.GoodAllAt D C I) :
    (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (C.twI w) (C.Q w)) ∧
    ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (C.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (C.twI w) (C.Q w) (C.k' w) (C.psi' w ^ a) (twEps D (C.twI w)) := by
  classical
  refine ⟨fun w hw => ?_, I.N0, fun w hw a ha => ?_⟩
  · have h1 := ((h w hw).2 1 (by simp)).1
    exact ⟨fun P hP => (h1.1 P hP).1, (Finset.disjoint_union_right.1 h1.2.1).1,
      GlobalTheory.AntiRam.ramExactly_conj D _ _ _ h1.2.2.2.2.1 h1.2.2.2.2.2.2.1⟩
  · have e : ∃ b : ℤ, b.natAbs = a.natAbs ∧ BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w ^ b) = C.psi' w ^ a := by
      cases C.sd w
      · exact ⟨-a, Int.natAbs_neg a, by simp [BlochKatoReduction.Gen.psiAt]⟩
      · exact ⟨a, rfl, by simp [BlochKatoReduction.Gen.psiAt]⟩
    obtain ⟨b, hb, e⟩ := e
    have hc : Nat.Coprime b.natAbs (D.ntw.l (C.twI w)) := by
      rw [hb]
      simpa using Int.isCoprime_iff_nat_coprime.1 ha
    exact e ▸ ((h w hw).2 b hc).2.2.2.2.1

theorem twI_eq {D : D7} {C : NChoice D} {xd : ThData D} (h : GoodO D C xd) {w w' : D.what₂.places.Pl}
    (hw : Twisted D w) (hw' : Twisted D w') (e : C.Q w = C.Q w') (hne : C.Q w ≠ ∅) : C.twI w = C.twI w' := by
  by_contra hn
  have := h.sep w w' hw hw' hn
  rw [← e] at this
  exact hne (disjoint_self.1 this)

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

theorem Q_eq (q : WPt p.s K) {w w' : (q.w.D q.Z).what₂.places.Pl} (hw : Twisted (q.w.D q.Z) w)
    (hw' : Twisted (q.w.D q.Z) w') (h : SamePair (q.w.D q.Z) w w') :
    q.O.ex.nch.Q w = q.O.ex.nch.Q w' ∧ q.O.ex.nch.k' w = q.O.ex.nch.k' w' := by
  have key : ∀ v v', Twisted (q.w.D q.Z) v → Twisted (q.w.D q.Z) v' → SameBelow (q.w.D q.Z) v v' →
      q.O.ex.nch.Q v = q.O.ex.nch.Q v' ∧ q.O.ex.nch.k' v = q.O.ex.nch.k' v' := by
    intro v v' hv hv' hs
    have m : ∀ u, Twisted (q.w.D q.Z) u → u ∈ q.x.Wt := fun u hu => by
      by_contra hn
      exact hu (q.x.what₂.mu.off u hn)
    have a := q.x.n.Q v (m v hv)
    have a' := q.x.n.Q v' (m v' hv')
    have c := q.x.coh.same v v' fun x hx => hs ⟨x, hx⟩
    exact ⟨a.1.trans (c.1.trans a'.1.symm), a.2.trans (c.2.1.trans a'.2.symm)⟩
  rcases h with h | h
  · exact key w w' hw hw' h
  · have k := key _ w' ((GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw) hw' h
    have c := q.core.a.all.choice.conj w hw
    exact ⟨(congrArg (fun t : TwPack _ => t.2.1) c).symm.trans k.1, (congrArg (fun t : TwPack _ => t.2.2.1) c).symm.trans k.2⟩

theorem twists_at_linked : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) (Q : V4.Slot), RowE Q (IsLinked p) fun _ D O _ _ => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w)) := by
  intro hL p Q
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', -, he⟩ := hl
  have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c =>
    (fun (D : D7) (O : Obj D) => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w))) s.1 s.2.1) he
  refine cast h1.symm ?_
  obtain ⟨I, -, hI, -⟩ := q.x.good.tw
  exact ⟨fun w hw => ⟨q.O.ex.nch.twI_l w, GlobalTheory.TwistGoodCompare.atPlace_of_tie q.B.coeffGaloisSubfield_isGalois q.O.ex.nch_tie w hw⟩,
    fun w w' hw hw' h => ⟨(Q_eq q hw hw' h).1, (Q_eq q hw hw' h).2, twI_eq q.x.good hw hw' (Q_eq q hw hw' h).1⟩, cond_powers hI⟩

end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

end
