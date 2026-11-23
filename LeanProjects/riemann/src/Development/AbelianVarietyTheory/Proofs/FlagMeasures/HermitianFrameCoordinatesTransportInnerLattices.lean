import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordInnerFst

open CoordInnerSnd

open ValuativeRel in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.CoordInnerFst.transport : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ) (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k)
    (c : _root_.GlobalTheory.HL.Coord P S),
    Function.Injective (c.inn P.A.f) ∧
    (∀ L, P.A.IsInner L ↔ S.IsInner S.f S.es
      (c.inn P.A.f L)) ∧
    (∀ A, S.IsInner S.f S.es A →
      ∃ L, A = c.inn P.A.f L) ∧
    ∀ L, c.lat (P.A.LamStd L) =
      S.stdLat S.f S.es
        (c.inn P.A.f L) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hPID : IsPrincipalIdealRing M.L.O :=
    (_root_.GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.1
  have hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O := fun x hx => _root_.GlobalTheory.UnramOrder.cj_mem M.L hx
  have hT : P.A.T ≠ 0 := by
    rw [← c.T_eq]
    exact Units.ne_zero _
  exact ⟨_root_.GlobalTheory.HL.CoordInnerSnd.inn_inj P.A c,
    fun L => _root_.GlobalTheory.HL.CoordInnerSnd.isInner_iff P.A c S.f S.es hcj hPID hT
      c.f_eq c.es_eq L,
    _root_.GlobalTheory.HL.CoordInnerSnd.inn_surj P.A c S.f S.es
      c.f_eq,
    _root_.GlobalTheory.HL.CoordInnerSnd.lat_lamStd P.A c S.f S.es
      c.f_eq c.es_eq⟩

end GlobalTheory.HL.CoordInnerFst
