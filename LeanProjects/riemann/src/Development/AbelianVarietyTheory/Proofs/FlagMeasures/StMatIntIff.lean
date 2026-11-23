import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StMatSpec
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOneEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCommonStabiliserUnitriangularCoordsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserIffRationalCoordsStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StIntLat

theorem stMat_int_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ y : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ, (∃ x ∈ G.K0, y = fun v p => Formalism.L2.SG.Pf.VolPinAsm.phiV X v (GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2)) ↔ ∀ p : Formalism.L2.SG.RealObj.FreeE w, (fun v => y v p) ∈ ((((ddS D ^ (-(((p.1.2.val - p.1.1.val : ℕ)) : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup).map (Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) 1)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c y
  have hT : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u').ne'
  have hli : LinearIndependent D.host.E G.f' := by
    have h0 : LinearIndependent D.host.E (frame F'0) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F'0.fl hT
    have h1 := h0.map' (c.e : (VS D).V →ₗ[D.host.E] G.V) c.e.ker
    have e : G.f' = (c.e : (VS D).V →ₗ[D.host.E] G.V) ∘ frame F'0 := by
      funext a; exact c.f'_eq a
    rw [e]; exact h1
  have hStCo := GlobalTheory.T.rationalCommonStabiliser_unitriangular_coords D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hK := GlobalTheory.T.integralStabiliser_iff_rational_coords D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hexp : ∀ a b : Fin (D.R.rS + 1), a < b →
      (-(((b.val - a.val : ℕ)) : ℤ)) = -((b : ℤ) - (a : ℤ)) := by
    intro a b hab
    have : a.val ≤ b.val := le_of_lt hab
    rw [Nat.cast_sub this]
  constructor
  · rintro ⟨x, hx, rfl⟩ p
    have hxSt : x ∈ G.St := by
      intro q
      obtain ⟨g', hg', he⟩ := hx q
      exact ⟨g', hg'.1.1, he⟩
    obtain ⟨B, -, hB, -⟩ := hStCo.1 x hxSt
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hB⟩
    have hmem := (hK x hxSt _ hspec).1 hx p.1.1 p.1.2 p.2.1
    refine ⟨GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2, ?_, ?_⟩
    · rw [hexp _ _ p.2.1]; exact hmem
    · funext v; simp [Formalism.L2.SG.NGCut.SplitEmbedding.embS]
  · intro h
    choose lam hlam hlamE using h
    let B : Formalism.L2.SG.PairVal.MatR D := fun a b =>
      if a = b then 1 else if hab : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
        then lam ⟨(a, b), hab⟩ else 0
    have hBU : IsUpUni B := by
      intro i j
      refine ⟨fun hji => ?_, fun hij => ?_⟩
      · have h1 : i ≠ j := fun h => (lt_irrefl j) (h ▸ hji)
        have h2 : ¬ (i < j ∧ Formalism.L2.SG.RealObj.blkOf w.1 i.1 = Formalism.L2.SG.RealObj.blkOf w.1 j.1) := fun h => (lt_asymm hji) h.1
        simp only [B, if_neg h1, dif_neg h2]
      · simp only [B, if_pos hij]
    have hBblk : ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 →
        B a b = 0 := by
      intro a b hne
      have h1 : a ≠ b := fun h => hne (h ▸ rfl)
      have h2 : ¬ (a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1) := fun h => hne h.2
      simp only [B, if_neg h1, dif_neg h2]
    obtain ⟨x, ⟨hxSt, hxB⟩, -⟩ := hStCo.2 B hBU hBblk
    have hxK : x ∈ G.K0 := by
      refine (hK x hxSt B hxB).2 fun a b hab => ?_
      have h1 : a ≠ b := ne_of_lt hab
      by_cases h2 : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
      · simp only [B, if_neg h1, dif_pos h2]
        have := hlam ⟨(a, b), h2⟩
        rw [hexp _ _ hab] at this
        exact this
      · simp only [B, if_neg h1, dif_neg h2]
        exact FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hxB⟩
    have hM : GlobalTheory.HL.TraceConjugationCover.stMat G x = B := by
      funext a b
      have e2 : ∑ d, (GlobalTheory.HL.TraceConjugationCover.stMat G x d b - B d b) • G.f' d = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, ← hspec b, ← hxB b, sub_self]
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ e2 a)
    refine ⟨x, hxK, ?_⟩
    funext v p
    have e1 := congrFun (hlamE p) v
    simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at e1
    rw [hM, ← e1]
    have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
    simp only [B, if_neg h1, dif_pos p.2]
    all_goals first | rfl | (congr 1)

end GlobalTheory.HL.StIntLat
