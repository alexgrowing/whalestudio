import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastBiExpand
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsModelChg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LastStepOne

theorem first_step_flat : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hLoc : LocP ch) (hBes : BesP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (r r₀ h : Pts ch.G)
    (hpts : IsPts ch t w β p.e r r₀ h) (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt ch.G j 0 hj))
    (h₁ : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1))
    (h₂ : topRank (locGrid ch.G t w) j + (0 + 1) = (locGrid ch.G t w).rank (D.R.m, j)),
    ∃ (F₀ : Frame (Kw w) (besAt ch.G hM j 0 hj vN).V₀.rank (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit))
      (T₁ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)) →ₗ[ℂ]
        (WO (besAt ch.G hM j 0 hj vN).V₀ (ch.G.V (.top (j + 1))) → ℂ)),
      p.IsCoreFrame (besAt ch.G hM j 0 hj vN) (p.xi ^ 0)⁻¹ (frTop ch.S.toGridChoice t w j (by omega)) F₀ ∧
      p.IsModel ch.W.ψ F₀ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) T₁ ∧
      (∀ O, IsOne O → T₁ O = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
        ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r₀) j, 1) (v ⟨j, by omega⟩))) ∧
      ∃ Φ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)),
        Φ.1 = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) (datC h₁ h₂
          (phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j))) ∧
        T₁ Φ = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
          ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r) j, 1) (f ⟨j, by omega⟩)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hChr hArr hLoc hBes hJac t w hw p hp β r r₀ h hpts M hM φ v f hvf j hj vN h₁ h₂
  have hm := D.R.two_le_m
  have hjm : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  have hev : Even j := by
    obtain ⟨a, ha⟩ := D.R.m_even
    exact ⟨a - 1, by omega⟩
  have hL := hLoc t w hw p hp β r r₀ h hpts j hjm.le
  have hc := hChr t w hw p hp

  have hone : p.IsLoc (frRow ch.S.B t w (j + 1) hjm) 1
      ((epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, j + 1)) := by
    have e1 : (epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, j + 1) = 1 := by
      rw [Pi.mul_apply, epsV_eq_one t w (by omega), elt_eq_one t w β (by omega), one_mul]
    have hmt : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m (j + 1))) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    refine ⟨fun a b => ?_, ?_⟩
    · rw [hmt, sub_self]
      simp
    · rw [e1, hmt, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Matrix.mul_one, (frRow ch.S.B t w (j + 1) hjm).βγ]
  obtain ⟨Tm, hTm, hTmO, Φ, hΦ, hTmΦ⟩ := hArr t w hw p hp φ j hjm (v ⟨j, hjm⟩) (f ⟨j, hjm⟩) (hvf ⟨j, hjm⟩)
    (epsV ch.G t w) ((repsAt ch.G t w).elt β) (epsV_mem t w) (h j * r₀ j) ((r₀ j)⁻¹ * r j) 1 1 hL.1 hone
    _ _ (frame h₂) (frame h₁)
  have hB := hBes t w hw p hp M hM j 0 hj vN (h j * r₀ j) (hL.2.1 hev) (0 + 1) h₂
  have hJ := hJac t w hw p hp M hM j 0 hj vN 1 (Or.inl ⟨rfl, rfl⟩) 0 h₁
  have hs : ((p.xi ^ 0)⁻¹ : Kw w) ≠ 0 := by simp
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.LocMod.Witness.exists_core p (besAt ch.G hM j 0 hj vN) hs
    (frTop ch.S.toGridChoice t w j (by omega))
  have hBF := GlobalTheory.FlatBFLoc.flatBF_of_laws D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  obtain ⟨T₀, hT₀, hT₀e⟩ := hBF (Kw w) p (unitVol w) (isUnitVol_unitVol w).1 ch.W.ψ (psiAt ch.W w) hc.1 0
    (besAt ch.G hM j 0 hj vN) (lastAt ch.G ch.W t hM j hj vN).J (lastAt ch.G ch.W t hM j hj vN).s (p.xi ^ 0)⁻¹ hs
    _ _ 0 (frTop ch.S.toGridChoice t w j (by omega)) F₀ _ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) _ hF₀ hB hJ Tm hTm
  have hψc : Continuous (psiAt ch.W w) := hc.2.1.continuous
  have hfl := GlobalTheory.LocFlat.flat_SB_onto (Kw w) (psiAt ch.W w) (unitVol w) hψc (isUnitVol_unitVol w).1
    (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j)) 0 (0 + 1) le_rfl
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator (Kw w) (psiAt ch.W w) (unitVol w) hc.2.1 (isUnitVol_unitVol w)
    (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j)) (Fin (topRank (locGrid ch.G t w) j)) 0 (0 + 1)
  refine ⟨F₀, T₀, hF₀, hT₀, fun O hO => ?_, ⟨_, (hfl.1 le_rfl).1 Φ.1 Φ.2⟩, ?_, ?_⟩
  · let Ob : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (0 + 1)) (Kw w)) :=
      ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
    have hOb : GlobalTheory.LocMod.IsOne Ob := rfl
    have e : O.1 = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) Ob.1 := by
      rw [hO]
      show _ = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) (Set.indicator _ _)
      rw [hun.1, if_neg (by omega)]
    refine (hT₀e Ob O e).symm.trans ?_
    exact congrArg _ (hTmO Ob hOb)
  · show GlobalTheory.LocFlat.flCol _ _ _ Φ.1 = _
    congr 1
    funext z
    exact hΦ z
  · refine (hT₀e Φ ⟨_, (hfl.1 le_rfl).1 Φ.1 Φ.2⟩ rfl).symm.trans ?_
    refine congrArg _ (hTmΦ.trans ?_)
    have e : (h j * r₀ j * ((r₀ j)⁻¹ * r j), (1 : GA D (ch.G.V (.grid D.R.m (j + 1)))) * 1) = (h j * r j, 1) := by
      rw [mul_one, mul_assoc, mul_inv_cancel_left]
    rw [e]
    rfl

end GlobalTheory.LastStepOne
