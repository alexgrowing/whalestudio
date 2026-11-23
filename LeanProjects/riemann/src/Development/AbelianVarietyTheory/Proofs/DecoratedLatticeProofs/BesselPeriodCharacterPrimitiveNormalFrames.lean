import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameColumnsUnitScaling
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIffCharacterTrivialSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIntIn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColPairSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimNormal

theorem z_pair {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : Fin S₀.rank → D.host.E) (i : Fin ρ) :
    ∑ r, ∑ t, star ((d.i₀ *ᵥ v) r) * HSpace.gram S r t * d.e t i = 0 := by
  have hent : ∀ c, ∑ r, ∑ t, star (d.i₀ r c) * HSpace.gram S r t * d.e t i = 0 := fun c => by
    rw [← GlobalTheory.SplitPrimJac.mat_entry S d.i₀ d.e c i, d.i₀e, Matrix.zero_apply]
  have e : ∑ r, ∑ t, star ((d.i₀ *ᵥ v) r) * HSpace.gram S r t * d.e t i =
      ∑ c, star (v c) * ∑ r, ∑ t, star (d.i₀ r c) * HSpace.gram S r t * d.e t i := by
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    calc _ = ∑ r, ∑ c, ∑ t, star (d.i₀ r c) * star (v c) * HSpace.gram S r t * d.e t i :=
            Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ c, ∑ r, ∑ t, star (d.i₀ r c) * star (v c) * HSpace.gram S r t * d.e t i := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
  rw [e]
  simp [hent]

end GlobalTheory.PrimNormal

namespace GlobalTheory.PrimNormal

theorem prim_of_normal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.PrimAt ψ ((y.bes j ρ h).lev (a.x j).vol).d (N j) (PP.under (𝓞 D.host.F)) := by
  intro D ψ hψ a y βT PP l FY sc hN hx N M hNsd hNint hMsd hMcore j ρ h
  rw [← l.under]
  have hc : j + (2 * ρ + 1) = l.s + 1 := by have := l.hs; omega
  have hB := hN.2.2.2.1 j ρ h (2 * ρ + 1) hc
  have hξ : valuation l.k (ofSplit l.q).xi = 1 := GlobalTheory.QTw.GeoInhab.xi_unit l.q l.unit
  have hsc := hN.1 j
  have hz := hN.2.2.1 j ρ h
  have inner0 : ∀ (x : Fin (Yc D j).rank → D.host.E) (i : Fin ρ),
      (∑ r, ∑ t, star (x r) * HSpace.gram (Yc D j) r t * ((y.bes j ρ h).lev (a.x j).vol).d.e t i) = 0 →
      ∀ (b : l.k) (col : Fin (Yc D j).rank → l.k), (∀ r, col r = b * l.q.pr (incA D (x r))) →
      ∑ r, ∑ t, col r * l.q.pr (cA D (incA D (HSpace.gram (Yc D j) r t))) *
        l.q.pr (cA D (incA D (((y.bes j ρ h).lev (a.x j).vol).d.e t i))) = 0 := by
    intro x i hx b col hcol
    rw [GlobalTheory.SplitPrimJac.colPair_smul l.q _ b x _ col hcol, hx, star_zero, map_zero, map_zero, mul_zero]
  have line : ∀ (i : Fin ρ) (b : AE D), GlobalTheory.FinPl.colMul ((y.bes j ρ h).lev (a.x j).vol).d.jX i b ∈
      GlobalTheory.FinPl.latV (Yc D j) (N j) (· = l.q.v) ↔ b ∈ GlobalTheory.FinPl.intAt D (· = l.q.v) := by
    intro i b
    refine GlobalTheory.PrimSplitLine.colMul_mem_latV_iff D l.k l.q _ _ ρ ((y.bes j ρ h).lev (a.x j).vol).d (N j) _
      (FY j (2 * ρ + 1) hc) i (Sum.inr ⟨i.val, by omega⟩) (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
      (sc j * (ofSplit l.q).xi ^ (ρ - i.val))
      (sc j * (-(ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) * (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val))
      (hNsd j (by omega)) (hNint j _ hc) ?_ ?_ ?_ ?_ b
    · rw [map_mul, map_pow, hsc, hξ, one_pow, one_mul]
    · simp only [map_mul, map_div₀, map_pow, Valuation.map_neg, map_one, hsc, hz, hξ]; simp
    · intro r; exact hB.2.2.1 i ⟨i.val, by omega⟩ rfl r
    · intro m
      rcases m with b | m
      · rw [if_neg Sum.inl_ne_inr]
        have hcol : ∀ r, (FY j (2 * ρ + 1) hc).β r (Sum.inl b) = ∑ e, (l.FX j (by omega)).β e b *
            l.q.pr (incA D ((((y.bes j ρ h).lev (a.x j).vol).d.i₀ * ((y.bes j ρ h).lev (a.x j).vol).o.iA) r e)) := by
          intro r
          rw [hB.2.1 r b, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun e _ => mul_comm _ _
        simp only [hcol, Finset.sum_mul]
        rw [Finset.sum_congr rfl fun r _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_eq_zero fun e _ => ?_
        simp only [mul_assoc]
        simp only [← mul_assoc]
        refine inner0 (fun r => (((y.bes j ρ h).lev (a.x j).vol).d.i₀ * ((y.bes j ρ h).lev (a.x j).vol).o.iA) r e) i ?_ _ _
          fun r => rfl
        rw [← GlobalTheory.SplitPrimJac.mat_entry, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc _ (HSpace.gram _), ((y.bes j ρ h).lev (a.x j).vol).d.i₀e, Matrix.mul_zero, Matrix.zero_apply]
      · by_cases hm : m.val < ρ
        · rw [if_neg (fun he => by cases he; simp at hm; omega)]
          refine inner0 (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e r ⟨m.val, hm⟩) i ?_ _ _ (hB.2.2.1 ⟨m.val, hm⟩ m rfl)
          rw [← GlobalTheory.SplitPrimJac.mat_entry, ((y.bes j ρ h).lev (a.x j).vol).d.ee, Matrix.zero_apply]
        · by_cases hm' : m.val = ρ
          · rw [if_neg (fun he => by cases he; simp at hm'; omega)]
            refine inner0 (fun r => (((y.bes j ρ h).lev (a.x j).vol).d.i₀ *ᵥ
              vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) r) i ?_ _ _ (hB.2.2.2.1 m hm')
            exact z_pair _ _ i
          · have hi' : 2 * ρ - m.val < ρ := by omega
            have hcol := hB.2.2.2.2 ⟨2 * ρ - m.val, hi'⟩ m (by simp; omega)
            rw [GlobalTheory.SplitPrimJac.colPair_smul l.q _ _ _ _ _ hcol, ← GlobalTheory.SplitPrimJac.mat_entry,
              ((y.bes j ρ h).lev (a.x j).vol).d.e'e, Matrix.one_apply]
            by_cases hii : (⟨2 * ρ - m.val, hi'⟩ : Fin ρ) = i
            · have hmv : m.val = 2 * ρ - i.val := by rw [← hii]; simp; omega
              rw [if_pos hii, if_pos (by congr 1; exact Fin.ext hmv), star_one, map_one, map_one, mul_one, ← hii]
            · rw [if_neg hii, if_neg (fun he => hii (by cases he; ext; simp; omega)), star_zero, map_zero, map_zero,
                mul_zero]
  obtain ⟨ψk, hχ, hcond⟩ := GlobalTheory.QTw.GeoInhab.exists_char l.q l.unit hψ
  have hε : l.q.e + cA D l.q.e ∈ GlobalTheory.FinPl.intAt D (· = l.q.v) :=
    ⟨GlobalTheory.FinPl.FrameLat.sum_mem_idAt l.q, by
      rw [RingHom.map_add]
      exact add_mem (GlobalTheory.FinPl.FrameLat.e_mem_intAt l.q).2
        ((GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 (GlobalTheory.FinPl.FrameLat.e_mem_intAt l.q).2)⟩
  intro i i' hii' t ht
  rw [← GlobalTheory.SplitIntChar.int_iff_psiE D l.k l.q ψ ψk hξ hχ hcond t ht]
  constructor
  · intro H
    have h1 := H (l.q.e + cA D l.q.e) ((line i' _).2 hε)
    have ht' : t * (l.q.e + cA D l.q.e) = t := by rw [mul_comm]; exact (GlobalTheory.FinPl.FrameLat.idem_iff l.q t).1 ht
    rwa [line i, ht'] at h1
  · intro H b hb
    rw [line i'] at hb
    rw [line i]
    exact ⟨Ideal.mul_mem_right _ _ H.1, by rw [RingHom.map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE H.2 hb.2⟩

end GlobalTheory.PrimNormal
