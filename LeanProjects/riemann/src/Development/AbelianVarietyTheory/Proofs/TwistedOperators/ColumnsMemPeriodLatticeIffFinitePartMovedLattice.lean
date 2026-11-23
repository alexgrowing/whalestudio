import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaAtEqProdAhG
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaDictionaryLatticeOfFrameCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMapColumnsMemLatGIffMovedFinitePartStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

theorem perVec_mem_range_iff (Wt : UnfAt U k x) (v : Fin r → D.host.E) :
    perVec Wt v ∈ Set.range Wt.Pm ↔ v ∈ (U.X k).Λ := by
  constructor
  · rintro ⟨a, ha⟩
    set w := v - (Wt.φ k a : Fin r → D.host.E) with hw
    have hpw : pv Wt w = 0 := by
      have e1 : pv Wt w = pv Wt v - pv Wt (Wt.φ k a : Fin r → D.host.E) := map_sub (pvHom Wt) _ _
      rw [e1, pv_lat]
      change perVec Wt v - Wt.Pm a = 0
      rw [← ha, sub_self]
    obtain ⟨N, hN, hNw⟩ := exists_nsmul_mem (U.X k) w
    set c' := (Wt.φ k).symm ⟨N • w, hNw⟩ with hc'
    have hc : (Wt.φ k c' : Fin r → D.host.E) = (N : D.host.E) • w := by
      rw [hc', LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
    have hP : Wt.Pm c' = Wt.Pm 0 := by
      rw [← pv_lat, hc, pv_nsmul, hpw, smul_zero, map_zero]
    have h0 : c' = 0 := Wt.per.2.1 hP
    have hw0 : (N : D.host.E) • w = 0 := by rw [← hc, h0, map_zero]; rfl
    have hw0' : w = 0 := by
      rcases smul_eq_zero.1 hw0 with h | h
      · exact absurd (Nat.cast_eq_zero.1 h) hN
      · exact h
    have : v = (Wt.φ k a : Fin r → D.host.E) := sub_eq_zero.1 hw0'
    rw [this]
    exact (Wt.φ k a).2
  · intro hv
    refine ⟨(Wt.φ k).symm ⟨v, hv⟩, ?_⟩
    rw [← perVec_lat, LinearEquiv.apply_symm_apply]

end GlobalTheory.AHPhase

theorem GlobalTheory.AHPhase.cols_per_iff_latO : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (ph : ℂ)
    (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).2, hx⟩)
      (Y : UnitAt Wt), GlobalTheory.AHPhase.PinAt T R i σ hV ph b γ g hx Wt Y →
    ∀ Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt (GlobalTheory.AHPhase.colB b Yr a) ∈ Set.range Wt.Pm) ↔
        actO (Vc D i) (Wc D i) 1 (γ * g)⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV ph b hph hb γ hγ g hfr hx Wt Y hp Yr
  rw [← GlobalTheory.T.rationalMap_columns_mem_latG_iff_moved_finitePart D G Pl0 T0 A T.Q.c.F R hLev i b hb (γ * g) Yr]
  refine forall_congr' fun a => ?_
  rw [GlobalTheory.AHPhase.perVec_mem_range_iff,
    GlobalTheory.T.thetaDictionary_lattice_of_frameCoordinates D G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV γ hγ g hfr]
  have e : (fun m : Fin (Wc D i).rank => GlobalTheory.AHPhase.colB b Yr a (Fin.cast (rank_Wc i) m)) =
      fun m => ∑ n, Yr m n * b n a := by
    funext m
    simp [GlobalTheory.AHPhase.colB]
  rw [e]
