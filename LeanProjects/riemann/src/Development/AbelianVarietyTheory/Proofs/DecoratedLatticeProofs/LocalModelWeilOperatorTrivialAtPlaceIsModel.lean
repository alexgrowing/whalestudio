import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocModMove

theorem placeIdem_mul_eq_zero {D : D7} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε) (a : AE D)
    (ha : a ∈ GlobalTheory.FinPl.idOff D (· = v)) : algebraMap (AF D.host.F) (AE D) ε * a = 0 := by
  obtain ⟨α, hεα, hv, hw⟩ := hε
  obtain ⟨h0, hc⟩ := GlobalTheory.FinPl.placeIdempotent_infinite_and_finite_components D v ε α hεα
  have hav : GlobalTheory.FinPl.compAt D v a = 0 := by
    simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at ha
    exact ha v rfl
  apply GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_mul, h0, zero_mul]
  · intro w
    rw [RingHom.map_mul]
    by_cases h : w = v
    · subst h; rw [hav, mul_zero]
    · rw [hc w, hw w h, TensorProduct.zero_tmul, zero_mul]

theorem ent_of_mem_grpOff {D : D7} {V : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D V}
    (hg : g ∈ GlobalTheory.FinPl.grpOff V P) :
    ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D P := by
  have hker := MonoidHom.mem_ker.1 hg
  intro i j
  rw [← Ideal.Quotient.eq]
  have h2 := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ GlobalTheory.FinPl.idOff D P) => u.1 i j) hker
  simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
  have h3 : Ideal.Quotient.mk (GlobalTheory.FinPl.idOff D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ GlobalTheory.FinPl.idOff D P)) i j := by
    by_cases hij : i = j
    · subst hij; simp only [Matrix.one_apply_eq, map_one]
    · simp only [Matrix.one_apply_ne hij, map_zero]
  rw [h3, ← h2]
  rfl

theorem mul_mul_eq_self {D : D7} {m n : ℕ} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    (A : Matrix (Fin m) (Fin m) (AE D)) (B : Matrix (Fin n) (Fin n) (AE D)) (y : Matrix (Fin m) (Fin n) (AE D))
    (hA : ∀ i j, A i j - (1 : Matrix (Fin m) (Fin m) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D (· = v))
    (hB : ∀ i j, B i j - (1 : Matrix (Fin n) (Fin n) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D (· = v))
    (hy : ∀ i j, algebraMap (AF D.host.F) (AE D) ε * y i j = y i j) : HMul.hMul (HMul.hMul A y) B = y := by
  have kill : ∀ a ∈ GlobalTheory.FinPl.idOff D (· = v), ∀ b : AE D, b = algebraMap (AF D.host.F) (AE D) ε * b → a * b = 0 := by
    intro a ha b hb
    rw [hb, ← mul_assoc, mul_comm a, placeIdem_mul_eq_zero v ε hε a ha, zero_mul]
  have h1 : HMul.hMul (A - 1) y = (0 : Matrix (Fin m) (Fin n) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.sub_apply]
    exact kill _ (hA i l) _ (hy l j).symm
  have h2 : HMul.hMul y (B - 1) = (0 : Matrix (Fin m) (Fin n) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.sub_apply, mul_comm]
    exact kill _ (hB l j) _ (hy i l).symm
  have e1 : HMul.hMul A y = y := by
    rw [← sub_eq_zero, ← h1, Matrix.sub_mul, Matrix.one_mul]
  have e2 : HMul.hMul y B = y := by
    rw [← sub_eq_zero, ← h2, Matrix.mul_sub, Matrix.mul_one]
  rw [e1, e2]

theorem actO_eq_self {D : D7} {V W : HSp D} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    {g : GA D V} (hg : g ∈ GlobalTheory.FinPl.grpOff V (· = v)) {h : GA D W} (hh : h ∈ GlobalTheory.FinPl.grpOff W (· = v))
    (y : WO V W) (hy : IsHalf (algebraMap (AF D.host.F) (AE D) ε) y) : actO V W g h y = y := by
  unfold actO
  exact mul_mul_eq_self v ε hε _ _ _ (ent_of_mem_grpOff hh)
    (ent_of_mem_grpOff ((GlobalTheory.FinPl.grpOff V (· = v)).inv_mem hg)) hy

theorem isModel_weil_off : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (ω : Om V W), IsWeilDatumO ψ V W χV χW ω →
  ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FV : Frame k V.rank Y') (FW : Frame k W.rank Y)
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO V W → ℂ)), (ofSplit q).IsModel ψ FV FW Tm →
  ∀ g ∈ GlobalTheory.FinPl.grpOff V (· = q.v), ∀ h ∈ GlobalTheory.FinPl.grpOff W (· = q.v), (ofSplit q).IsModel ψ FV FW ((ω (g, h)) ∘ₗ Tm) := by
  intro D k _ _ _ _ q ψ hψ V W χV χW ω hω Y Y' _ _ _ _ FV FW Tm hM g hg h hh
  obtain ⟨ε, hεv, hsum⟩ := q.above
  refine (GlobalTheory.LocModU.localModel_uniq_transport_exist D k (ofSplit q) Y Y' V W FV FW ψ hψ).2.1 Tm hM (ω (g, h))
    (fun f hf => hω.om_pres _ f hf) (fun f hf y hy => ?_)
  have hy' : IsHalf (algebraMap (AF D.host.F) (AE D) ε) y := by
    rw [← hsum]; exact hy
  rw [hω.om_heis g h y f hf, actO_eq_self q.v ε hεv hg hh y hy']

end GlobalTheory.LocModMove
