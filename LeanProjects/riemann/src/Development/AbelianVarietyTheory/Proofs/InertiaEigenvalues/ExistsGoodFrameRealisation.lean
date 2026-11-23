import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameOfReal

theorem exists_frame_real : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ j : Fin D.R.m, ∃ F : Frame (Vc D j) (Wc D j), F.Good ∧ IsStdChar D F.ψ (-1) ∧ F.ψ = Rl.ψ ∧ F.θ = Rl.θ ∧ F.sT = cart (Rl.MW j (sg0 D A3.A)) ∧ (∀ τ, (F.BS τ).val = Rl.BV j τ) ∧ F.BT = onb (Rl.MW j (sg0 D A3.A)) ∧ F.ΛS = Rl.ΛV j ∧ F.ΛT = Rl.ΛW j ∧ F.βS = Rl.βV j ∧ F.βT = Rl.βW j ∧ F.f₀ = Rl.vacP j ∧ Lev.IsBaseFrame (Vc D j) F.βS F.ΛS 1 ∧ Lev.IsBaseFrame (Wc D j) F.βT F.ΛT 1 := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC j
  have hBV := hC.models.BV j
  have hu : ∀ τ, IsUnit (Rl.BV j τ) := fun τ => by
    obtain ⟨ε, hε, h2, -⟩ := hBV τ
    have hd : (Matrix.diagonal fun a => (ε a : ℂ)) * Matrix.diagonal (fun a => (ε a : ℂ)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rcases hε a with h | h <;> simp [h.1]
    refine IsUnit.of_mul_eq_one_right (Matrix.diagonal (fun a => (ε a : ℂ)) * (Matrix.conjTranspose (Rl.BV j τ) * gramAt D (Vc D j) τ)) ?_
    rw [Matrix.mul_assoc, h2, hd]
  have sdV := hC.lev.βV j
  have sdW := hC.lev.βW j
  have bV : Lev.IsBaseFrame (Vc D j) (Rl.βV j) (Rl.ΛV j) 1 := by
    obtain ⟨c, hc⟩ := sdV
    rwa [one_pow] at hc
  have bW : Lev.IsBaseFrame (Wc D j) (Rl.βW j) (Rl.ΛW j) 1 := by
    obtain ⟨c, hc⟩ := sdW
    rwa [one_pow] at hc
  have hv := (hC.thP.vP j A3.A.μ0).1
  have hstd := (hC.thP.ωP j A3.A.μ0).std
  refine ⟨⟨Rl.ψ, Rl.θ, cart (Rl.MW j (sg0 D A3.A)), fun τ => (hu τ).unit, onb (Rl.MW j (sg0 D A3.A)), Rl.ΛV j, Rl.ΛW j,
    Rl.βV j, Rl.βW j, Rl.vacP j⟩, ?_, hstd, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, bV, bW⟩
  exact
    { rank_le := (D.sp.W_rank _ (Nat.le_add_left _ _) j.2).le.trans (r_le_V j)
      onbS := hBV
      cartT := fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
      onbT := fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order j τ)
      sdS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ sdV
      sdT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ sdW
      frS := bV.1
      frT := bW.1
      vac := hv }

end GlobalTheory.FrameOfReal
