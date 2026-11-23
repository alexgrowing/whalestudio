import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfComps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvFinSSOneNot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemHROfGram
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameCompletes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenMulEqIdem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFreeFramePairs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RgTrans

private theorem mul_mul_mul_smul_eq_smul_mul_mul_mul {A : Type*} [CommRing A] {a b c d f : Type*} [Fintype b] [Fintype c]
    [Fintype d] (R : Matrix a b A) (P : Matrix b c A) (G : Matrix c d A) (X : Matrix d f A) (e : A) :
    R * (P * (G * (e • X))) = e • (R * (P * (G * X))) := by
  simp only [Matrix.mul_smul]

private theorem yv_smul_snd {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) (e : AE D)
    (w : Mx D V.rank r × Mx D V.rank t) :
    yv V b₀ (w.1, e • w.2) = e • yv V b₀ w :=
  mul_mul_mul_smul_eq_smul_mul_mul_mul _ _ _ _ e

theorem idemEx_trans : IdemEx → Trans := by
  intro hI D r t V b₀ hb₀ S e he
  have hee : e * e = e := ((hI D S).2 e he).1
  have hce : cA D e = e := ((hI D S).2 e he).2
  refine ⟨GlobalTheory.CompanionTheory.FreeFrames.isOpen_free D r t V.rank e hee
    (GlobalTheory.CompanionTheory.UnitNbhd.exists_open_mul_eq_idem GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D S e he), ?_⟩
  intro z z' hz hz' hzc hz'c
  obtain ⟨Γ, hΓ, hN⟩ := GlobalTheory.CompanionTheory.FrameComplete.frame_completes D r t V b₀ hb₀ e hee hce
  obtain ⟨N, hNe, hNg, hN1, hN2⟩ := hN z hz hzc
  obtain ⟨N', hN'e, hN'g, hN'1, hN'2⟩ := hN z' hz' hz'c
  obtain ⟨h, hh, hhN⟩ := GlobalTheory.CompanionTheory.WittS.exists_unitary_off_S
    (GlobalTheory.CompanionTheory.SPartTensor.sPart GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps) D V S e he _ Γ hΓ N N'
    hNe hN'e hNg hN'g
  have hy : ∀ w : Mx D V.rank r × Mx D V.rank t, e • w.2 = w.2 → e • yv V b₀ w = yv V b₀ w := by
    intro w hw
    have key : yv V b₀ w = e • yv V b₀ w := by
      calc yv V b₀ w = yv V b₀ (w.1, e • w.2) := by rw [hw]
        _ = e • yv V b₀ w := yv_smul_snd V b₀ e w
    rw [key, smul_smul, hee]
  have h1 : mm (mt V h) z.1 = z'.1 := by
    ext i j
    rw [← hN'1, ← hhN]
    simp only [mm, Matrix.mul_apply, hN1]
  have h2 : mm (mt V h) (z.2 - mm z.1 (yv V b₀ z)) = z'.2 - mm z'.1 (yv V b₀ z') := by
    ext i j
    rw [← hN'2, ← hhN]
    simp only [mm, Matrix.mul_apply, hN2]
  refine ⟨h, yv V b₀ z' - yv V b₀ z, hh, ?_, ?_⟩
  · rw [smul_sub, hy z' hz'c.2.1, hy z hzc.2.1]
  · have h3 : mm (mt V h) (z.2 + mm z.1 (yv V b₀ z' - yv V b₀ z)) =
        mm (mt V h) (z.2 - mm z.1 (yv V b₀ z)) + mm (mm (mt V h) z.1) (yv V b₀ z') := by
      simp only [mm, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]
      abel
    refine Prod.ext h1.symm ?_
    rw [h3, h1, h2]
    simp only [mm, sub_add_cancel]

end GlobalTheory.CompanionTheory.RgTrans
