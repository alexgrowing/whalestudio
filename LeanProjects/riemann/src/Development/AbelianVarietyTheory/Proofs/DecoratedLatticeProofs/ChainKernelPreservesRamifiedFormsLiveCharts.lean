import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepKernelPreservesLevelRamifiedFormsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumEqFiniteDatumRepresentativePairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem kernels_keep_ramL : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j), A.Is → A.Live ι → ∀ i, i < B.R.m → ∀ φ, A.RamL ι i φ → A.RamL ι (i + 1) ((I.chain l u a).K i φ) := by
  intro B X I hOk hP l Z u a Ch₀ Ch A ι hIs hLive i hi φ hφ
  refine ⟨GlobalTheory.T.chainStepKernel_preserves_levelRamifiedForms I hOk hP l Z u a i hi φ hφ.1, ?_⟩
  intro c' hc'
  have hSB : IsSBHalf A.e (stdHom ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))) (0 : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) :=
    ⟨fun t h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun t h => absurd rfl h⟩
  have key := fun (c : (I.chain l u a).cls i) (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) =>
    (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hOk hP l Z u a Ch₀ A hIs i hi (A.chOf i c) (A.chOf (i+1) c') 0 hSB 1
      (fun z => by simp [hLive.dead i hi _ hc']) ⟨c, rfl⟩ ⟨c', rfl⟩).2.2 z
  have hxi : ∀ c : (I.chain l u a).cls i, xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') = 0 := by
    intro c
    funext x
    obtain ⟨γ, rfl⟩ : ∃ γ, toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ = x := by
      refine ⟨(LinearMap.toMatrix' x).submatrix (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))), ?_⟩
      show Matrix.toLin' _ = x
      conv_rhs => rw [← Matrix.toLin'_toMatrix' x]
      rfl
    have h1 := key c γ
    simp only [Pi.zero_apply, one_mul] at h1
    exact (map_eq_zero_iff _ B.embLL.injective).1 h1.symm
  have hth : ∀ c : (I.chain l u a).cls i, I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') = 0 := by
    intro c
    unfold TC.th thAt
    rw [hxi c]
    exact thOf_zero ..
  have hunf : ∀ c : (I.chain l u a).cls i, (I.chain l u a).unf i c c' = 0 := by
    intro c
    show ChainIn.unf _ _ _ _ _ _ = 0
    unfold ChainIn.unf
    show _ ∘ₗ jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))) 0 ∘ₗ _ = 0
    rw [hth c]
    have hJ : jetC I.J.cD (0 : VCx B.fields.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ) = 0 := by
      funext m
      simp [jetC, derivAt0, iteratedFDeriv_zero_fun]
    rw [hJ]
    have hM : jetMap (0 : (DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) → ℂ) 0 = 0 := by
      have hL : jetLin (0 : (DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) → ℂ) = 0 := by
        apply (MvPolynomial.basisMonomials _ ℂ).ext
        intro m
        rw [jetLin, Module.Basis.constr_basis]
        simp
      unfold jetMap
      rw [hL]
      simp
    rw [hM]
    simp
  have hK : ∀ c : (I.chain l u a).cls i, (I.chain l u a).Kmap i c c' = 0 := by
    intro c
    unfold ColumnChain.Kmap
    rw [hunf c]
    simp
  funext y
  simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, hK]
  simp

end GlobalTheory.AdForm
