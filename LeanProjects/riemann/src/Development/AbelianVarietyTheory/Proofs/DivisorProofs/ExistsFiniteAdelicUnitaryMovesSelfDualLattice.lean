import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualComapOrthonormalFrameUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCompletionComapRationalMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryAdelicMatrixConjOrthonormalFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenusTranslate

open GlobalTheory.AdLat GlobalTheory.UnRep

theorem hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    z ∈ Formalism.L2.Herm.hatL L ↔
      (fun i => (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm (z i)) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  refine ⟨GlobalTheory.PrincInLevel.swap_symm_mem_hat L z, fun h => ?_⟩
  have := GlobalTheory.PrincInLevel.swap_mem_hatL L _ h
  simpa using this

set_option maxHeartbeats 2000000 in

theorem exists_move_colLat : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    ∃ x : GA D V, x ∈ GfC V ∧ ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (Formalism.IndefR.Lev.finE V x).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  intro D V fr Λ hfr hΛ
  have hU := GlobalTheory.T.selfDual_comap_orthonormalFrame_unimodular D V fr Λ hfr hΛ
  have hT : (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).TrivAt 1 :=
    ⟨0, Nat.coprime_zero_left 1 |>.2 rfl, by simp, by simp⟩
  have hgen : ∃ g : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E), GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g.1 ∧
      ∀ z, z ∈ GlobalTheory.AdLat.hat D.host.F ((Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔
      (g⁻¹).1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) := by
    obtain ⟨g, hgU, hgL, -⟩ := GlobalTheory.AdelTranslate.exists_adelic_translate D.host.E (Formalism.L2.Pj.hostOfRecord D) V.rank 1 _
      one_pos hU hT
    have hstd := GlobalTheory.UnRep.StdInhab.main D.host.E (Formalism.L2.Pj.hostOfRecord D) V.rank
    have hfg := hstd.2.2.1
    have hsp := hstd.2.2.2.1
    have hL := GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield D.host.E) D.host.E V.rank
      (Formalism.L2.Pj.stdLat D.host.E V.rank) g hfg hsp
    obtain ⟨Λ'', hL''⟩ := hL
    have h1 := hL''.1
    have h4 := hL''.2.2.2
    have e : Λ'' = Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)) :=
      SetLike.coe_injective (h1.trans hgL.symm)
    refine ⟨g, by
      have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
      rw [hc]; exact hgU, fun z => ?_⟩
    rw [← e, ← SetLike.mem_coe, h4]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · intro hz
      exact ⟨_, hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  obtain ⟨g, hgU, hg'⟩ := hgen
  have hfm1 : GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 * GlobalTheory.UnRep.fm D.host.F fr.1 = 1 := by
    rw [← GlobalTheory.UnRep.FullReps.fm_mul, Units.inv_mul, GlobalTheory.UnRep.FullReps.fm_one]
  have hfm2 : GlobalTheory.UnRep.fm D.host.F fr.1 * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 = 1 := by
    rw [← GlobalTheory.UnRep.FullReps.fm_mul, Units.mul_inv, GlobalTheory.UnRep.FullReps.fm_one]
  obtain ⟨U, hU1, hU2⟩ : ∃ U : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E),
      U.1 = GlobalTheory.UnRep.fm D.host.F fr.1 ∧ (U⁻¹).1 = GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 :=
    ⟨⟨GlobalTheory.UnRep.fm D.host.F fr.1, GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1, hfm2, hfm1⟩, rfl, rfl⟩
  have hX := GlobalTheory.T.isUnitaryAdelicMatrix_conj_orthonormalFrame D V fr g.1 hfr hgU
  rw [← hU1, ← hU2, ← Units.val_mul, ← Units.val_mul] at hX
  obtain ⟨X, hXe⟩ : ∃ X : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E), X = U * g * U⁻¹ := ⟨_, rfl⟩
  rw [← hXe] at hX
  have hlift := (GlobalTheory.UnitarySplit.real_finite_split D V).2.2.2.1 X hX
  obtain ⟨x, hx, hxX⟩ := hlift
  have key : ∀ w : Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E,
      w ∈ GlobalTheory.AdLat.hat D.host.F (colLat fr : Set (Fin V.rank → D.host.E)) ↔
        X.1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    intro w
    have ew : GlobalTheory.UnRep.fm D.host.F fr.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← GlobalTheory.UnRep.FullReps.fm_mul, Units.mul_inv, GlobalTheory.UnRep.FullReps.fm_one, Matrix.one_mulVec]
    have h1 := GlobalTheory.T.adelicCompletion_comap_rational_matrix D.host.F D.host.E V.rank fr (colLat fr) (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w)
    rw [ew, GlobalTheory.T.columnLattice_comap_eq_standardLattice] at h1
    have h2 := GlobalTheory.T.adelicCompletion_comap_rational_matrix D.host.F D.host.E V.rank fr Λ (g.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w))
    have hgg : (g⁻¹).1 *ᵥ (g.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w)) = GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hg', hgg] at h2
    rw [h1, hXe, Units.val_mul, Units.val_mul, hU1, hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]
  refine ⟨x, hx, fun v => ?_⟩
  have hfin : (fun i => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm
      (((Formalism.IndefR.Lev.finE V x).1 *ᵥ v) i)) =
      X.1 *ᵥ fun i => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v i) := by
    have hfe : Formalism.IndefR.Lev.finE V x = Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) X := by rw [← hxX]; rfl
    rw [hfe]
    funext i
    rw [AlgEquiv.symm_apply_eq]
    have hv : ⇑(Formalism.IndefR.Lev.swapAE D) ∘ (fun j =>
        (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v j)) = v :=
      funext fun j => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).apply_symm_apply (v j)
    have hm := RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) X.1
      (fun j => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v j)) i
    rw [hv] at hm
    exact hm.symm
  rw [hatL_iff, hatL_iff, hfin]
  exact key _

end GlobalTheory.GenusTranslate
