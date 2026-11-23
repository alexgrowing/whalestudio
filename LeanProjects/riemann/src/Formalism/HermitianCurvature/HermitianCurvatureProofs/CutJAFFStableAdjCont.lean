import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjS

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gf_sgs (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) (g : B.Mat k r) :
    Gf k r D.z D.z' (B.sgs p g) = Gf k r D.z D.z' g := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hn1 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ ∈ Q.Nlev k r 0 := by
    refine ⟨Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.n_inv_mem hn, ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutMP.ER.CAS.level_zero_set_eq_group]
    exact (Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.n_inv_mem hn).1
  have hn2 : (Matrix.of p.2.2 : B.Mat k r) ∈ Q.Nlev k r 0 := by
    refine ⟨hn', ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutMP.ER.CAS.level_zero_set_eq_group]
    exact hn'.1
  have e1 := Formalism.FourierDecayAlt.P.CutMP.gf_SgS D (Formalism.FourierDecayAlt.P.CutMP.h_mem_Sset D.z (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh))
    (Formalism.FourierDecayAlt.P.CutMP.h_mem_Sset D.z' hh') ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * g * Matrix.of p.2.2)
  have e2 := Formalism.FourierDecayAlt.P.CutMP.gf_SgS D (Formalism.FourierDecayAlt.P.CutMP.n_mem_Sset D.z hn1)
    (Formalism.FourierDecayAlt.P.CutMP.n_mem_Sset D.z' hn2) g
  unfold B.sgs
  rw [← e2, ← e1]
  congr 1
  simp only [mul_assoc]

theorem sgs_mem (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) {g : B.Mat k r}
    (hg : g ∈ B.GV k r) : B.sgs p g ∈ B.GV k r := by
  rw [Formalism.FourierDecayAlt.P.B5.sgs_eq]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
    (Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem (Formalism.FourierDecayAlt.P.B5.inSS_left D hp)) hg) (Formalism.FourierDecayAlt.P.B5.inSS_right D hp)

theorem sgs_continuous (p : B.SS k r) : Continuous (B.sgs p : B.Mat k r → B.Mat k r) := by
  unfold B.sgs
  exact (((continuous_const : Continuous fun _ : B.Mat k r =>
    (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹).matrix_mul continuous_id).matrix_mul
    continuous_const).matrix_mul continuous_const

theorem suppIn_rho (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : B.SuppIn (B.GPos D) F) : B.SuppIn (B.GPos D) (B.rho D p F) := by
  intro x hx
  have hxG : x ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (fun y hy => hy.1) hx
  have hsub : {g | g ∈ B.GV k r ∧ B.rho D p F g ≠ 0} ⊆ B.sgs p ⁻¹' {g | g ∈ B.GV k r ∧ F g ≠ 0} := by
    intro y hy
    refine ⟨sgs_mem D hp hy.1, fun h0 => hy.2 ?_⟩
    unfold B.rho
    rw [h0]
    simp
  have h1 : x ∈ B.sgs p ⁻¹' closure {g | g ∈ B.GV k r ∧ F g ≠ 0} :=
    (sgs_continuous p).closure_preimage_subset _ (closure_mono hsub hx)
  have h2 := hF h1
  refine ⟨hxG, ?_⟩
  have := h2.2
  rwa [gf_sgs D hp] at this

variable [FiniteDimensional ℂ Wq]

theorem ckOn_opAdj (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (hs : B.SmoothCoef (B.GPos D) Θ)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F) (hFs : B.SuppIn (B.GPos D) F) :
    B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) := by
  unfold B.opAdj
  refine Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_list_sum Θ
    (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) (fun T hT => ?_)
  exact Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' (Formalism.FourierDecayAlt.P.B5.ckOn_coef (hs T hT).2 hF hFs)
    T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)))

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

theorem adjoint_continuity_holds : AdjCont := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs f hf _ hfs p hp
  exact ⟨Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_opAdj D Θ hs (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) (suppIn_rho D hp hfs)),
    Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp (ckOn_opAdj D Θ hs hf hfs))⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
