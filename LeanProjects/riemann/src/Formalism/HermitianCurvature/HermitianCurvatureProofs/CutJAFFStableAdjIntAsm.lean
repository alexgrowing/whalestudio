import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableFormAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem hasCompactSupport_rho (D : B.RealPlaceData k r Wp Wq) {q : B.SS k r} (hq : D.inSS q)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : HasCompactSupport F) : HasCompactSupport (B.rho D q F) := by
  have ha := Formalism.FourierDecayAlt.P.B5.inSS_left D hq
  have hb := Formalism.FourierDecayAlt.P.B5.inSS_right D hq
  have himg : B.sgs q ⁻¹' tsupport F ⊆ (fun g => (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)⁻¹) '' tsupport F := by
    intro x hx
    refine ⟨B.sgs q x, hx, ?_⟩
    dsimp only
    rw [Formalism.FourierDecayAlt.P.B5.sgs_eq]
    have key : ∀ (a b y : B.Mat k r), a * a⁻¹ = 1 → b * b⁻¹ = 1 → a * (a⁻¹ * y * b) * b⁻¹ = y := by
      intro a b y ha hb
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hb, Matrix.mul_one, ← Matrix.mul_assoc, ha, Matrix.one_mul]
    exact key _ _ x (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv ha).1 (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hb).1
  have hcK : IsCompact ((fun g => (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)⁻¹) '' tsupport F) :=
    hF.image ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  refine hcK.of_isClosed_subset isClosed_closure (closure_minimal (fun x hx => himg (subset_tsupport _ ?_)) hcK.isClosed)
  intro h0
  apply hx
  show B.rho D q F x = 0
  unfold B.rho
  rw [h0]
  simp

variable [FiniteDimensional ℂ Wq]

noncomputable def II (D : B.RealPlaceData k r Wp Wq) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  ∫ x : Mt k r, B.hsInner (X (Matrix.of x)) (Y (Matrix.of x)) ∂D.μG

theorem ii_swap (D : B.RealPlaceData k r Wp Wq) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)) : II D X Y = conj (II D Y X) := by
  unfold II
  rw [← integral_conj]
  congr 1
  funext x
  unfold B.hsInner
  rw [inner_conj_symm]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hermitian_curvature_adjoint_integral : AdjIntAsm := by
  intro hU hF k r Wp Wq _ _ _ _ _ _ D Θ hs hc f hf hfc hfs p hp φ hφ hφc hφs
  obtain ⟨p', hp', hUp⟩ := hU k r Wp Wq D p hp
  have hU' : ∀ X Y, II D (B.rho D p X) Y = II D X (B.rho D p' Y) := hUp
  have hF' : ∀ F F' : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F →
      B.SuppIn (B.GPos D) F → B.CkOn ⊤ (B.GV k r) F' → HasCompactSupport F' → B.SuppIn (B.GPos D) F' →
      II D (B.opApply Θ F) F' = II D F (B.opAdj Θ F') := hF k r Wp Wq D Θ hs hc
  have hcomm : II D (B.opApply Θ (B.rho D p' φ)) f = II D (B.rho D p' (B.opApply Θ φ)) f := by
    unfold II
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae D.haarG] with x hx
    by_cases hxp : Matrix.of x ∈ B.GPos D
    · rw [hc p' hp' φ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hφ) _ hxp]
    · have h0 : f (Matrix.of x) = 0 := by
        by_contra hne
        exact hxp (hfs (subset_closure ⟨hx, hne⟩))
      simp only [h0, Formalism.FourierDecayAlt.P.B5.hs_zero_right]
  show II D (B.opAdj Θ (B.rho D p f)) φ = II D (B.rho D p (B.opAdj Θ f)) φ
  calc II D (B.opAdj Θ (B.rho D p f)) φ = conj (II D φ (B.opAdj Θ (B.rho D p f))) := ii_swap D _ _
    _ = conj (II D (B.opApply Θ φ) (B.rho D p f)) := by
        rw [hF' φ (B.rho D p f) hφ hφc hφs (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) (hasCompactSupport_rho D hp hfc)
          (suppIn_rho D hp hfs)]
    _ = II D (B.rho D p f) (B.opApply Θ φ) := (ii_swap D _ _).symm
    _ = II D f (B.rho D p' (B.opApply Θ φ)) := hU' _ _
    _ = conj (II D (B.rho D p' (B.opApply Θ φ)) f) := ii_swap D _ _
    _ = conj (II D (B.opApply Θ (B.rho D p' φ)) f) := by rw [hcomm]
    _ = conj (II D (B.rho D p' φ) (B.opAdj Θ f)) := by
        rw [hF' (B.rho D p' φ) f (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp' hφ) (hasCompactSupport_rho D hp' hφc)
          (suppIn_rho D hp' hφs) hf hfc hfs]
    _ = II D (B.opAdj Θ f) (B.rho D p' φ) := (ii_swap D _ _).symm
    _ = II D (B.rho D p (B.opAdj Θ f)) φ := (hU' _ _).symm

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
