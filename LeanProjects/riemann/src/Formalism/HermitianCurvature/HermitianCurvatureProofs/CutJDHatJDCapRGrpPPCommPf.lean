import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PCommPf

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq]

theorem isOpen_slice {Dc : (Fin r → ℂ) → Set (Q.Mx k r)}
    (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1}) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    IsOpen (Dc c) := by
  have h := ho.preimage (continuous_const.prodMk continuous_id : Continuous (fun g : Q.Mx k r => (c, g)))
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨hc, hg⟩, fun hg => hg.2⟩

theorem tL_crd_comm (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Q.Mx k r))
    (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1})
    (hΨ : Q.SmoothFam k r i {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} Ψ) (l : Fin r) (Y : ℂ) (a b : Fin 2)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r i) (hgD : g ∈ Dc c) :
    Q.crd (pOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pOp l) Ψ) c g ∧
    Q.crd (pbOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pbOp l) Ψ) c g := by
  have hO : IsOpen (Dc c) := isOpen_slice ho hc
  have hgG : g ∈ Q.Glev k r i ∩ Dc c := ⟨hg, hgD⟩
  have hx : ((c, g) : Qx8.XX k r) ∈ Qx8.UU Dc := ⟨hc, hgD⟩
  have hcd := Qx8.cd_tL (E := Wq →L[ℂ] Wp) (i := i) (U₀ := Qx8.UU Dc) ho z z' Y a b
  have hder : ∀ s s₂ : ℂ,
      s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g +
        s₂ • Qx8.dv (Pi.single l Complex.I) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g)) =
      Q.tL k r z z' i Y a b (fun g' => s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) Ψ c g' +
        s₂ • Qx8.dv (Pi.single l Complex.I) Ψ c g'))) g := by
    intro s s₂
    rw [hcd.comm _ Ψ hΨ (c, g) hx hg, hcd.comm _ Ψ hΨ (c, g) hx hg, smul_smul]
    have := Qx8.tl_comb (z := z) (z' := z') (i := i) Formalism.FourierDecayAlt.P.transfer_linear_local hO Y a b (s * (1 / 2)) s₂
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l 1) hΨ) hc)
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l Complex.I) hΨ) hc) hgG
    rw [← this]
    simp only [smul_smul]
  refine ⟨?_, ?_⟩
  · show pOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pOp l (fun c' => Ψ c' g') c) g
    have h := hder (c l) (-Complex.I)
    simp only [pOp, if_pos hc, wirt]
    simp only [Qx8.dv, neg_smul, ← sub_eq_add_neg] at h
    exact h
  · show pbOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pbOp l (fun c' => Ψ c' g') c) g
    have h := hder (star (c l)) Complex.I
    simp only [pbOp, if_pos hc, wirtBar]
    simp only [Qx8.dv] at h
    exact h

end PCommPf

theorem residue_projection_commutation : JDRPComm := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).1

theorem crd_pbOp_QL_last_comm :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Dc : (Fin r → ℂ) → Set (Q.Mx k r)) (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} →
    Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ →
    ∀ (l : Fin r) (Y : ℂ) (a b : Fin 2), ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
      Q.crd (Formalism.QuantumDeterminants.pbOp l) (Q.QL k r z z' (Fin.last r) Y a b Ψ) c g =
        Q.QL k r z z' (Fin.last r) Y a b (Q.crd (Formalism.QuantumDeterminants.pbOp l) Ψ) c g := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).2

end Formalism.FourierDecayAlt.P.CutMP

end
