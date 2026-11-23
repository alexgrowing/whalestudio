import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerGenericEigenFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogPole

theorem ksMatrix_eq_zero_of_ne_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → Θ a b = 0 := by
  intro E _ _ _ H Dw l Xo c TF U n e v hv D Θ hKS i k hik
  obtain ⟨htan, huq, heig⟩ := hv
  let A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1) :=
    fun x => Matrix.diagonal fun j => algX TF.Y.s U.1 (embK c (e.symm j).1 x)
  have hA : ∀ x j, IsCombAtG TF.Y.t (LogKS.chart U) v (A x j) (v j ≫ (TF.Y.t.act.act x).left) := by
    intro x j
    have h := heig x (e.symm j).1 (e.symm j).2
    simp only [Sigma.eta, Equiv.apply_symm_apply] at h
    convert h using 2
    funext m
    simp only [A, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  obtain ⟨e', he'⟩ := TF.logKS U n v A htan huq hA
  have hmem : Θ ∈ LogKS.balanced H.bar A := by
    rw [(he' D Θ).1 hKS]
    exact (e' D).2
  have hd := ((LogKS.mem_balanced_diagonal H.bar
    (fun j x => algX TF.Y.s U.1 (embK c (e.symm j).1 x)) Θ).1 hmem).2
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, embK c (e.symm i).1 x ≠ embK c ((starRingEnd ℂ).comp (e.symm k).1) x := by
    by_contra hcon
    push_neg at hcon
    apply hik
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext y
    have h := congrArg (fun z : c.F => (z : ℂ)) (hcon y)
    simpa [embK_coe, conjEmb] using h
  have hu : IsUnit (algX TF.Y.s U.1 (embK c (e.symm i).1 x) -
      algX TF.Y.s U.1 (embK c (e.symm k).1 (H.bar x))) := by
    rw [GlobalTheory.LogKSDiv.GenKSProof.embK_bar', ← map_sub]
    exact (IsUnit.mk0 _ (sub_ne_zero.2 hx)).map _
  exact hu.mul_right_eq_zero.1 (hd x i k)

end GlobalTheory.LogPole
