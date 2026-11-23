import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicVectorsCorrespondSchrodingerThetaMapStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DarbImageRevB

variable {D : D7}

theorem incM_mul {m : ℕ} (G H : Matrix (Fin m) (Fin m) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D := D) (G * H) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM H :=
  Matrix.map_mul

theorem incM_one {m : ℕ} : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D := D) (1 : Matrix (Fin m) (Fin m) D.host.E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def crd {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d) :
    Matrix (Fin m) (Fin k) (AE D) ≃+ Matrix (Fin d) (Fin m) (AE D) where
  toFun u := HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)
  invFun x := GlobalTheory.TripleRead.ptO G e x
  left_inv u := by
    simp only [GlobalTheory.TripleRead.ptO]
    rw [Matrix.mul_assoc, ← incM_mul, Matrix.mul_nonsing_inv _ hG, incM_one, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have e1 : ((GlobalTheory.TripleRead.ptO G e x)ᵀ.submatrix e.symm id) = HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    simp only [e1]
    rw [Matrix.mul_assoc, ← incM_mul, Matrix.nonsing_inv_mul _ hG, incM_one, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

theorem exists_darbAlg_thO_eq_fockF : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∀ (g : WO W₁ X → ℂ) (P : PolF D X.rank W₁.rank), IsFinF ψ θ false A₁ B g →
          ∃ Φ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb, GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Φ = fockF ψ θ false A₁ B g P := by
  intro _ _ D ψ θ _ hθ W W₁ X A A₁ B α β _ ωA ωB _ _ e Bs Γ Xc om om' h _ _ R Rf hM g P hg
  have hG : IsUnit W₁.gram.det := (Formalism.L2.Theta.gram_det_ne W₁).isUnit
  have key := (GlobalTheory.T.algebraicVectors_correspond_schrodinger_thetaMap D ψ θ hθ false W₁ X A₁ B e.symm Bs hM.triple.base h.ψ Γ.V' Γ.W _ _ _ _
    (by simpa using h.JW₁) (by rw [h.JX]; rfl) hM.triple.geo.hV' hM.triple.geo.hW
    (fun w => by
      obtain ⟨τ, h1, -, h2, h3⟩ := h.cart w
      exact ⟨τ, h1, by simpa using h2, by rw [h3]; rfl⟩)
    Γ.M' hM.triple.geo.hM' (crd W₁.gram hG e) (fun u => by simp [crd])).1
  obtain ⟨Φ, hΦ, hd⟩ := key (fockF ψ θ false A₁ B g P) (Submodule.subset_span ⟨g, P, hg, rfl⟩)
  refine ⟨Φ, hΦ, funext fun x => ?_⟩
  have h2 := hd.2 ((crd W₁.gram hG e).symm x)
  rw [AddEquiv.apply_symm_apply] at h2
  exact h2

end GlobalTheory.DarbImageRevB

end
