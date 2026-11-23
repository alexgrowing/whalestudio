import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatumStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.GaussThetaAlg

def transposeMulEquiv {A : Type} [CommRing A] {α β γ : Type} [Fintype β] [DecidableEq β] (e : γ ≃ α)
    (G H : Matrix β β A) (hHG : H * G = 1) : Matrix β γ A ≃+ Matrix α β A where
  toFun u := uᵀ.submatrix e.symm id * G
  invFun x := (x * H)ᵀ.submatrix id e
  left_inv u := by
    show ((uᵀ.submatrix e.symm id * G) * H)ᵀ.submatrix id e = u
    rw [Matrix.mul_assoc, mul_eq_one_comm.1 hHG, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    show ((x * H)ᵀ.submatrix id e)ᵀ.submatrix e.symm id * G = x
    have : ((x * H)ᵀ.submatrix id e)ᵀ.submatrix e.symm id = x * H := by
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [this, Matrix.mul_assoc, hHG, Matrix.mul_one]
  map_add' u v := by
    show (u + v)ᵀ.submatrix e.symm id * G = _
    rw [← Matrix.add_mul]
    rfl

theorem mem_algF_of_isFinF {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M)
    (B : Fr X) (f : WO M X → ℂ) (hf : IsFinF ψ θ ε A B f) : f ∈ algF ψ θ ε A B := by
  refine Submodule.subset_span ⟨f, 1, hf, ?_⟩
  show f = pureTensorL _ f 1
  have h1 : (1 : MvPolynomial (FVar D X.rank M.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp [MvPolynomial.coe_basisMonomials]
  simp only [pureTensorL]
  rw [h1, Module.Basis.constr_basis]
  simp [opPow]

theorem isFinF_thO (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ)
    (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig) (hψ : Bs.ψ = ψ)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
    (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : Vs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s')
    (hemb : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
      Ws.θ w = ((B.cart τ).submatrix e e).map conj)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ)
    (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin S.rank × Fin d → Fv D.host.F v) → ℂ) (hg : M.IsGauss Bs.ψ Bs.emb g)
    (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    IsFinF ψ θ ε A B (GlobalTheory.TripleRead.thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) := by
  classical
  have hsg : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε <;> ext i j <;> simp [sgn, HSpace.gram]
  have hdet : IsUnit ((if ε then -1 else 1 : D.host.E) • S.gram).det := by
    rw [Matrix.det_smul]
    refine IsUnit.mul (IsUnit.pow _ (by cases ε <;> simp)) ?_
    exact LatVac.gram_det_isUnit S
  have hHG : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹ *
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet]
    simp
  obtain ⟨f, hf, hD⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ ε S X A B e.symm Bs hBs hψ Vs Ws r s r' s' hJ
    (by rw [hJW]; rfl) hV hW (fun w => by
      obtain ⟨τ, h1, h2, h3⟩ := hemb w
      exact ⟨τ, h1, h2, by rw [h3]; rfl⟩) M hM
    (transposeMulEquiv e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram))
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹) hHG)
    (fun u => rfl) g φ hg hφ hvac
  convert hf using 1
  funext x
  show GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho ψ (GlobalTheory.TripleRead.ptO (sgn ε S).gram e x)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) = f x
  rw [hD.2, hsg]
  congr 1
  show (((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹)ᵀ.submatrix id e)ᵀ.submatrix e.symm id) *
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = x
  have hx : ((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹)ᵀ.submatrix id e)ᵀ.submatrix e.symm id =
      x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹ := by
    ext i j
    simp
  rw [hx, Matrix.mul_assoc, hHG, Matrix.mul_one]

theorem thO_gauss_mem_algF : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
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
        ∀ (f₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
          (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          Γ.M.IsGauss Bs.ψ Bs.emb f₀ → (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
          GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∈ algF ψ θ true A B := by
  intro _ _ D ψ θ _ hθ W W₁ X A A₁ B α β _ ωA ωB _ _ e Bs Γ Xc om om' h _ _ R Rf hm f₀ φ hg hφ hvac
  apply mem_algF_of_isFinF
  refine isFinF_thO D ψ θ hθ true W X A B e Bs hm.triple.base h.ψ Γ.V Γ.W _ _ _ _ (by rw [h.JW]; rfl) h.JX
    hm.triple.geo.hV hm.triple.geo.hW (fun w => ?_) Γ.M hm.triple.geo.hM f₀ φ hg hφ hvac
  obtain ⟨τ, h1, h2, _, h4⟩ := h.cart w
  exact ⟨τ, h1, by rw [h2]; simp, h4⟩

end GlobalTheory.GaussThetaAlg

end
