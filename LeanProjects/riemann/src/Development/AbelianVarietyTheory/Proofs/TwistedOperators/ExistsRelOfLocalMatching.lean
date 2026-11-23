import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareRel

section Rel

variable {P Q Pr : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pr] [Module ℂ Pr]

def relOf (q : P →ₗ[ℂ] Pr) (q' : Q →ₗ[ℂ] Pr) : Submodule ℂ (P × Q) :=
  LinearMap.eqLocus (q ∘ₗ LinearMap.fst ℂ P Q) (q' ∘ₗ LinearMap.snd ℂ P Q)

theorem mem_relOf {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} {x : P × Q} : x ∈ relOf q q' ↔ q x.1 = q' x.2 := Iff.rfl

theorem relOf_fst {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq' : Function.Surjective q') (a : P) : ∃ b, (a, b) ∈ relOf q q' := by
  obtain ⟨b, hb⟩ := hq' (q a)
  exact ⟨b, hb.symm⟩

theorem relOf_snd {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) (b : Q) : ∃ a, (a, b) ∈ relOf q q' := by
  obtain ⟨a, ha⟩ := hq (q' b)
  exact ⟨a, ha⟩

theorem relOf_ne_top [Nontrivial Pr] {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) : relOf q q' ≠ ⊤ := by
  intro h
  obtain ⟨y, hy⟩ := exists_ne (0 : Pr)
  obtain ⟨a, rfl⟩ := hq y
  have h1 : (a, (0 : Q)) ∈ relOf q q' := h ▸ Submodule.mem_top
  rw [mem_relOf, map_zero] at h1
  exact hy h1

end Rel

section Pol

variable {σ₁ σ₂ ν : Type} (e : σ₁ ⊕ σ₂ ≃ ν)

def polTens : MvPolynomial σ₁ ℂ ⊗[ℂ] MvPolynomial σ₂ ℂ ≃ₗ[ℂ] MvPolynomial ν ℂ :=
  ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)).equiv
    (MvPolynomial.basisMonomials ν ℂ) (Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr e).toEquiv)

theorem finsupp_sum_eq (m : σ₁ →₀ ℕ) (n : σ₂ →₀ ℕ) :
    Finsupp.domCongr e (Finsupp.sumElim m n) = m.mapDomain (e ∘ Sum.inl) + n.mapDomain (e ∘ Sum.inr) := by
  ext x
  obtain ⟨s, rfl⟩ := e.surjective x
  have h1 : Function.Injective (e ∘ Sum.inl) := e.injective.comp Sum.inl_injective
  have h2 : Function.Injective (e ∘ Sum.inr) := e.injective.comp Sum.inr_injective
  rcases s with s | s
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inl]
    rw [show e (Sum.inl s) = (e ∘ Sum.inl) s from rfl, Finsupp.mapDomain_apply h1, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu).symm
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inr]
    rw [show e (Sum.inr s) = (e ∘ Sum.inr) s from rfl, Finsupp.mapDomain_apply h2, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu)

theorem polTens_tmul (p₁ : MvPolynomial σ₁ ℂ) (p₂ : MvPolynomial σ₂ ℂ) :
    polTens e (p₁ ⊗ₜ p₂) = MvPolynomial.rename (e ∘ Sum.inl) p₁ * MvPolynomial.rename (e ∘ Sum.inr) p₂ := by
  have key : (TensorProduct.mk ℂ _ _).compr₂ (polTens e).toLinearMap =
      (LinearMap.mul ℂ (MvPolynomial ν ℂ)).compl₁₂ (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inl)).toLinearMap
        (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inr)).toLinearMap := by
    refine (MvPolynomial.basisMonomials σ₁ ℂ).ext fun m => (MvPolynomial.basisMonomials σ₂ ℂ).ext fun n => ?_
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials]
    have h : (MvPolynomial.monomial m (1 : ℂ)) ⊗ₜ[ℂ] (MvPolynomial.monomial n (1 : ℂ)) =
        ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)) (m, n) := by
      rw [Module.Basis.tensorProduct_apply, MvPolynomial.coe_basisMonomials, MvPolynomial.coe_basisMonomials]
    rw [h, polTens]
    erw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, mul_one,
      Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]
    rw [finsupp_sum_eq]
  exact LinearMap.congr_fun₂ key p₁ p₂

end Pol

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

section Route

variable {D : D7} {a b c d b' : ℕ}

def routeVar (en : Fin a ⊕ Fin c ≃ Fin d) (eb : Fin b ≃ Fin b') : FVar D a b ⊕ FVar D b c ≃ FVar D d b' where
  toFun := Sum.elim (fun v => (v.1, en (.inl v.2.1), eb v.2.2)) (fun v => (v.1, en (.inr v.2.2), eb v.2.1))
  invFun w := Sum.elim (fun x => Sum.inl (w.1, x, eb.symm w.2.2)) (fun z => Sum.inr (w.1, eb.symm w.2.2, z)) (en.symm w.2.1)
  left_inv := by rintro (⟨τ, x, y⟩ | ⟨τ, y, z⟩) <;> simp
  right_inv := by
    rintro ⟨τ, k, y⟩
    rcases h : en.symm k with x | z
    · obtain rfl := en.symm_apply_eq.1 h
      simp
    · obtain rfl := en.symm_apply_eq.1 h
      simp

def polRoute (en : Fin a ⊕ Fin c ≃ Fin d) (eb : Fin b ≃ Fin b') : PolF D a b ⊗[ℂ] PolF D b c ≃ₗ[ℂ] PolF D d b' :=
  polTens (routeVar en eb)

end Route

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : ℕ) {d b' b₁ : ℕ}

def iotaBig (en : Fin (G.V (.grid i (j + 1))).rank ⊕ Fin (G.V (.grid (i + 1) j)).rank ≃ Fin d)
    (eb : Fin (G.V (.grid (i + 1) (j + 1))).rank ≃ Fin b') :
    PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ≃ₗ[ℂ] PolF D d b' :=
  polRoute en eb

def iotaSmall (en : Fin (G.V (.grid i (j + 1))).rank ⊕ Fin (G.V (.grid (i + 1) j)).rank ≃ Fin d)
    (eb₁ : Fin (G.V (.grid i j)).rank ≃ Fin b₁) :
    PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) ≃ₗ[ℂ] PolF D d b₁ :=
  polRoute en eb₁

def squareRel (en : Fin (G.V (.grid i (j + 1))).rank ⊕ Fin (G.V (.grid (i + 1) j)).rank ≃ Fin d)
    (eb : Fin (G.V (.grid (i + 1) (j + 1))).rank ≃ Fin b') (eb₁ : Fin (G.V (.grid i j)).rank ≃ Fin b₁) {Pr : Type*}
    [AddCommGroup Pr] [Module ℂ Pr] (q : PolF D d b' →ₗ[ℂ] Pr) (q' : PolF D d b₁ →ₗ[ℂ] Pr) :
    Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) :=
  relOf (q ∘ₗ (iotaBig G i j en eb).toLinearMap) (q' ∘ₗ (iotaSmall G i j en eb₁).toLinearMap)

theorem hasInfExp_alpha {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (τ : D.what₂.Tau) {a : ℚ}
    (h : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) τ a) : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j) τ a := by
  obtain ⟨-, -, ⟨θ, hθ⟩, -⟩ := id h
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨n', hn', ho'⟩ := hL.xi_fin t'
  have h0 := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  have h0' := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t') hn' ho' τ
  have hK : ∀ s, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G s i j = (L.mu0 (j + 1) * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) * L.xi s := fun s => by
    show L.mu0 (j + 1) * L.xi s * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = _
    exact mul_right_comm _ _ _
  have e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j * (L.xi t)⁻¹ * L.xi t' := by
    rw [hK t', hK t, mul_inv_cancel_right]
  have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.Chain.StepVac.hasInfExp_mul h (GlobalTheory.Chain.StepVac.hasInfExp_inv h0)) h0'
  rw [e]
  simpa using this

end Grid

theorem nontrivial_of_tensor {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
    [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi] (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) : Nontrivial Pr := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨u, hu⟩ := exists_ne (0 : Pi)
  apply hu
  rw [← e.apply_symm_apply u, hz (e.symm u), map_zero]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7} {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
  [AddCommGroup Pi] [Module ℂ Pi]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7}

end GlobalTheory.SquareRel
