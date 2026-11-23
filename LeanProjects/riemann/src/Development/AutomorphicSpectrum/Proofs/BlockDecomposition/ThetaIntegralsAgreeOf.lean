import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.CompanionTheory.AgreeO

variable {D : D7}

def OneSystem : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ν 𝓕 ν₁ 𝓕₁, IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
      (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
      (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) (S : Submodule ℂ (WO W₁ X → ℂ)),
      IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' ∧ S ≤ algF ψ θ false A₁ B ∧
      (∀ Φ' ∈ algF ψ θ false A₁ B, ∃ Φ₀ ∈ S, Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B)) ∧
      (∀ Φ₀ ∈ S, ModInt θ ωB ν₁ 𝓕₁ Φ₀) ∧
      ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ₀ ∈ S, p Φ = p' Φ₀ →
        thetaInt ωA ν 𝓕 Φ = c • thetaInt ωB ν₁ 𝓕₁ Φ₀

def MapsUnique : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ωA ωB Pi rf rl p p' Pi₀ rf₀ rl₀ p₀ p₀', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
      IsMatch ψ θ A A₁ B α β ωA ωB Pi₀ rf₀ rl₀ p₀ p₀' →
      ∃ s : ℂ, s ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ false A₁ B, p Φ = p' Φ' → p₀ Φ = s • p₀' Φ'

def skewJ (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) : Matrix (Fin d) (Fin d) D.host.E :=
  D.host.xi0 • reindex e e X.gramᵀ

def skewU (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (h : J = skewJ X e) (g : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J :=
  ⟨⟨reindex e e (mt X g), reindex e e (mt X g⁻¹),
    by simp only [Formalism.L2.Theta.mt, map_inv, reindex_apply, submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv],
    by simp only [Formalism.L2.Theta.mt, map_inv, reindex_apply, submatrix_mul_equiv, Units.inv_mul, submatrix_one_equiv]⟩, by
    have k : (mt X g)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ * (mt X g).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
      have := congrArg transpose (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram X g)
      rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ) := rfl
    show (reindex e e (mt X g))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (reindex e e (mt X g)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J
    rw [h, skewJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1]
    congr 1
    have e2 : (reindex e e (mt X g)).map (cA D) = reindex e e ((mt X g).map (cA D)) := rfl
    have e3 : (reindex e e (mt X g))ᵀ = reindex e e (mt X g)ᵀ := rfl
    rw [e2, e3]
    simp only [reindex_apply, submatrix_mul_equiv]
    rw [k]⟩

def ptInv (ε : Bool) (M X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (x : WO M X) : Matrix (Fin M.rank) (Fin d) (AE D) :=
  (HMul.hMul (x : Matrix (Fin X.rank) (Fin M.rank) (AE D)) (((sgn ε M).gram⁻¹).map (incA D)))ᵀ.submatrix id e.symm

def thetaOf {ε : Bool} {M X : HSp D} {d : ℕ} (e : Fin X.rank ≃ Fin d) {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ)
    (Φ : (Fin M.rank × Fin d → AF D.host.F) → ℂ) (x : WO M X) : ℂ :=
  GlobalTheory.WeilM.thetaSum D.host.F (Mo.co.rho ψ (ptInv ε M X e x) Φ)

structure IsDict {ε : Bool} {M X : HSp D} {d : ℕ} (e : Fin X.rank ≃ Fin d) (ψ : AddChar (AF D.host.F) ℂ) (ω : WRep M X)
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram)
    (hZ : Z.J = skewJ X e) : Prop where

  theta : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d), IsThetaFunO ψ (sgn ε M) X (thetaOf (ε := ε) e Mo ψ Φ)

  surj : ∀ f, IsThetaFunO ψ (sgn ε M) X f → ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d), thetaOf (ε := ε) e Mo ψ Φ = f

  inj : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d),
    thetaOf (ε := ε) e Mo ψ Φ = thetaOf (ε := ε) e Mo ψ Φ' → Φ = Φ'

  equiv : ∀ g h, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d),
    thetaOf (ε := ε) e Mo ψ (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hY g, skewU X e hZ h) Φ) = ω (g, h) (thetaOf (ε := ε) e Mo ψ Φ)

structure IsReading {W W₁ X : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  ψ : Bs.ψ = ψ

  JW : Γ.V.J = (1 : D.host.E) • W.gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • W₁.gram

  JX : Γ.W.J = skewJ X e

  cart : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Γ.V.θ w = A.cart τ ∧ Γ.V'.θ w = -A₁.cart τ ∧
    Γ.W.θ w = (reindex e e (B.cart τ)).map conj

  α : Xc.α = α

  β : Xc.β = β

  μW : Γ.M.μ = ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW)

  domW : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW '' 𝓕

  μW₁ : Γ.M'.μ = ν₁.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁)

  domW₁ : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁ '' 𝓕₁

def ReadingExists : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) ν 𝓕 ν₁ 𝓕₁, IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
      (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
      (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsReading ψ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ Bs Γ Xc),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧ IsDict (ε := true) e ψ ωA Γ.M om 1 h.JW h.JX ∧
        IsDict (ε := false) e ψ ωB Γ.M' om' (-1) h.JW₁ h.JX

end GlobalTheory.CompanionTheory.AgreeO

end
