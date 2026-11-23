import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

open GlobalTheory.Grid GlobalTheory.Doubling

variable {D : D7}

def adj (S T : HSp D) (y : WO S T) : WO T S :=
  HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
    (T.gram.map (incA D))

def blkL (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V := fun a b => z (Fin.castAdd V₁.rank a) b

def blkR (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V₁ := fun a b => z (Fin.natAdd V.rank a) b

def ten (M V V₁ : HSp D) : (WO M V → ℂ) →ₗ[ℂ] (WO V₁ M → ℂ) →ₗ[ℂ] (WO M (hsum V V₁) → ℂ) :=
  LinearMap.mk₂ ℂ (fun φ φ' z => φ (blkL M V V₁ z) * φ' (adj M V₁ (blkR M V V₁ z)))
    (fun _ _ _ => funext fun _ => add_mul _ _ _) (fun _ _ _ => funext fun _ => mul_assoc _ _ _)
    (fun _ _ _ => funext fun _ => mul_add _ _ _) (fun _ _ _ => funext fun _ => mul_left_comm _ _ _)

section Route

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (V M V₁ : Node D)

abbrev Pair : Type := (WO M.V V.V → ℂ) × (WO V₁.V M.V → ℂ)

abbrev RealPart : Type := Pol M V ⊗[ℂ] Pol V₁ M

def IsFinPair (f : Pair V M V₁) : Prop := IsFinVec ψ θ ε M V f.1 ∧ IsFinVec ψ θ (!ε) V₁ M f.2

def IsAlgPair (φ : Pair V M V₁) : Prop :=
  ∃ f, IsFinPair ψ θ ε V M V₁ f ∧ ∃ P P', φ = (fock ψ θ ε M V f.1 P, fock ψ θ (!ε) V₁ M f.2 P')

def total {n : ℕ} (Φ : Fin n → Pair V M V₁) : WO M.V (hsum V.V V₁.V) → ℂ := ∑ k, ten M.V V.V V₁.V (Φ k).1 (Φ k).2

def algVec : Submodule ℂ (WO M.V (hsum V.V V₁.V) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ φ, IsAlgPair ψ θ ε V M V₁ φ ∧ Φ = ten M.V V.V V₁.V φ.1 φ.2}

def withFin (f : Pair V M V₁) : RealPart V M V₁ →ₗ[ℂ] (WO M.V (hsum V.V V₁.V) → ℂ) :=
  TensorProduct.lift (ten M.V V.V V₁.V) ∘ₗ TensorProduct.map (fock ψ θ ε M V f.1) (fock ψ θ (!ε) V₁ M f.2)

variable {V M V₁}

def route (a : ArrS M V) (b : ArrS V₁ M) (mV : V.MeasDat) (mM : M.MeasDat) {n : ℕ} (Φ : Fin n → Pair V M V₁)
    (F : GA D V.V → ℂ) : GA D V₁.V → ℂ :=
  ∑ k, b.int mM (Φ k).2 (a.int mV (Φ k).1 F)

end Route

section Quot

variable (θ : InfFam D)

def IsDer (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (Φ Φ' : Z → ℂ) : Prop :=
  ∀ z, HasDerivAt (fun t : ℝ => ρ (oneP θ X τ Y t) Φ z) (Φ' z) 0

def IsStable (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (S : Submodule ℂ (Z → ℂ)) : Prop :=
  (∀ g ∈ GfC X, ∀ Φ ∈ S, ρ g Φ ∈ S) ∧ ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∃ Φ' ∈ S, IsDer θ X ρ τ Y Φ Φ'

def IsIrred (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi) : Prop :=
  Nontrivial Pi ∧ ∀ N : Submodule ℂ Pi, (∀ g ∈ GfC X, ∀ x ∈ N, rf g x ∈ N) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, rl τ Y x ∈ N) →
    N = ⊥ ∨ N = ⊤

structure IsCoinvMap {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi) : Prop where

  stabM : IsStable θ M (fun g => ω (g, 1)) S

  stabX : IsStable θ X (fun h => ω (1, h)) S

  onto : S.map p = ⊤

  invf : ∀ g ∈ GfC M, ∀ Φ ∈ S, p (ω (g, 1) Φ) = p Φ

  invl : ∀ τ, ∀ Y ∈ lieAt M τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ M (fun g => ω (g, 1)) τ Y Φ Φ' → p Φ' = 0

  eqf : ∀ h ∈ GfC X, ∀ Φ ∈ S, p (ω (1, h) Φ) = rf h (p Φ)

  eql : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ X (fun h => ω (1, h)) τ Y Φ Φ' → p Φ' = rl τ Y (p Φ)

end Quot

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

abbrev big (i j : ℕ) : HSp D := hsum (G.V i (j + 1)).V (G.V (i + 1) j).V

variable (R) in

def al (t : T) (i j : ℕ) : (AE D)ˣ →* Circle := R.toLevCh.mu t (j + 1) * R.eta ^ (rkV D i j % 2)

def be (i j : ℕ) : (AE D)ˣ →* Circle := G.chi (D.R.m - i) * R.eta ^ (rkV D i j % 2)

structure IsMatching (t : T) (i j : ℕ) (ωA : WRep (G.V (i + 1) (j + 1)).V (big G i j)) (ωB : WRep (G.V i j).V (big G i j))
    (Pi : ModuleCat.{0} ℂ) (rf : GA D (big G i j) → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin (big G i j).rank) (Fin (big G i j).rank) ℂ → Module.End ℂ Pi)
    (p : (WO (G.V (i + 1) (j + 1)).V (big G i j) → ℂ) →ₗ[ℂ] Pi) (p' : (WO (G.V i j).V (big G i j) → ℂ) →ₗ[ℂ] Pi) : Prop where

  weilA : IsWeil R.ψ true (G.V (i + 1) (j + 1)).V (big G i j) (be G i j) (be G i j / al R t i j) ωA

  weilB : IsWeil R.ψ false (G.V i j).V (big G i j) (al R t i j) (al R t i j / be G i j) ωB

  irred : IsIrred (big G i j) Pi rf rl

  mapA : IsCoinvMap R.θ ωA (algVec R.ψ R.θ true (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j)) Pi rf rl p

  mapB : IsCoinvMap R.θ ωB (algVec R.ψ R.θ false (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j)) Pi rf rl p'

def routeA (t : T) (i j : ℕ) {n : ℕ} (Φ : Fin n → Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j))
    (F : GA D (G.V i (j + 1)).V → ℂ) : GA D (G.V (i + 1) j).V → ℂ :=
  route (G.X i (j + 1)) (G.th t (i + 1) j) (G.meas t i (j + 1)) (G.meas t (i + 1) (j + 1)) Φ F

def routeB (t : T) (i j : ℕ) {n : ℕ} (Φ : Fin n → Pair (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j))
    (F : GA D (G.V i (j + 1)).V → ℂ) : GA D (G.V (i + 1) j).V → ℂ :=
  route (G.th t i j) (G.X i j) (G.meas t i (j + 1)) (G.meas t i j) Φ F

def CommWith (t : T) (i j : ℕ) {Pi : ModuleCat.{0} ℂ} (p : (WO (G.V (i + 1) (j + 1)).V (big G i j) → ℂ) →ₗ[ℂ] Pi)
    (p' : (WO (G.V i j).V (big G i j) → ℂ) →ₗ[ℂ] Pi) (c : ℂ) : Prop :=
  ∀ (n n' : ℕ) (ΦA : Fin n → Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j))
    (ΦB : Fin n' → Pair (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j)),
    (∀ k, IsAlgPair R.ψ R.θ true _ _ _ (ΦA k)) → (∀ k, IsAlgPair R.ψ R.θ false _ _ _ (ΦB k)) →
    p (total _ _ _ ΦA) = p' (total _ _ _ ΦB) →
    ∀ (F : G.CV i (j + 1)) (v : SmT (G.V i (j + 1)).M), routeA G t i j ΦA (F.1 v) = c • routeB G t i j ΦB (F.1 v)

def MatchedExist (i j : ℕ) {Pi : ModuleCat.{0} ℂ} (p : (WO (G.V (i + 1) (j + 1)).V (big G i j) → ℂ) →ₗ[ℂ] Pi)
    (p' : (WO (G.V i j).V (big G i j) → ℂ) →ₗ[ℂ] Pi)
    (σ : RealPart (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j) →ₗ[ℂ]
      RealPart (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j)) : Prop :=
  ∀ fB, IsFinPair R.ψ R.θ false (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j) fB →
    ∃ (n : ℕ) (fA : Fin n → Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j)),
      (∀ k, IsFinPair R.ψ R.θ true _ _ _ (fA k)) ∧
      ∀ Q, p (∑ k, withFin R.ψ R.θ true _ _ _ (fA k) (σ Q)) = p' (withFin R.ψ R.θ false _ _ _ fB Q)

def SquareComm (i j : ℕ) : Prop :=
  ∃ σ, ∀ t : T, (∃ ωA ωB Pi rf rl p p', IsMatching G t i j ωA ωB Pi rf rl p p') ∧
    ∀ ωA ωB Pi rf rl p p', IsMatching G t i j ωA ωB Pi rf rl p p' →
      (∃ c : ℂ, c ≠ 0 ∧ CommWith G t i j p p' c) ∧ MatchedExist G i j p p' σ

def SquaresCommute (F : Face D A) : Prop :=
  R.Char F → G.Is → ∀ i j, i < D.R.m → j < D.R.m → SquareComm G i j

example (t : T) (i j : ℕ) : al R t i j / be G i j = R.toLevCh.mu t (j + 1) / G.chi (D.R.m - i) :=
  mul_div_mul_right_eq_div _ _ _

example (M V V₁ : HSp D) (φ : WO M V → ℂ) (φ' : WO V₁ M → ℂ) : ten M V V₁ φ φ' 0 = φ 0 * φ' 0 := by
  have h : adj M V₁ (blkR M V V₁ 0) = 0 := by
    ext a b
    simp [adj, blkR, Matrix.mul_apply]
  show φ (blkL M V V₁ 0) * φ' (adj M V₁ (blkR M V V₁ 0)) = _
  rw [h]; rfl

example (hG : G.Is) (t : T) {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (f : Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j))
    (hf : IsFinPair R.ψ R.θ true _ _ _ f) (P P') (F : G.CV i (j + 1)) (v : SmT (G.V i (j + 1)).M) :
    routeA G t i j (fun _ : Fin 1 => (fock R.ψ R.θ true _ _ f.1 P, fock R.ψ R.θ false _ _ f.2 P')) (F.1 v) =
      (G.ioT t (i + 1) j f.2 (G.ioX t i (j + 1) f.1 F)).1 ((G.th t (i + 1) j).It P' ((G.X i (j + 1)).It P v)) := by
  rw [routeA, route, Fin.sum_univ_one, (hG.lifts.X t i (j + 1) hi hj f.1 hf.1).int_eq]
  exact (hG.lifts.th t (i + 1) j hi hj f.2 hf.2).int_eq _ _ _

end GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

end
