import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.FockScal

open GlobalTheory.FockSubst

theorem foldr_scal {ι X : Type} {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop} (c : ι → ℂ)
    (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (h : ∀ i f, P f → A' i f = c i • A i f)
    {f : X → ℂ} (hf : P f) (l : List ι) :
    P (l.foldr (fun i g => A i g) f) ∧
      l.foldr (fun i g => A' i g) f = (l.map c).prod • l.foldr (fun i g => A i g) f := by
  induction l with
  | nil => simpa using hf
  | cons i l ih =>
    refine ⟨hA _ _ ih.1, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih.2, h _ _ (hsm _ _ ih.1), Asm _ _ _ ih.1, smul_smul]

theorem pure_monomial {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) (α : ι →₀ ℕ) :
    pureTensorL A f (MvPolynomial.monomial α 1) = opPow A α f := by
  unfold pureTensorL
  have := (MvPolynomial.basisMonomials ι ℂ).constr_basis ℂ (fun k : ι →₀ ℕ => opPow A k f) α
  rwa [MvPolynomial.coe_basisMonomials] at this

theorem prod_fiber {ι κ : Type} [Fintype κ] [DecidableEq κ] (g : ι → κ) (μ : κ → ℂ) (α : ι →₀ ℕ) :
    ((Finsupp.toMultiset α).toList.map fun i => μ (g i)).prod = ∏ τ, μ τ ^ (∑ v ∈ α.support with g v = τ, α v) := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add]), Finsupp.prod,
    ← Finset.prod_fiberwise (s := α.support) (g := g)]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.1 hv).2]

theorem pure_scal {ι κ X : Type} [Fintype κ] [DecidableEq κ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (g : ι → κ) (μ : κ → ℂ) (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (h : ∀ i f, P f → A' i f = μ (g i) • A i f)
    {f : X → ℂ} (hf : P f) (α : ι →₀ ℕ) :
    pureTensorL A' f (MvPolynomial.monomial α 1) =
      (∏ τ, μ τ ^ (∑ v ∈ α.support with g v = τ, α v)) • pureTensorL A f (MvPolynomial.monomial α 1) := by
  rw [pure_monomial, pure_monomial]
  unfold opPow
  rw [(foldr_scal (fun i => μ (g i)) hsm hA Asm h hf _).2, prod_fiber]

theorem unitMap_smul {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) {z : ℂ} (hz : z ≠ 0)
    (a : Fin m) (j : Fin n) : unitMap (z • B) B' a j = z⁻¹ • unitMap B B' a j := by
  have e : z • B = B * (z • (1 : Matrix (Fin n) (Fin n) ℂ)) := by simp
  have e' : (z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ = z⁻¹ • 1 :=
    Matrix.inv_eq_left_inv (by simp [smul_smul, hz])
  unfold unitMap
  rw [e, Matrix.mul_inv_rev, e']
  simp

theorem cplxO_pm {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) (a : Fin m) (j : Fin n) (u : Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t u = ((if decide (s = 1 ↔ t = 1) then 1 else -1 : ℂ) * Complex.I) • u := by
  have h1 : (-1 : Matrix (Fin n) (Fin n) ℂ) ≠ 1 := fun h => by
    have := congrFun (congrFun h j) j
    simp at this
    norm_num at this
  have h2 : (-1 : Matrix (Fin m) (Fin m) ℂ) ≠ 1 := fun h => by
    have := congrFun (congrFun h a) a
    simp at this
    norm_num at this
  unfold cplxO
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [h1, h2]

theorem pureTensorO_scal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ ζ : D.what₂.Tau → ℂ, (∀ τ, ‖ζ τ‖ = 1) → ∀ α : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T x.s y.s (fun τ => ζ τ • x.B τ) y.B f (MvPolynomial.monomial α 1) = (∏ τ, (if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (MvPolynomial.monomial α 1) := by
  intro D ψ θ hψ hθ S T x y hx hy f hf ζ hζ α
  have hz : ∀ τ, ζ τ ≠ 0 := fun τ h => by simpa [h] using hζ τ
  let μ : D.what₂.Tau → ℂ := fun τ => if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) (fun τ => ζ τ • x.B τ) y.B i g =
      μ i.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, μ]
    rw [unitMap_smul _ _ (hz ρ), aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (cplxO_pm (hx.pm ρ) (hy.pm ρ) a j _)]
    congr 1
    rw [map_inv₀, ← Complex.inv_eq_conj (hζ ρ), inv_inv]
    simp only [decide_eq_true_eq]
  have hA : ∀ i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i f) :=
    fun _ _ h => aPlus_th hψ hθ _ _ _ h
  have Asm : ∀ i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i f :=
    fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  exact pure_scal (P := IsThetaFunO ψ S T) (fun v : FVar D T.rank S.rank => v.1) μ
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) hA Asm key hf α

end GlobalTheory.FockScal
