import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain

structure RowSide (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] where

  Amb : D.what₂.Tup → Type
  [instAmb : ∀ μ, NormedAddCommGroup (Amb μ)]
  [instAmbi : ∀ μ, InnerProductSpace ℂ (Amb μ)]
  [instAmbf : ∀ μ, FiniteDimensional ℂ (Amb μ)]

  Mult : D.what₂.Tup → ℕ → Type
  [instMult : ∀ μ j, NormedAddCommGroup (Mult μ j)]
  [instMulti : ∀ μ j, InnerProductSpace ℂ (Mult μ j)]
  [instMultf : ∀ μ j, FiniteDimensional ℂ (Mult μ j)]
  multZero : ∀ μ, Mult μ 0 ≃ₗᵢ[ℂ] EE
  multTop : ∀ μ, Mult μ D.R.m ≃ₗᵢ[ℂ] Amb μ

  io : ∀ μ j, Mult μ (j + 1) →ₗ[ℂ] Mult μ j

  Mtilde : ∀ μ, Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) (Amb μ)

  cen : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] Module.End ℂ (Amb μ)

  eOp : ∀ μ, Amb μ →ₗ[ℂ] Amb μ
  eOp_idem : ∀ μ, eOp μ ∘ₗ eOp μ = eOp μ
  eOp_sa : ∀ μ, (eOp μ).IsSymmetric

  eOp_tie : ∀ μ, eOp μ = (open Classical in
    if h : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) then cen μ ⟨D.ntypes.e0, h⟩ else 0)

  RR : HLat D.what₂.LL
  RR_frames : ∀ v, IsUnit (RR.X v).det

  jEE : RR.V →ₛₗ[D.what₂.embLL] EE
  jEE_basis : LinearIndependent ℂ (fun i => jEE (RR.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jEE (RR.b i))) = ⊤

  jEE_norm : ∀ x : RR.V,
    Formalism.HermitianLatticesTheory.normAt RR.b RR.X (InfinitePlace.mk D.what₂.embLL) x = ‖jEE x‖

attribute [instance] RowSide.instAmb RowSide.instAmbi RowSide.instAmbf RowSide.instMult
  RowSide.instMulti RowSide.instMultf

def DV.RhoUnit (D : D7) (ρ : D.what₂.Tup → ℝ) : Prop :=
  ∀ w : D.what₂.places.Pl, ∃ r : ℚ, (r : ℝ) = ρ (D.what₂.muAt w) ^ 2 ∧
    vAdd (D.plEq w) (r : D.what₂.LL) = 0 ∧ vAdd (D.plEq (D.what₂.places.conj w)) (r : D.what₂.LL) = 0

theorem DV.rhoUnit_one (D : D7) : DV.RhoUnit D (fun _ => 1) :=
  fun _ => ⟨1, by norm_num, by simp [vAdd], by simp [vAdd]⟩

namespace RowSide

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (S : RowSide D EE)

def downTo (μ : D.what₂.Tup) : (j : ℕ) → S.Mult μ j →ₗ[ℂ] S.Mult μ 0
  | 0 => LinearMap.id
  | j + 1 => (downTo μ j).comp (S.io μ j)

def iota (μ : D.what₂.Tup) : S.Amb μ →ₗ[ℂ] EE :=
  (S.multZero μ).toLinearEquiv.toLinearMap ∘ₗ S.downTo μ D.R.m ∘ₗ
    (S.multTop μ).symm.toLinearEquiv.toLinearMap

def thetaUp (μ : D.what₂.Tup) : EE →ₗ[ℂ] S.Amb μ := LinearMap.adjoint (S.iota μ)

def V0 (μ : D.what₂.Tup) : Submodule ℂ (S.Amb μ) := LinearMap.range (S.eOp μ)

def Usp (μ : D.what₂.Tup) : Submodule ℂ (S.Amb μ) := S.V0 μ ⊓ LinearMap.ker (S.iota μ)

def Qsp (μ : D.what₂.Tup) : Submodule ℂ (S.Amb μ) := S.V0 μ ⊓ (S.Usp μ)ᗮ

def LamSet (μ : D.what₂.Tup) : Set (S.Amb μ) :=
  (fun x => (S.Qsp μ).starProjection x) '' ((S.Mtilde μ).carrier ∩ (S.V0 μ : Set (S.Amb μ)))

def RRset (μ : D.what₂.Tup) : Set EE := S.iota μ '' S.LamSet μ

def iotaQ (μ : D.what₂.Tup) : S.Qsp μ →ₗ[ℂ] EE := (S.iota μ).domRestrict (S.Qsp μ)

def cc : Submodule (𝓞 D.what₂.LL) (Module.Dual D.what₂.LL S.RR.V) := S.RR.dualL

def RRDef : Prop :=
  ∀ x : S.RR.V, x ∈ S.RR.L ↔ ∀ w : D.what₂.places.Pl, ∃ d : 𝓞 D.what₂.LL,
    d ∉ (D.plEq w).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 D.what₂.LL) {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)}

def RRFull : Prop :=
  S.RR.L.FG ∧ Submodule.span D.what₂.LL (S.RR.L : Set S.RR.V) = ⊤

def AIntegral : Prop :=
  ∀ μ x, x ∈ (S.Mtilde μ).carrier → ((D.what₂.restRowsFiniteGroupCard : ℂ) • S.eOp μ x) ∈ (S.Mtilde μ).carrier

def OneForm : Prop := ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → S.RRset μ ⊆ Set.range S.jEE

def RowLatticeBoundForBasis {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (kap : ℝ) : Prop :=
  (∀ μ, Function.Bijective (S.iotaQ μ)) ∧ 0 < kap ∧
  ∃ ρ : D.what₂.Tup → ℝ, ρ D.what₂.mu0 = 1 ∧ (∀ μ, 0 < ρ μ) ∧ DV.RhoUnit D ρ ∧ ∀ μ (σ : Fin n),
    (S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ)) (b σ) =
      ((kap * ρ μ * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP μ j (ty σ) : ℝ) : ℂ) • b σ

def IsGramAt (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (G : D.what₂.LL) : Prop :=
  ∃ (n : ℕ) (x : Fin n → S.Amb μ), LinearIndependent ℂ x ∧
    (∀ y ∈ S.LamSet μ, ∃ d : 𝓞 D.what₂.LL, d ∉ (D.plEq w).asIdeal ∧
      d ∉ (D.plEq (D.what₂.places.conj w)).asIdeal ∧ ∃ c : Fin n → 𝓞 D.what₂.LL,
        D.what₂.embLL (d : D.what₂.LL) • y = ∑ i, D.what₂.embLL (c i : D.what₂.LL) • x i) ∧
    (∀ i, ∃ d : 𝓞 D.what₂.LL, d ∉ (D.plEq w).asIdeal ∧
      d ∉ (D.plEq (D.what₂.places.conj w)).asIdeal ∧ ∃ (T : Finset (S.Amb μ)) (c : S.Amb μ → 𝓞 D.what₂.LL),
        (T : Set (S.Amb μ)) ⊆ S.LamSet μ ∧
        D.what₂.embLL (d : D.what₂.LL) • x i = ∑ y ∈ T, D.what₂.embLL (c y : D.what₂.LL) • y) ∧
    D.what₂.embLL G = (Matrix.of fun i j => inner ℂ (x i) (x j)).det

def sharp (D : D7) : RowSide D D.what₂.EE where
  Amb := D.what₂.Amb
  Mult := D.what₂.Mult
  multZero := D.what₂.multZero
  multTop := D.what₂.multTop
  io := D.what₂.io
  Mtilde := D.what₂.Mtilde
  cen := D.ntypes.cenAmb
  eOp := D.what₂.eOp
  eOp_idem := D.what₂.eOp_idem
  eOp_sa := D.what₂.eOp_sa
  eOp_tie := fun μ => by
    rw [D.nStage_trivialCharacter_compat.1 μ]; rfl
  RR := D.div.RR
  RR_frames := D.div_good.1
  jEE := D.jEE
  jEE_basis := D.jEE_basis
  jEE_norm := D.jEE_norm

end RowSide

structure BaseLevelRowSide (D : D7) where
  s : RowSide D D.what₂.EE0

namespace BaseLevelRowSide

variable {D : D7} (X : BaseLevelRowSide D)

def principalHermitianLattice : HLat D.what₂.LL := X.s.RR

def cc0 : Submodule (𝓞 D.what₂.LL) (Module.Dual D.what₂.LL X.s.RR.V) := X.s.cc

def BaseRowLatticeFull : Prop := X.s.RRFull

def L1c0 (kap : ℝ) : Prop := X.s.RowLatticeBoundForBasis D.what₂.onb0 D.what₂.ft0 kap

end BaseLevelRowSide

def SharpLatticeBound (D : D7) (kap : ℝ) : Prop := (RowSide.sharp D).RowLatticeBoundForBasis D.what₂.onb D.what₂.ft kap

def lam0 (D : D7) : ℝ := Real.log (D.what₂.restRowsFiniteGroupCard : ℝ)

def Lemma3 (D : D7) (C : ℝ) : Prop :=
  ∃ n : D.what₂.FT → ℕ, (∀ π, D.what₂.nRows π = n π * D.what₂.nRows0 π) ∧
    (∀ π, 0 < D.what₂.nRows0 π) ∧
    (∀ π π', (∀ k, D.nd.lab k π = D.nd.lab k π') → n π = n π') ∧
    ∀ π, |(n π : ℝ) - ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (D.R.f * D.R.k)| ≤
      C * ((D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)) *
        ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (D.R.f * D.R.k)

def LemmaT (D : D7) (X : BaseLevelRowSide D) (C : ℝ) : Prop :=
  C * ((D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)) ≤ 1 / 3 →
  ∀ HH0 : ℝ, X.principalHermitianLattice.muMax ≤ HH0 →
    D.div.RR.muMax ≤ HH0 + 14 * lam0 D ∧
    D.div.RR.muDual ≤ X.principalHermitianLattice.muDual +
      3 * (C * ((D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ))) *
        (X.principalHermitianLattice.muDual + HH0 + 28 * lam0 D) + 28 * lam0 D

end Formalism.BasicNotions

end
