import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.FilteredPoleLength.ReducedBasisBounds.GradedFreeLengthFiltered
import Formalism.FilteredPoleLength.ReducedBasisBounds.BetaSesquilinearity

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

abbrev WL (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) :
    Submodule (X.Kl la) (X.Vl la) :=
  X.locK la (X.Msup ka)

def inW (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO))
    (N : Submodule (X.Ol la) (X.Vl la)) : Submodule (X.Ol la) ↥(WL X ka la) :=
  N.comap ((WL X ka la).subtype.restrictScalars (X.Ol la))

def MW (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) :
    Submodule (X.Ol la) ↥(WL X ka la) :=
  inW X ka la (X.loc la (X.Msup ka))

def ThW (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) : Submodule (X.Ol la) ↥(WL X ka la) :=
  inW X ka la (X.loc la (X.Theta S ka wL wF T))

structure LocDat (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) where

  O' : Type
  K' : Type
  V₁ : Type
  [iO : CommRing O']
  [dO : IsDomain O']
  [vO : IsDiscreteValuationRing O']
  [aO : Algebra (X.Ol la) O']
  [fK : Field K']
  [aOK : Algebra O' K']
  [frK : IsFractionRing O' K']
  [aKK : Algebra (X.Kl la) K']
  [aOlK : Algebra (X.Ol la) K']
  [st1 : IsScalarTower (X.Ol la) (X.Kl la) K']
  [st2 : IsScalarTower (X.Ol la) O' K']
  [gV : AddCommGroup V₁]
  [mKV : Module K' V₁]
  [mOV : Module O' V₁]
  [st3 : IsScalarTower O' K' V₁]
  [mKlV : Module (X.Kl la) V₁]
  [st4 : IsScalarTower (X.Kl la) K' V₁]

  bc : ↥(WL X ka la) →ₗ[X.Kl la] V₁

  ϖ : X.Ol la

  K₁ : Type
  [fK₁ : Field K₁]
  [aK₁ : Algebra K' K₁]
  [fdK₁ : FiniteDimensional K' K₁]
  [sK₁ : Algebra.IsSeparable K' K₁]
  [aOK₁ : Algebra O' K₁]
  [st5 : IsScalarTower O' K' K₁]

  ι : Type
  [fι : Fintype ι]
  y : ι → X.Pt la

  ν : ι → ℝ
  ep : ι → ℕ
  f : ι → ℕ

  R : ℕ
  I : ℕ

  N₁ : Submodule O' V₁
  Z : Submodule O' V₁
  Zm : Submodule O' V₁
  N' : Submodule O' V₁

  n : ℕ
  be : ℕ
  th : Fin n → V₁
  c : V₁ →ₗ[K'] (Fin n → K₁)

  Wsec : Type
  [gWs : AddCommGroup Wsec]
  [mWs : Module O' Wsec]
  AA : Submodule O' Wsec
  AA' : Submodule O' Wsec
  N₁' : Submodule O' Wsec
  ρ : ↥N' →ₗ[O'] Wsec

  a : O'
  a' : O'

  Rr : ι → Type
  Aq : ι → Type
  [rR : ∀ z, CommRing (Rr z)]
  [lR : ∀ z, IsLocalRing (Rr z)]
  [aR : ∀ z, Algebra O' (Rr z)]
  [hR : ∀ z, IsLocalHom (algebraMap O' (Rr z))]
  [gA : ∀ z, AddCommGroup (Aq z)]
  [mRA : ∀ z, Module (Rr z) (Aq z)]
  [mOA : ∀ z, Module O' (Aq z)]
  [sRA : ∀ z, IsScalarTower O' (Rr z) (Aq z)]
  xq : ∀ z, Rr z
  nq : ι → ℕ
  Fq : ∀ z, ℕ → Submodule (Rr z) (Aq z)
  rq : ι → ℕ → ℕ

  A0 : Type
  [S_units_euler_difference : AddCommGroup A0]
  [multiplicityBound : Module O' A0]
  n1 : ℕ
  F1 : ℕ → Submodule O' ↥AA
  ι1 : Type
  [fι1 : Fintype ι1]
  [dι1 : DecidableEq ι1]
  deg : ι1 → ℕ
  δ : ℕ
  t : Fin δ → A0
  σ : ∀ k, ↥(F1 k) →ₗ[O'] ({α : ι1 // deg α = k} → A0)
  u : ι1 → Fin δ → ↥AA

attribute [instance] LocDat.iO LocDat.dO LocDat.vO LocDat.aO LocDat.fK LocDat.aOK LocDat.frK LocDat.aKK
  LocDat.aOlK LocDat.st1 LocDat.st2 LocDat.gV LocDat.mKV LocDat.mOV LocDat.st3 LocDat.mKlV LocDat.st4
  LocDat.fK₁ LocDat.aK₁ LocDat.fdK₁ LocDat.sK₁ LocDat.aOK₁ LocDat.st5 LocDat.fι LocDat.gWs LocDat.mWs
  LocDat.rR LocDat.lR LocDat.aR LocDat.hR LocDat.gA LocDat.mRA LocDat.mOA LocDat.sRA LocDat.S_units_euler_difference LocDat.multiplicityBound
  LocDat.fι1 LocDat.dι1

namespace LocDat

variable {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {la : HeightOneSpectrum (𝓞 B.KO)} (L : LocDat X ka la)

def up (N : Submodule (X.Ol la) ↥(WL X ka la)) : Submodule L.O' L.V₁ :=
  Submodule.span L.O' (L.bc '' (N : Set ↥(WL X ka la)))

def v (z : L.ι) : ℝ := X.phiC la (L.y z)

def mm (T e : ℕ) (z : L.ι) : ℕ := (max 0 ⌈(L.ep z : ℝ) * ((T : ℝ) * L.ν z - (e : ℝ))⌉).toNat

def err (T : ℕ) (cc : ℝ) : ℝ :=
  (L.R : ℝ) * ((T : ℝ) * cc * ∑ z, ((L.ep z : ℝ) * L.f z) * L.v z) + (L.R : ℝ) * (L.I : ℝ) +
    ((Module.length L.O' (↥L.Zm ⧸ L.Z.comap L.Zm.subtype)).toNat : ℝ) +
    (((IsDiscreteValuationRing.addVal L.O' L.a).toNat : ℝ) -
        ((IsDiscreteValuationRing.addVal L.O' L.a').toNat : ℝ) +
        (finrank L.K' L.K₁ : ℝ) * (L.n : ℝ) * (L.be : ℝ)) / (finrank L.K' L.K₁ : ℝ)

def _root_.Formalism.MainNotions.Gaps.T0.InLat (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO))
    (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  Formalism.LatticeIndexTer.IsLat (X.Ol la) (X.Kl la) ↥(WL X ka la) (MW X ka la) ∧
    Formalism.LatticeIndexTer.IsLat (X.Ol la) (X.Kl la) ↥(WL X ka la) (ThW X S ka wL wF T la)

def InExt : Prop :=
  IsBaseChange L.K' L.bc ∧ Irreducible L.ϖ ∧ Irreducible (algebraMap (X.Ol la) L.O' L.ϖ)

def InTie (S : Scal B) (wL : WeightFamilies.Wt D j) : Prop :=
  ∀ z, X.depth S.sW wL la (L.y z) = ((L.ν z : ℝ) : EReal) ∧ (∃ m : ℤ, (L.ep z : ℝ) * L.ν z = m) ∧
    1 ≤ L.ep z ∧ 0 ≤ L.v z

def InRes (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T e : ℕ) : Prop :=
  L.N₁ ⊔ L.Z ≤ L.up (ThW X S ka wL wF T la) ∧ (∀ i, L.th i ∈ L.up (MW X ka la)) ∧
    (∀ i, L.th i ∈ L.up (ThW X S ka wL wF T la)) ∧
    LinearMap.ker L.c ≤ Submodule.span L.K' ((L.N₁ ⊔ L.Z : Submodule L.O' L.V₁) : Set L.V₁) ∧
    LinearMap.ker L.c ⊔ Submodule.span L.K' (Set.range L.th) = ⊤ ∧
    (∀ x ∈ L.up (MW X ka la), ∀ i, ∃ w ∈ integralClosure L.O' L.K₁,
      L.c x i = (algebraMap L.O' L.K₁ (algebraMap (X.Ol la) L.O' L.ϖ)) ^ (-(L.be : ℤ)) * w) ∧
    L.a ≠ 0 ∧ L.a' ≠ 0 ∧
    algebraMap L.O' L.K' L.a =
      Algebra.norm L.K' (Matrix.of fun i k => L.c (L.th k) i).det * algebraMap L.O' L.K' L.a' ∧
    (L.up (MW X ka la)).map ((algebraMap (X.Ol la) L.O' L.ϖ ^ e) • (LinearMap.id : L.V₁ →ₗ[L.O'] L.V₁)) ⊓
      (Submodule.span L.K' ((L.N₁ ⊔ L.Z : Submodule L.O' L.V₁) : Set L.V₁)).restrictScalars L.O' ≤ L.N' ∧
    L.N₁ ≤ L.N' ∧ L.Z ≤ L.Zm ∧ L.Zm ≤ L.N' ∧ (∀ x, L.ρ x ∈ L.AA') ∧
    LinearMap.ker L.ρ = L.Zm.comap L.N'.subtype ∧ (L.N₁.comap L.N'.subtype).map L.ρ = L.N₁' ∧
    L.N₁' ≤ L.AA ∧ L.AA ≤ L.AA' ∧ Module.length L.O' (↥L.Zm ⧸ L.Z.comap L.Zm.subtype) ≠ ⊤

def InPts (T e : ℕ) : Prop :=
  (∀ z, L.Fq z 0 = ⊤) ∧ (∀ z, L.Fq z (L.nq z) = ⊥) ∧ (∀ z k, k < L.nq z → L.Fq z (k + 1) ≤ L.Fq z k) ∧
    (∀ z k, k < L.nq z → ∀ w ∈ L.Fq z k, L.xq z • w ∈ L.Fq z (k + 1) → w ∈ L.Fq z (k + 1)) ∧
    (∀ z k, k < L.nq z →
      Module.length (L.Rr z)
          (↥(L.Fq z k) ⧸ (L.Fq z (k + 1) ⊔ (L.Fq z k).map
            ((L.xq z ^ L.mm T e z) • (LinearMap.id : L.Aq z →ₗ[L.Rr z] L.Aq z))).comap (L.Fq z k).subtype) =
        ((L.rq z k * L.mm T e z : ℕ) : ℕ∞)) ∧
    (∀ z, ∑ k ∈ Finset.range (L.nq z), L.rq z k = L.R) ∧
    (∀ z, Module.length (IsLocalRing.ResidueField L.O') (IsLocalRing.ResidueField (L.Rr z)) = (L.f z : ℕ∞)) ∧
    Nonempty ((↥L.AA' ⧸ L.AA.comap L.AA'.subtype) ≃ₗ[L.O']
      ((z : L.ι) → L.Aq z ⧸ (⊤ : Submodule (L.Rr z) (L.Aq z)).map
        ((L.xq z ^ L.mm T e z) • (LinearMap.id : L.Aq z →ₗ[L.Rr z] L.Aq z))))

def InLead : Prop :=
  L.F1 0 = ⊤ ∧ L.F1 L.n1 = ⊥ ∧ (∀ k, L.F1 (k + 1) ≤ L.F1 k) ∧
    (∀ k, LinearMap.ker (L.σ k) = (L.F1 (k + 1)).comap (L.F1 k).subtype) ∧
    (∀ k, Function.Surjective (L.σ k)) ∧ (∀ α, L.deg α < L.n1) ∧
    (∀ α i, ∃ h : L.u α i ∈ L.F1 (L.deg α), L.σ (L.deg α) ⟨L.u α i, h⟩ = Pi.single ⟨α, rfl⟩ (L.t i)) ∧
    LinearIndependent L.O' L.t ∧
    L.N₁'.comap L.AA.subtype = Submodule.span L.O' (Set.range fun p : L.ι1 × Fin L.δ => L.u p.1 p.2) ∧
    Fintype.card L.ι1 = L.R ∧
    Module.length L.O' (L.A0 ⧸ Submodule.span L.O' (Set.range L.t)) = (L.I : ℕ∞)

def Ok (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T e : ℕ) : Prop :=
  InLat X ka la S wL wF T ∧ L.InExt ∧ L.InTie S wL ∧ L.InRes S wL wF T e ∧ L.InPts T e ∧ L.InLead

end LocDat

def Thm0Local : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) (e : ℕ),
    H1 large₂ X H S wL nus → 1 ≤ T → 0 ≤ cc D large₂ H.Cc H.Ac H.CRc wL →
    X.Theta S ka wL wF T ≤ X.Msup ka →
    (T : ℝ) * nus la ≤ (e : ℝ) →
    ∀ L : LocDat X ka la, L.Ok S wL wF T e →
    ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
      X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
          (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
          (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
        (e : ℝ) * (finrank (X.Kl la) V' : ℝ) + L.err T (cc D large₂ H.Cc H.Ac H.CRc wL)

def Thm0Concl : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) (r : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    H1 large₂ X H S wL nus → 1 ≤ T → 0 ≤ cc D large₂ H.Cc H.Ac H.CRc wL →
    X.Theta S ka wL wF T ≤ X.Msup ka →
    (∀ la, 0 ≤ r la) → Summable (fun la => r la * X.lN la) → (∑' la, r la * X.lN la) ≤ β →
    (∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∃ L : LocDat X ka la, L.Ok S wL wF T e ∧ L.err T (cc D large₂ H.Cc H.Ac H.CRc wL) ≤ r la) →
    Concl X S ka wL wF T nus β

end Formalism.MainNotions.Gaps.T0
