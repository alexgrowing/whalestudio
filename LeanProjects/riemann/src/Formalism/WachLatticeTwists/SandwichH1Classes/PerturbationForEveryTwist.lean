import Formalism.WachLatticeTwists.SandwichH1Classes.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

def matAct {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {r : ℕ}
    (V : Matrix (Fin r) (Fin r) R) (g0 : X →ₗ[R] X) : (Fin r → X) →ₗ[R] (Fin r → X) :=
  LinearMap.pi fun k => ∑ t, V k t • (g0 ∘ₗ LinearMap.proj t)

structure TateTr (ℓ : ℕ) [Fact ℓ.Prime] where
  Om : Type
  Oi : Type
  [cOm : CommRing Om]
  [cOi : CommRing Oi]
  [a1 : Algebra ℤ_[ℓ] Om]
  [a2 : Algebra ℤ_[ℓ] Oi]
  [a3 : Algebra Om Oi]
  [tw : IsScalarTower ℤ_[ℓ] Om Oi]
  pr : Oi →ₗ[Om] Om
  pr_alg : ∀ a, pr (algebraMap Om Oi a) = a
  g0 : Oi →ₐ[Om] Oi
  pr_comp_g_zero : ∀ y, pr (g0 y) = pr y

attribute [instance] TateTr.cOm TateTr.cOi TateTr.a1 TateTr.a2 TateTr.a3 TateTr.tw

namespace TateTr

variable {ℓ : ℕ} [Fact ℓ.Prime] (Tt : TateTr ℓ)

def Xm : Submodule Tt.Om Tt.Oi := LinearMap.ker Tt.pr

def gX : Tt.Xm →ₗ[Tt.Om] Tt.Xm :=
  Tt.g0.toLinearMap.restrict (fun y hy => by
    have : Tt.pr y = 0 := hy
    show Tt.pr (Tt.g0 y) = 0
    rw [Tt.pr_comp_g_zero, this])

def T2 (z : Tt.Om) : Prop :=
  (∀ x : Tt.Xm, z • x = 0 → x = 0) ∧ (∀ x, Tt.gX x = x → x = 0) ∧ ∀ x, ∃ y, z • x = Tt.gX y - y

def Vi {r : ℕ} (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (i : ℤ) :
    Matrix (Fin r) (Fin r) Tt.Om :=
  algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • Vmᵀ

def gmI {r : ℕ} (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (i : ℤ) :
    (Fin r → Tt.Om) →ₗ[ℤ_[ℓ]] (Fin r → Tt.Om) :=
  (matAct (Tt.Vi Vm w i) LinearMap.id).restrictScalars ℤ_[ℓ]

def gXI {r : ℕ} (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (i : ℤ) :
    (Fin r → Tt.Xm) →ₗ[ℤ_[ℓ]] (Fin r → Tt.Xm) :=
  (matAct (Tt.Vi Vm w i) Tt.gX).restrictScalars ℤ_[ℓ]

def HTdec {r : ℕ} (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) : Prop :=
  ∃ (N : ℕ) (B B' : Matrix (Fin r) (Fin r) Tt.Oi) (u : Fin r → ℤ), (∀ k, u k ∈ U) ∧
    B * B' = ((ℓ : Tt.Oi) ^ N) • (1 : Matrix (Fin r) (Fin r) Tt.Oi) ∧
    B' * B = ((ℓ : Tt.Oi) ^ N) • (1 : Matrix (Fin r) (Fin r) Tt.Oi) ∧
    ∀ k t, ∑ q, Tt.g0 (B k q) * algebraMap Tt.Om Tt.Oi (Vm q t)
      = ((w ^ (-(u k)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • B k t

end TateTr

def EqMap.comap {ℓ : ℕ} [Fact ℓ.Prime] {G G' : Type} [Group G] [Group G']
    {M : Type} [AddCommGroup M] [Module ℤ_[ℓ] M] [TopologicalSpace M]
    {M' : Type} [AddCommGroup M'] [Module ℤ_[ℓ] M'] [TopologicalSpace M']
    {a : Representation ℤ_[ℓ] G M} {a' : Representation ℤ_[ℓ] G M'} (F : EqMap a a') (p : G' →* G) :
    EqMap (a.comp p) (a'.comp p) := ⟨F.f, F.cont, fun g m => F.eqv (p g) m⟩

def StatInterInv : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] (OC : Type) [CommRing OC] [Algebra ℤ_[ℓ] OC]
    (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) (r : ℕ) (S S' : SL actO r) (Y Y' : Matrix (Fin r) (Fin r) OC),
    (∀ a : OC, (ℓ : OC) * a = 0 → a = 0) → Inter S S' Y →
    Y * Y' = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) →
    Y' * Y = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) → Inter S' S Y'

def StatInterTwist : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] (OC : Type) [CommRing OC] [Algebra ℤ_[ℓ] OC]
    (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) (r : ℕ) (S S' : SL actO r) (Y : Matrix (Fin r) (Fin r) OC)
    (χ : G →* ℤ_[ℓ]ˣ) (i : ℤ), Inter S S' Y → Inter (S.twist χ i) (S'.twist χ i) Y

def StatSLofInter : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] (OC : Type) [CommRing OC] [Algebra ℤ_[ℓ] OC]
    (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) (r : ℕ) (S' : SL actO r) (Um : G → Matrix (Fin r) (Fin r) OC)
    (Y Y' : Matrix (Fin r) (Fin r) OC),
    (∀ a : OC, (ℓ : OC) * a = 0 → a = 0) → (∀ g, Y.map (actO g) * S'.Mx g = Um g * Y) →
    Y * Y' = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) →
    Um 1 = 1 ∧ ∀ g h, Um (g * h) = (Um h).map (actO g) * Um g

def SandwichCompositeOnH1 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G G' : Type) [Group G] [Group G'] [TopologicalSpace G'] (OC : Type)
    [CommRing OC] [Algebra ℤ_[ℓ] OC] [TopologicalSpace OC] [IsTopologicalRing OC]
    [ContinuousConstSMul ℤ_[ℓ] OC]
    (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) (r : ℕ) (S S' : SL actO r) (Y Y' : Matrix (Fin r) (Fin r) OC)
    (h : Inter S S' Y) (h' : Inter S' S Y') (p : G' →* G),
    Y' * Y = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) →
    ∀ x : H1 (S'.rep.comp p), (h.eqMap.comap p).onH ((h'.eqMap.comap p).onH x) = (ℓ : ℤ_[ℓ]) • x

def PerturbationForEveryTwist : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (Tt : TateTr ℓ) (r : ℕ) (Vm : Matrix (Fin r) (Fin r) Tt.Om)
    (z z' ϖ ϖ₁ : Tt.Om) (w : ℤ_[ℓ]ˣ) (i : ℤ),
    z * z' = algebraMap ℤ_[ℓ] Tt.Om (ℓ : ℤ_[ℓ]) → ϖ * ϖ₁ = algebraMap ℤ_[ℓ] Tt.Om (ℓ : ℤ_[ℓ]) →
    IsAdicComplete (Ideal.span {ϖ}) (Fin r → Tt.Xm) → Tt.T2 z →
    (∀ a b, z * ϖ ∣ (Vm - 1) a b) → (ℓ : ℤ_[ℓ]) ^ 2 ∣ (w : ℤ_[ℓ]) - 1 →
    (∀ v, Tt.gXI Vm w i v = v → v = 0) ∧ ∀ v, ∃ y, (ℓ : ℤ_[ℓ]) • v = Tt.gXI Vm w i y - y

def StatHTW : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (Tt : TateTr ℓ) (r : ℕ) (Vm : Matrix (Fin r) (Fin r) Tt.Om)
    (w : ℤ_[ℓ]ˣ) (U : Finset ℤ),
    (∀ a : Tt.Om, (ℓ : ℤ_[ℓ]) • a = 0 → a = 0) → Tt.HTdec Vm w U →
    (∀ u ∈ U, ∀ v, Tt.gXI Vm w u v = v → v = 0) →
    ∀ i : ℤ, aeval (Tt.gmI Vm w i) (HTpoly ℓ w U i) = 0

def StatLogClass : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type) [AddCommGroup M] [Module ℤ_[ℓ] M] [TopologicalSpace M] [T2Space M] [ContinuousAdd M]
    [ContinuousSMul ℤ_[ℓ] M] (a : Representation ℤ_[ℓ] G M) (H : Subgroup G) (γ : G)
    (lg : G → ℤ_[ℓ]) (c : Z1 a) (w0 : M),
    Continuous lg → (∀ g h, lg (g * h) = lg g + lg h) → (∀ h ∈ H, lg h = 0) →
    (∀ S : Subgroup G, IsClosed (S : Set G) → H ≤ S → γ ∈ S → S = ⊤) →
    (∀ g, a g w0 = w0) → (∀ h ∈ H, c.1 h = 0) → c.1 γ = w0 →
    ∀ σ, lg γ • c.1 σ = lg σ • w0

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
