import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineExtensions
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.InvariantsVanishing
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharacterHyp
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharUnramified
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section
namespace GlobalTheory.TopSteps
open scoped LaurentSeries PowerSeries TensorProduct
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1 H2)

def Repr {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l} (F : DFun R n G) (A : Ob k G)
    (z : G → Fin A.m → k) (b g : ZMod n → Vc k A.m) : Prop :=
  ∃ (E : Ob k G) (a : (Fin A.m → k) →ₗ[k] (Fin E.m → k)) (p : (Fin E.m → k) →ₗ[k] (Fin 1 → k)) (e : Fin E.m → k)
    (ε : ZMod n → Vc k E.m), F.Obj E ∧ IsHom A E a ∧ IsHom E (chr 1) p ∧ Function.Injective a ∧
    Function.Exact a p ∧ p e = (fun _ => 1) ∧ (∀ σ, E.ρ σ e = e + a (z σ)) ∧
    ∀ i, F.map E (chr 1) p i (ε i) = F.unit i ∧
      F.map A E a i (b i) = (F.D E).φ i (ε (i - 1)) - ε i ∧ F.map A E a i (g i) = (F.D E).γ i (ε i) - ε i

def KerIs {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] (lam : O)
    (q : M →ₗ[O] N) : Prop := ∀ x, q x = 0 ↔ ∃ y, x = lam • y

def IndepMod {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (lam : O) {s : ℕ} (c : Fin s → M) : Prop :=
  ∀ x : Fin s → O, ∑ a, x a • c a = 0 → ∀ a, lam ∣ x a

variable {l : ℕ} [Fact l.Prime]

structure TopSit (P : LocPrime l) where
  K : FinExt l
  LL : FinExt l
  n : ℕ
  r : ℕ
  [nz : NeZero n]
  emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)
  D : TopData n r
  Γ : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)
  hyp : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Hyp P K LL emb D Γ

attribute [instance] TopSit.nz

namespace TopSit
variable {P : LocPrime l} (S : TopSit P)

abbrev O : Type := ↥(OL S.LL)

abbrev G : Type := ↥(GK S.K)

abbrev admitted {M : Type} [AddCommGroup M] [Module S.O M] (π : Representation S.O S.G M) : Prop :=
  Admissible (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut π

abbrev cls {M : Type} [AddCommGroup M] [Module S.O M] (W : Representation S.O S.G M) (X : Type) [AddCommGroup X]
    [Module S.O X] : Set (H1 (twCoef W S.Γ.χ₁ X) ⊤) := adm (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X

def IsRes (k : Type) [Field k] [Algebra S.O k] : Prop :=
  Function.Surjective (algebraMap S.O k) ∧ ∀ x, algebraMap S.O k x = 0 ↔ S.Γ.lam ∣ x

def Real : Prop :=
  ∀ (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k →
    ∃ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι ∧
    ∃ (F : DFun R S.n S.G) (M : ModTh F S.D), (∀ σ, (M.ω σ : k) = algebraMap S.O k (S.Γ.ε σ)) ∧
      (∃ q : ↥S.Γ.T₀.L.T →ₗ[S.O] (Fin M.T.m → k), Function.Surjective q ∧
        KerIs S.Γ.lam q ∧ ∀ σ x, q (twistRep S.Γ.W₀ S.Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x)) ∧
      ∀ (A : Ob k S.G) (N : Type) [AddCommGroup N] [Module S.O N] (π : Representation S.O S.G N)
        (e : N ≃ₗ[S.O] (Fin A.m → k)), S.admitted π → (∀ σ x, e (twistRep π S.Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) →
        ∃ L, M.Model A L

def Closed : Prop :=
  ∀ (M M' : Type) [AddCommGroup M] [Module S.O M] [AddCommGroup M'] [Module S.O M']
    (π : Representation S.O S.G M) (π' : Representation S.O S.G M'),
    (∀ f : M →ₗ[S.O] M', (∀ σ x, f (π σ x) = π' σ (f x)) →
      (Function.Injective f → S.admitted π' → S.admitted π) ∧ (Function.Surjective f → S.admitted π → S.admitted π')) ∧
    (S.admitted π → S.admitted π' → S.admitted (π.prod π'))

def CoefAdm {M : Type} [AddCommGroup M] [Module S.O M] (W : Representation S.O S.G M) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X], S.admitted (coefRep W X)

def StdAdm : Prop := S.CoefAdm S.Γ.W₀ ∧ ∀ c : ℕ, 1 ≤ c → c ≤ S.D.t → S.CoefAdm (S.Γ.Wchi c)

def Lem0 {M : Type} [AddCommGroup M] [Module S.O M] (W : Representation S.O S.G M) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (∃ A : Submodule S.O (H1 (twCoef W S.Γ.χ₁ X) ⊤), S.cls W X = A) ∧
    (∀ (a : ℕ) (ha : ∀ x : X, S.Γ.lam ^ a • x = 0), 1 ≤ a →
      S.cls W X = admAt (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X a ha) ∧
    ∀ (X' : Type) [AddCommGroup X'] [Module S.O X'] [Finite X'] (f : X →ₗ[S.O] X') (c : H1 (twCoef W S.Γ.χ₁ X) ⊤),
      (c ∈ S.cls W X → coefH1 W S.Γ.χ₁ f c ∈ S.cls W X') ∧
      (Function.Injective f → coefH1 W S.Γ.χ₁ f c ∈ S.cls W X' → c ∈ S.cls W X)

def ResBound {M : Type} [AddCommGroup M] [Module S.O M] (W : Representation S.O S.G M) (s₀ : ℕ) : Prop :=
  ∀ (s : ℕ) (c : Fin s → H1 (twCoef W S.Γ.χ₁ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK S.Γ)) ⊤),
    (∀ a, c a ∈ S.cls W (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK S.Γ)) →
    IndepMod S.Γ.lam c → s ≤ s₀

def Vanish : Prop :=
  (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep S.Γ).invariants = ⊥ ∧ Subsingleton (H2 (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep S.Γ) ⊤)

def FreeH : Prop :=
  (Module.Free S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ) ∧ Module.Finite S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ) ∧
    Module.finrank S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ) = S.r * S.n) ∧
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X], TensIso S.Γ.T₀.L S.Γ.χ₁ X

def FSummand : Prop :=
  (∃ C : Submodule S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) C) ∧
    Module.finrank S.O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) = S.D.dsum

def FinAdm : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (finiteSelmer (P.PD S.K) S.Γ.T₀.L S.Γ.χ₁ X : Set _) ⊆ S.cls S.Γ.W₀ X

def UnrAdm : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia S.Γ X (IK S.K) ⊆ S.cls (S.Γ.Wchi 1) X

def CrysCalc : Prop :=
  (∀ (T T' T'' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (U U' : ZMod S.n → Multiset ℤ) (e : T''.V ≃ₗ[↥S.LL.1] (T.V × T'.V)),
    (∀ σ x, e (T''.ρ σ x) = (T.ρ σ (e x).1, T'.ρ σ (e x).2)) → CrysWith (P.PD S.K) S.emb T.ρ U →
    CrysWith (P.PD S.K) S.emb T'.ρ U' → CrysWith (P.PD S.K) S.emb T''.ρ (fun i => U i + U' i)) ∧
  (∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (U : ZMod S.n → Multiset ℤ) (θ : S.G →* S.Oˣ) (a : ZMod S.n → ℤ),
    CrysWith (P.PD S.K) S.emb T.ρ U → IsCrysChar (P.PD S.K) S.emb θ a →
    CrysWith (P.PD S.K) S.emb (twistRep T.ρ (chiLL ↥S.LL.1 θ)) (fun i => (U i).map (· + a i)) ∧
    IsCrysChar (P.PD S.K) S.emb θ⁻¹ (fun i => -a i)) ∧
  IsCrysChar (P.PD S.K) S.emb S.Γ.ε (fun _ => -1) ∧
  ∀ μ : S.G →* S.Oˣ, (Continuous fun σ => algebraMap S.O ↥S.LL.1 (μ σ)) → (∀ σ ∈ IK S.K, μ σ = 1) →
    IsCrysChar (P.PD S.K) S.emb μ (fun _ => 0)

end TopSit
end GlobalTheory.TopSteps
