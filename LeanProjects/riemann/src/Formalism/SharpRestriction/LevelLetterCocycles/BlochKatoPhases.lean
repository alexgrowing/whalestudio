import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.GaloisCohomology.Statement
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuInf

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal TensorProduct

namespace Formalism.MainNotions.BlochKatoReduction

instance instTopKmodO (O : Type) [CommRing O] [IsDomain O] : TopologicalSpace (Formalism.BasicNotions.KmodO O) := ⊥

instance instDiscKmodO (O : Type) [CommRing O] [IsDomain O] : DiscreteTopology (Formalism.BasicNotions.KmodO O) :=
  ⟨rfl⟩

def matAct {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : (Fin n → M) →ₗ[R] (Fin n → M) where
  toFun v i := ∑ j, A i j • v j
  map_add' v w := by ext i; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext i; simp [Finset.smul_sum, smul_comm c]

theorem matAct_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) :
    (matAct (M := M) (A * B)) = matAct A * matAct B := by
  apply LinearMap.ext; intro v; funext i
  show ∑ j, (A * B) i j • v j = ∑ k, A i k • ∑ j, B k j • v j
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem matAct_one {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ} :
    (matAct (M := M) (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  ext v i
  simp [matAct, Matrix.one_apply]

def twRep {G : Type} [Group G] {O₀ O' : Type} [CommRing O₀] [CommRing O'] [IsDomain O']
    (φ : O₀ →+* O') {r : ℕ} (ρ : G →* GL (Fin r) O₀) (χ : G →* O₀ˣ) (ψ : G →* O'ˣ) :
    Representation O' G (Fin r → Formalism.BasicNotions.KmodO O') where
  toFun g := (((ψ g)⁻¹ * (Units.map φ.toMonoidHom (χ g))⁻¹ : O'ˣ) : O') •
    matAct ((ρ g : Matrix (Fin r) (Fin r) O₀).map φ)
  map_one' := by simp [matAct_one]
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, mul_inv_rev, Matrix.map_mul, matAct_mul]
    rw [smul_mul_smul_comm]
    congr 1
    ring

def scalGL {R : Type} [CommRing R] (n : ℕ) : Rˣ →* GL (Fin n) R :=
  Units.map (Matrix.scalar (Fin n)).toMonoidHom

theorem scalGL_comm {R : Type} [CommRing R] {n : ℕ} (a : Rˣ) (A : GL (Fin n) R) :
    scalGL n a * A = A * scalGL n a := by
  apply Units.ext
  exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _

def twGL {G R : Type} [Group G] [CommRing R] {r : ℕ} (ρ : G →* GL (Fin r) R) (χ : G →* Rˣ) :
    G →* GL (Fin r) R where
  toFun g := scalGL r (χ g)⁻¹ * ρ g
  map_one' := by simp
  map_mul' g h := by
    calc scalGL r (χ (g * h))⁻¹ * ρ (g * h)
        = scalGL r (χ g)⁻¹ * (scalGL r (χ h)⁻¹ * ρ g) * ρ h := by
          rw [map_mul, map_mul, mul_inv, map_mul]; simp only [mul_assoc]
      _ = scalGL r (χ g)⁻¹ * (ρ g * scalGL r (χ h)⁻¹) * ρ h := by
          rw [scalGL_comm (χ h)⁻¹ (ρ g)]
      _ = _ := by simp only [mul_assoc]

def IsWild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : G E Ω) : Prop :=
  σ ∈ Ine (F := E) A ∧ ∀ x : Ω, x ≠ 0 → A.valuation (σ x - x) < A.valuation x

namespace Gen

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  (X : NTw D.R D.host D.what₂ D.LL0 N)

abbrev GE (N : NData D.R D.host D.what₂) : Type := G D.host.E N.Om

def phiK (i : X.Tw) (k : ℕ) : X.O0 i →+* X.Ok i k :=
  (algebraMap (X.O i) (X.Ok i k)).comp (algebraMap (X.O0 i) (X.O i))

def psiAt {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) : Γ →* A :=
  if b then ψ else ψ⁻¹

structure BKPh where
  br : ∀ (i : X.Tw) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∈ placesOver D.host.E (X.l i) →
    LocBridge (X.l i) D.host.E N.Om (Dec (F := D.host.E) (N.plOm.1 v)) (X.O0 i)

  ex : NExp D.R D.host D.what₂ D.LL0 N X

variable {X} (bkP : BKPh X)

def chiS (i : X.Tw) (s : X.Sig i) : GE N →* (X.O0 i)ˣ := X.chi1 i (X.jS i s) (X.side i s)

def goodE (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (s : X.Sig i) : Prop :=
  ∃ x : Y.Fm i (X.jS i s) (X.side i s), x ≠ 0 ∧
    MonoidAlgebra.lift (FractionRing (X.O i))
      (Module.End (FractionRing (X.O i)) (Y.Fm i (X.jS i s) (X.side i s))) (G0g N)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i (X.jS i s) (X.side i s)))
      (Y.eAlg i (X.side i s)) x = x ∧
    ∀ k P, 1 ≤ k → k ≤ D.R.r → Formalism.BasicNotions.IsSplitPl D.host P → P ∉ X.S0 i →
      Y.hkF i (X.jS i s) (X.side i s) k P x =
        algebraMap (X.O i) (FractionRing (X.O i)) (X.hEig i s k P) • x

def goodS (i : X.Tw) (s : X.Sig i) : Prop := goodE bkP.ex i s

open Classical in

def SigG (i : X.Tw) : Finset (X.Sig i) := Finset.univ.filter (goodS bkP i)

theorem mem_SigG (i : X.Tw) (s : X.Sig i) : s ∈ SigG bkP i ↔ goodS bkP i s := by
  classical
  simp [SigG]

def Trep (i : X.Tw) (s : X.Sig i) (k : ℕ) (ψ : GE N →* (X.Ok i k)ˣ) :
    Representation (X.Ok i k) (GE N) (Fin D.R.r → Formalism.BasicNotions.KmodO (X.Ok i k)) :=
  twRep (phiK X i k) (X.rhoS i s) (chiS i s) ψ

def Tgl (i : X.Tw) (s : X.Sig i) : GE N →* GL (Fin D.R.r) (X.O0 i) := twGL (X.rhoS i s) (chiS i s)

abbrev DecV (N : NData D.R D.host D.what₂) (v : HeightOneSpectrum (𝓞 D.host.E)) : Subgroup (GE N) :=
  Dec (F := D.host.E) (N.plOm.1 v)

section Loc

variable (i : X.Tw) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (X.l i))

abbrev PDv := (D.loc (X.l i)).PD (bkP.br i v hv).Kw

abbrev EmbV : Type := ↥(bkP.br i v hv).Kw.1 →ₐ[ℚ_[X.l i]] ↥(bkP.br i v hv).LL.1

abbrev repV {m : ℕ} (r : GE N →* GL (Fin m) (X.O0 i)) :=
  (bkP.br i v hv).rep (r.comp (DecV N v).subtype)

def cE (x : D.host.E) : ↥(bkP.br i v hv).Kw.1 :=
  ⟨(bkP.br i v hv).j (algebraMap D.host.E N.Om x), (bkP.br i v hv).j_E x⟩

def IsFrac (x : ↥(bkP.br i v hv).LL.1) (n d : X.O0 i) : Prop :=
  d ≠ 0 ∧ (bkP.br i v hv).toLL d * x = (bkP.br i v hv).toLL n

def IsImgK (k : ℕ) (x : ↥(bkP.br i v hv).LL.1) (y : FractionRing (X.Ok i k)) : Prop :=
  ∃ n d : X.O0 i, IsFrac bkP i v hv x n d ∧
    algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (phiK X i k d) * y =
      algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (phiK X i k n)

def dimD {m : ℕ} (r : GE N →* GL (Fin m) (X.O0 i)) (τ : EmbV bkP i v hv) : ℕ :=
  Module.finrank ↥(bkP.br i v hv).LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdRE (PDv bkP i v hv) (repV bkP i v hv r) τ)

def dimFil0 {m : ℕ} (r : GE N →* GL (Fin m) (X.O0 i)) (τ : EmbV bkP i v hv) : ℕ :=
  Module.finrank ↥(bkP.br i v hv).LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.FildR (PDv bkP i v hv) (repV bkP i v hv r) τ 0)

end Loc

def IsConjEmb (i : X.Tw) (v v' : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∈ placesOver D.host.E (X.l i)) (hv' : v' ∈ placesOver D.host.E (X.l i))
    (τ : EmbV bkP i v hv) (τ' : EmbV bkP i v' hv') : Prop :=
  ∀ (x : D.host.E) (n d : X.O0 i),
    IsFrac bkP i v' hv' (τ' (cE bkP i v' hv' x)) n d ↔ IsFrac bkP i v hv (τ (cE bkP i v hv (D.host.conj x))) n d

open Classical in

def bk (i : X.Tw) (s : X.Sig i) (k : ℕ) (ψ : GE N →* (X.Ok i k)ˣ)
    (v : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (X.Ok i k) (H1 ((Trep i s k ψ).comp (DecV N v).subtype)) :=
  if hv : v ∈ placesOver D.host.E (X.l i) then
    Submodule.span (X.Ok i k) {x | ∃ (z : Z1 ((Trep i s k ψ).comp (DecV N v).subtype))
      (c : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1)
      (y : ↥(DecV N v) → Fin D.R.r → FractionRing (X.Ok i k)),
      c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) ∧
      (∀ g a, IsImgK bkP i v hv k (c ((bkP.br i v hv).e g) a) (y g a)) ∧
      (∀ g a, (z : ↥(DecV N v) → Fin D.R.r → Formalism.BasicNotions.KmodO (X.Ok i k)) g a =
        Submodule.Quotient.mk (y g a)) ∧
      x = Submodule.Quotient.mk z}
  else ⊥

def Spl (i : X.Tw) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  ((⋃ k, placesOver D.host.E (D.host.g k)) ∪ ↑(X.pD i)) \ placesOver D.host.E (X.l i)

def selT (i : X.Tw) (s : X.Sig i) (k : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (ψ : GE N →* (X.Ok i k)ˣ) : Submodule (X.Ok i k) (H1 (Trep i s k ψ)) :=
  Formalism.GaloisCohomology.SelAll (Trep i s k ψ) N.plOm
    (Formalism.GaloisCohomology.bkCond (Trep i s k ψ) N.plOm (X.l i) (Spl i ∪ ↑Q) (bk bkP i s k ψ))

def lenN (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (M : Type)
    [AddCommGroup M] [Module R M] : ℝ≥0∞ :=
  ((Module.length R M : ℕ∞) : ℝ≥0∞) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ≥0∞)

def sLen (i : X.Tw) (s : X.Sig i) (k : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (ψ : GE N →* (X.Ok i k)ˣ) : ℝ≥0∞ :=
  lenN (X.Ok i k) (X.l i) (selT bkP i s k Q ψ)

variable (X)

def v0 (i : X.Tw) (j : ℕ) (b : Bool) : ℝ≥0∞ :=
  lenN (X.O i) (X.l i) (X.B i j b ⧸ X.Theta i j b)

def lenPsi (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (ψ : GE N →* (X.Ok i k)ˣ) : ℝ≥0∞ :=
  lenN (X.Ok i k) (X.l i) (TensorProduct (X.O i) (X.Ok i k) (X.B i j b) ⧸ X.ThetaPsi i j b k Q ψ)

def kMap (i : X.Tw) (k : ℕ) : FractionRing (X.O i) →+* FractionRing (X.Ok i k) :=
  IsFractionRing.lift (g := (algebraMap (X.Ok i k) (FractionRing (X.Ok i k))).comp
    (algebraMap (X.O i) (X.Ok i k)))
    ((IsFractionRing.injective (X.Ok i k) (FractionRing (X.Ok i k))).comp (X.Ok_inj i k))

def thEval (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (lam : X.abelian₂ i) (k : ℕ)
    (ψ : X.RCG i Q →* (X.Ok i k)ˣ) : FractionRing (X.Ok i k) :=
  ∑ δ, kMap X i k (X.th i Q lam δ) *
    algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) ((ψ δ : (X.Ok i k)ˣ) : X.Ok i k)

def nval (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (x : R) : ℝ :=
  (IsDiscreteValuationRing.addVal R x).toNat / (IsDiscreteValuationRing.addVal R (l : R)).toNat

def vK (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ)
    (x : FractionRing R) : ℝ :=
  let p := (IsLocalization.surj (nonZeroDivisors R) x).choose
  nval R l p.1 - nval R l (p.2 : R)

def c0 (i : X.Tw) (lam : X.abelian₂ i) : ℝ := vK (X.O i) (X.l i) (∑ δ, X.th i ∅ lam δ)

def tameVal {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ)
    (ψ : GE N →* Rˣ) (A : ValuationSubring N.Om) : ℝ :=
  sInf {x : ℝ | ∃ σ ∈ Ine (F := D.host.E) A, ψ σ ≠ 1 ∧ x = nval R l ((ψ σ : R) - 1)}

def TrivAbove {A : Type} [Group A] (ψ : GE N →* A) (l : ℕ) : Prop :=
  ∀ v ∈ placesOver D.host.E l, ∀ A' : ValuationSubring N.Om, IsPlaceOver A' v →
    ∀ σ ∈ Dec (F := D.host.E) A', ψ σ = 1

def NC (i : X.Tw) : Prop :=
  X.l i = 2 ∨
  (∀ P ∈ placesOver D.host.E (X.l i),
    P.asIdeal.ramificationIdx ℤ = 1) ∨
  ∃ z : N.Om, IsPrimitiveRoot z (X.l i) ∧
    D.R.t * D.R.r < Module.finrank D.host.E (IntermediateField.adjoin D.host.E {z})

def eps0 (i : X.Tw) : GE N →* (X.O0 i)ˣ :=
  (Units.map (algebraMap ℤ_[X.l i] (X.O0 i)).toMonoidHom).comp
    (cycZ (F := D.host.E) (Ω := N.Om) (X.l i))

def ind2 (l : ℕ) : ℝ := if l = 2 then 1 else 0

def nu (i : X.Tw) : ℕ :=
  KStar.Tree.nuOf (X.l i) (cycZ (F := D.host.E) (Ω := N.Om) (X.l i)) (D.R.t * D.R.r)

def QOk (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) ∧ Disjoint Q (X.S0 i) ∧
    ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def sFun (R : Ranks) : ℕ := if Odd (R.r + 6) then R.r + 6 else R.r + 7

def NFun (R : Ranks) : ℕ := R.k + R.m * (R.t + sFun R + 1)

def SOk (i : X.Tw) (lam : X.abelian₂ i) (s : ℤ) : Prop :=
  X.s2 i lam = 2 * s ∧ 1 ≤ s ∧ s ≤ (NFun D.R : ℤ) + 1

variable {X}

def Tmat (i : X.Tw) (s : X.Sig i) (g : GE N) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
  (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) •
    ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))

theorem Tgl_coe (i : X.Tw) (s : X.Sig i) (g : GE N) :
    ((Tgl i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) =
      Tmat i s g := by
  show Matrix.scalar (Fin D.R.r) _ * _ = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  rfl

def Tdual (i : X.Tw) (s : X.Sig i) (g : GE N) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
  ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • (Tmat i s g)⁻¹.transpose

def SelfDual (i : X.Tw) (s : X.Sig i) : Prop :=
  ∃ A : GL (Fin D.R.r) (X.O0 i), ∀ g g' : GE N, (∀ x, g' x = X.cc (g (X.cc.symm x))) →
    Tdual i s g' = (A : Matrix _ _ (X.O0 i)) *
      ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g) *
        ((A⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix _ _ (X.O0 i))

def NoJump (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v (hv : v ∈ placesOver D.host.E (X.l i)) (τ : EmbV bkP i v hv) (a : ℤ),
    Formalism.WeaklyAdmissibleFiltrations.IsJumpV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a → a < -1 ∨ (D.R.t : ℤ) < a

open Classical in

def PsiOk (i : X.Tw) (A Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P ∧ P.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E P = 1) ∧
    Disjoint Q (X.S0 i ∪ A) ∧ 1 ≤ k' ∧
    IsOpen ((ψ'.comp (X.art i Q)).ker : Set (GE N)) ∧
    AntiHom X.cc (ψ'.comp (X.art i Q)) ∧
    (∀ g, ψ'.comp (X.art i Q) g ∈ Subgroup.zpowers (X.zk i k')) ∧
    RamExactly (ψ'.comp (X.art i Q)) ↑Q ∧
    TrivAbove (ψ'.comp (X.art i Q)) (X.l i)

def partA (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) : Prop :=
  ∑ s ∈ SigG bkP i, sLen bkP i s k' Q (psiAt (X.side i s) (ψ'.comp (X.art i Q))) ≤
    ENNReal.ofReal (eps' + (nu X i : ℝ) * (SigG bkP i).card)

def partAT (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) : Prop :=
  ∃ epsT : X.Sig i → ℝ, (∀ s, 0 ≤ epsT s) ∧ ∑ s ∈ SigG bkP i, epsT s ≤ eps' ∧
    ∀ s, goodS bkP i s → sLen bkP i s k' Q (psiAt (X.side i s) (ψ'.comp (X.art i Q))) ≤
      ENNReal.ofReal ((nu X i : ℝ) + epsT s)

def partB (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) : Prop :=
  ∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧
    ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
    ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      lenPsi X i j b k' Q (psiAt b (ψ'.comp (X.art i Q))) ≤ v0 X i j b + ENNReal.ofReal (epsB j b)

def partC (N0 : X.Tw → ℕ) (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) : Prop :=
  ∀ lam : X.abelian₂ i, thEval X i Q lam k' (psiAt (X.sideL i lam) ψ') ≠ 0 ∧
    -(N0 i : ℝ) ≤ vK (X.Ok i k') (X.l i) (thEval X i Q lam k' (psiAt (X.sideL i lam) ψ')) ∧
    vK (X.Ok i k') (X.l i) (thEval X i Q lam k' (psiAt (X.sideL i lam) ψ')) ≤ c0 X i lam + eps'

def partD (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) : Prop :=
  (D.R.t : ℝ) * ∑ P ∈ Q, tameVal (X.l i) (ψ'.comp (X.art i Q)) (N.plOm.1 P) ≤ eps'

def SetHyp (i : X.Tw) : Prop :=
  True ∧ (∀ s, goodS bkP i s → SelfDual i s) ∧ (∀ s, goodS bkP i s → NoJump bkP i s) ∧
    (∀ lam, (∑ δ, X.th i ∅ lam δ) ≠ 0) ∧ (∀ lam, ∃ s : ℤ, SOk X i lam s) ∧ 100 ≤ D.R.r ∧
    ∀ k, 2 * D.R.r ≤ D.host.g k

def ProjectionDerivativeEstimate (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.E)),
  ∃ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A Q k' ψ' ∧ partA bkP i Q k' ψ' eps' ∧ partAT bkP i Q k' ψ' eps' ∧
    partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

def AutomorphicLevelRaisingAtTwist (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.E)),
  ∃ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A Q k' ψ' ∧ partA bkP i Q k' ψ' eps' ∧ partAT bkP i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

def AutomorphicLevelRaisingWithLevels (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.E)),
  ∃ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A Q k' ψ' ∧ partA bkP i Q k' ψ' eps' ∧ partAT bkP i Q k' ψ' eps' ∧
    partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

def aux₃ (N0 : X.Tw → ℕ) : Prop := ∀ i, X.NonzeroIndexPlace i → ProjectionDerivativeEstimate bkP N0 i

abbrev IsotypicValuationAtRing (i : X.Tw) (s : X.Sig i) : Prop :=
    (∀ v, v ∉ placesOver D.host.E (X.l i) → (∀ k, v ∉ placesOver D.host.E (D.host.g k)) →
      ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, X.rhoS i s σ = 1) ∧
    (∀ v (hv : v ∈ placesOver D.host.E (X.l i)), ∀ r ∈ ({X.rhoS i s, Tgl i s} : Set _),
      (bkP.br i v hv).IsdRW (D.loc (X.l i)) (r.comp (DecV N v).subtype) ∧
      ((∀ k, X.l i ≠ D.host.g k) →
        (bkP.br i v hv).IsCrysW (D.loc (X.l i)) (r.comp (DecV N v).subtype)) ∧
      (bkP.br i v hv).IsPotCrysW (D.loc (X.l i)) (r.comp (DecV N v).subtype)) ∧
    (∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (A : ValuationSubring N.Om), IsPlaceOver A v →
      ∀ x : Fin D.R.r → FractionRing (X.O0 i), (∀ g ∈ Dec (F := D.host.E) A,
        ((Tmat i s g).map (algebraMap (X.O0 i) (FractionRing (X.O0 i)))).mulVec x = x) → x = 0) ∧
    (∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (A : ValuationSubring N.Om), IsPlaceOver A v →
      ∀ x : Fin D.R.r → FractionRing (X.O0 i), (∀ g ∈ Dec (F := D.host.E) A,
        ((Tdual i s g).map (algebraMap (X.O0 i) (FractionRing (X.O0 i)))).mulVec x = x) → x = 0) ∧
    (∀ v v' (hv : v ∈ placesOver D.host.E (X.l i)) (hv' : v' ∈ placesOver D.host.E (X.l i))
      (τ : EmbV bkP i v hv) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' →
      dimD bkP i v hv (Tgl i s) τ + dimD bkP i v' hv' (Tgl i s) τ' =
        dimFil0 bkP i v hv (Tgl i s) τ + dimFil0 bkP i v' hv' (Tgl i s) τ' + D.R.r)

def adm1 : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ s : X.Sig i, IsotypicValuationAtRing bkP i s

variable (X) in

def rbar (i : X.Tw) (s : X.Sig i) (g : GE N) :
    Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (X.O0 i)) :=
  ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map
    (IsLocalRing.residue (X.O0 i))

variable (X) in

abbrev ValuationStabilityAtRing (i : X.Tw) (s : X.Sig i) : Prop :=
    Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) = ⊤ ∧
    ∀ k, D.host.g k ≠ X.l i → ∀ v ∈ placesOver D.host.E (D.host.g k),
      ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
        (∀ σ : GE N, IsWild A σ → rbar X i s σ = 1) ∧
        ∃ σ ∈ Ine (F := D.host.E) A,
          (rbar X i s σ - (IsLocalRing.residue (X.O0 i)
            ((chiS i s σ : (X.O0 i)ˣ) : X.O0 i)) • (1 : Matrix _ _ _)).det ≠ 0

variable (X) in

def adm2 : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ s : X.Sig i, ValuationStabilityAtRing X i s

variable (D) in

def adm3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), Formalism.MainNotions.N.bkACore ((D.loc l).PD K) ∧
    Formalism.MainNotions.LocalSituation.bkADim ((D.loc l).PD K) ∧ Formalism.MainNotions.N.bkBCore ((D.loc l).PD K)

def ArchimedeanSignatureMatching : Prop :=
  Formalism.GaloisCohomology.PTCoker ∧ Formalism.GaloisCohomology.PTSha ∧ Formalism.GaloisCohomology.TateLocalDualityH2Hypothesis ∧ Formalism.GaloisCohomology.LocalFinitenessK ∧
    Formalism.GaloisCohomology.LocalTateDualityK ∧ Formalism.GaloisCohomology.LocalEulerCharK

variable (X)

abbrev characterTwistExists (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (s : X.Sig i) : Prop :=
  goodE Y i s → ∃ η : GE N →* (X.O0 i)ˣ,
    Continuous (fun g => ((η g : (X.O0 i)ˣ) : X.O0 i)) ∧
    (∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
      ∀ σ ∈ Ine (F := D.host.E) A, ((η σ : (X.O0 i)ˣ) : X.O0 i) •
        ((X.rhoS i s σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) = 1) ∧
    (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
      (∀ σ ∈ Ine (F := D.host.E) A, ((η σ : (X.O0 i)ˣ) : X.O0 i) •
        ((X.rhoS i s σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) =
          ((X.delta i σ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ _)) ∨
      (∀ σ ∈ Ine (F := D.host.E) A, ((η σ : (X.O0 i)ˣ) : X.O0 i) •
        ((X.rhoS i s σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) =
          (((X.delta i σ)⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ _))) ∧
    ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ⁻¹ →
      ∑ k ∈ Finset.range (D.R.r + 1), (-1 : X.O i) ^ k * ((normV P : ℕ) : X.O i) ^ (k * (k - 1) / 2) *
          X.hEig i s k P =
        algebraMap (X.O0 i) (X.O i) (1 - ((η σ : (X.O0 i)ˣ) : X.O0 i) •
          ((X.rhoS i s σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))).det

def adm8 (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ s : X.Sig i, characterTwistExists X Y i s

def adm9 (N0 : X.Tw → ℕ) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk X i Q →
    ∀ (lam : X.abelian₂ i) (s : ℤ), SOk X i lam s → ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y =
      ((X.l i : ℕ) : FractionRing (X.O i)) ^ (N0 i) * X.th i Q lam δ

def eq' {K : Type} [Field K] (Y qms : K) (q : ℕ) : K :=
  (1 - Y * qms) * (1 - Y⁻¹ * qms) + ((q : K) - 1) * qms ^ 2

open Classical in

def adm10 : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk X i Q →
    ∀ (lam : X.abelian₂ i) (s : ℤ), SOk X i lam s → ∀ (P Pb : HeightOneSpectrum (𝓞 D.host.E)) (_hP : P ∈ Q) (_hPb : Pb ∈ Q),
      P ≠ Pb → IsConjPl D.host P Pb → ∀ (k : ℕ) (ψ : X.RCG i ((Q.erase P).erase Pb) →* (X.Ok i k)ˣ)
      (σ : GE N), IsFrob (N.plOm.1 P) (normV P) σ →
        thEval X i Q lam k (ψ.comp (X.res i Q ((Q.erase P).erase Pb)
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))) =
          eq' (kMap X i k (algebraMap (X.O i) (FractionRing (X.O i)) (X.Xv i lam P)) *
                algebraMap (X.Ok i k) (FractionRing (X.Ok i k))
                  ((ψ (X.art i ((Q.erase P).erase Pb) σ) : (X.Ok i k)ˣ) : X.Ok i k))
              (((normV P : ℕ) : FractionRing (X.Ok i k)) ^ (-s)) (normV P) *
            thEval X i ((Q.erase P).erase Pb) lam k ψ

def specB (i : X.Tw) (j : ℕ) (b : Bool) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k : ℕ)
    (w : X.RCG i Q → X.B i j b) (ψ : X.RCG i Q →* (X.Ok i k)ˣ) : X.Ok i k ⊗[X.O i] X.B i j b :=
  ∑ δ, ((ψ δ : (X.Ok i k)ˣ) : X.Ok i k) ⊗ₜ[X.O i] w δ

def PqOp (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (Y : X.Ok i k) :
    Module.End (X.Ok i k) (X.Ok i k ⊗[X.O i] X.B i j b) :=
  ∑ n ∈ Finset.range (D.R.r + 1),
    ((-1 : X.Ok i k) ^ n * ((normV P : ℕ) : X.Ok i k) ^ (n * (n - 1) / 2) * Y ^ n) •
      (X.hk i j b n P).baseChange (X.Ok i k)

def ClassQ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  ∀ P ∈ Q, ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal)

open Classical in

def admB : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
  ∃ (n : ℕ) (w : ∀ Q : Finset (HeightOneSpectrum (𝓞 D.host.E)), Fin n → X.RCG i Q → X.B i j b)
    (ch : Set (HeightOneSpectrum (𝓞 D.host.E))) (sg : Bool),
    (∀ P P', IsConjPl D.host P P' → P ≠ P' → (P ∈ ch ↔ P' ∉ ch)) ∧
    LinearIndependent (X.O i) (fun a => ∑ δ, w ∅ a δ) ∧
    Submodule.span (X.O i) (Set.range fun a => ∑ δ, w ∅ a δ) = X.Theta i j b ∧
    (∀ Q, QOk X i Q → ClassQ (D := D) Q → ∀ (k : ℕ) (ψ : X.RCG i Q →* (X.Ok i k)ˣ),
      RamExactly (ψ.comp (X.art i Q)) ↑Q → TrivAbove (ψ.comp (X.art i Q)) (X.l i) →
      ∀ a, specB X i j b Q k (w Q a) ψ ∈ X.ThetaPsi i j b k Q (ψ.comp (X.art i Q))) ∧
    (∀ Q, QOk X i Q → ClassQ (D := D) Q → ∀ (P Pb : HeightOneSpectrum (𝓞 D.host.E)) (_hP : P ∈ Q) (_hPb : Pb ∈ Q),
      P ≠ Pb → IsConjPl D.host P Pb → P ∈ ch →
      ∀ (k : ℕ) (ψ : X.RCG i ((Q.erase P).erase Pb) →* (X.Ok i k)ˣ),
      TrivAbove (ψ.comp (X.art i ((Q.erase P).erase Pb))) (X.l i) →
      ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∀ a,
        specB X i j b Q k (w Q a) (ψ.comp (X.res i Q ((Q.erase P).erase Pb)
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))) =
          PqOp X i j b k P ((psiAt sg ψ (X.art i ((Q.erase P).erase Pb) σ) : (X.Ok i k)ˣ) : X.Ok i k)
            (specB X i j b ((Q.erase P).erase Pb) k (w ((Q.erase P).erase Pb) a) ψ))

variable {X}

def AdmACD (N0 : X.Tw → ℕ) : Prop :=
  adm1 bkP ∧ adm2 X ∧ adm3 D ∧ ArchimedeanSignatureMatching ∧ adm9 X N0 ∧ adm10 X

def admitted (N0 : X.Tw → ℕ) : Prop :=
  adm1 bkP ∧ adm2 X ∧ adm3 D ∧ ArchimedeanSignatureMatching ∧ adm8 X bkP.ex ∧ adm9 X N0 ∧ adm10 X ∧ admB X ∧ X.SigSpan

def Stmt : Prop := ∀ N0 : X.Tw → ℕ, admitted bkP N0 → aux₃ bkP N0

def SelmerBoundFromLocalInputs : Prop := ∀ N0 : X.Tw → ℕ, AdmACD bkP N0 → ∀ i, X.NonzeroIndexPlace i → AutomorphicLevelRaisingWithLevels bkP N0 i

end Gen

variable (D : Formalism.BasicNotions.D7)

abbrev BK := Gen.BKPh D.ntw

def bk0 : BK D := ⟨D.ntwbr, D.nexp⟩

variable {D} in

def pin (bkP : BK D) : BK D := ⟨bkP.br, D.nexp⟩

def SigGood : Prop := ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i), Gen.goodS (bk0 D) i s

variable {D} in

def adm1 (bkP : BK D) : Prop := Gen.adm1 bkP

def adm2 : Prop := Gen.adm2 D.ntw

def adm3 : Prop := Gen.adm3 D

def ArchimedeanSignatureMatching : Prop := Gen.ArchimedeanSignatureMatching

def adm8 : Prop := Gen.adm8 D.ntw D.nexp

def adm9 (N0 : D.ntw.Tw → ℕ) : Prop := Gen.adm9 D.ntw N0

def adm10 : Prop := Gen.adm10 D.ntw

def admB : Prop := Gen.admB D.ntw

def EigenvectorSpanning : Prop := D.ntw.SigSpan

def admitted (bkP : BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  adm1 bkP ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching ∧ adm8 D ∧ adm9 D N0 ∧ adm10 D ∧ admB D ∧ EigenvectorSpanning D

def AdmACD (bkP : BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  adm1 bkP ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching ∧ adm9 D N0 ∧ adm10 D

def aux₃ (bkP : BK D) (N0 : D.ntw.Tw → ℕ) : Prop := Gen.aux₃ (pin bkP) N0

def LevelRaisingFamilyWithLevels (bkP : BK D) (N0 : D.ntw.Tw → ℕ) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → Gen.AutomorphicLevelRaisingWithLevels (pin bkP) N0 i

def LevelRaisingFamily (bkP : BK D) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → Gen.AutomorphicLevelRaisingAtTwist (pin bkP) i

def Stmt (bkP : BK D) : Prop := ∀ N0 : D.ntw.Tw → ℕ, admitted D bkP N0 → aux₃ D bkP N0

def SelmerBoundFromLocalInputs (bkP : BK D) : Prop := ∀ N0 : D.ntw.Tw → ℕ, AdmACD D bkP N0 → LevelRaisingFamilyWithLevels D bkP N0

end Formalism.MainNotions.BlochKatoReduction

end
