import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal

namespace GlobalTheory.TwSys

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsTameInertiaElementAtTwistPrime (i : X.Tw) (z : GE N) : Prop :=
  ∃ v ∈ X.pD i, ∃ A : ValuationSubring N.Om, IsPlaceOver A v ∧ z ∈ Ine (F := D.host.E) A ∧
    IsUnit (((X.delta i z : (X.O0 i)ˣ) : X.O0 i) ^ 2 - 1) ∧
    ∀ U : Subgroup (GE N), IsOpen (U : Set (GE N)) → U.Normal →
      ∃ n : ℕ, Nat.Coprime n (X.l i * Ideal.absNorm v.asIdeal) ∧ z ^ n ∈ U

def Over (P v : PlE D.host) : Prop := v = P ∨ IsConjPl D.host P v

def GoodChar (i : X.Tw) (M : ℕ) (P : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) : Prop :=
  IsOpen (d.ker : Set (GE N)) ∧ AntiHom X.cc d ∧ TrivAbove d (X.l i) ∧
    (∀ v, ¬ Over P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, d σ = 1) ∧
    (∀ v, Over P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ c, ∃ σ ∈ Ine (F := D.host.E) A, d σ = c)

def AdmFam (i : X.Tw) (M : ℕ) (H : Subgroup (GE N)) (S : Finset (PlE D.host))
    (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  IsOpen (H : Set (GE N)) ∧ H.Normal ∧
    (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) ∧
    ∀ P, P ∉ S → IsSplitPl D.host P → DecV N P ≤ H → GoodChar X i M P (d P)

def SlopeTestRemainingChoices (i : X.Tw) (M : ℕ) (A : Finset (PlE D.host)) {ι : Type} (P : ι → PlE D.host)
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  (∀ q v, Over (P q) v → IsSplitPl D.host v ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E v = 1 ∧
      v ∉ X.S0 i ∧ v ∉ A ∧ normV v % (2 * X.l i ^ M) = 1) ∧
    (∀ q q', Over (P q) (P q') → q = q') ∧ ∀ q, GoodChar X i M (P q) (d q)

def Steps (i : X.Tw) (M : ℕ) (H : Subgroup (GE N)) (z : GE N) {R : ℕ} (P : Fin R ⊕ Fin R → PlE D.host)
    (d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  (∀ a (σ : GE N), IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ H) ∧
    ∀ a b (σ : GE N), IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ →
      d (.inl b) σ = Multiplicative.ofAdd (if a = b then 1 else 0)

def IsQ {ι : Type} (P : ι → PlE D.host) (Q : Finset (PlE D.host)) : Prop := ∀ v, v ∈ Q ↔ ∃ q, Over (P q) v

abbrev Del (i : X.Tw) (M : ℕ) (ι : Type) : Type := Multiplicative (ι → ZMod (X.l i ^ M))

abbrev abelian₂ (i : X.Tw) (M : ℕ) (ι : Type) : Type := MonoidAlgebra (X.O0 i) (Del X i M ι)

def delAll (i : X.Tw) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) :
    GE N →* Del X i M ι where
  toFun g := Multiplicative.ofAdd fun q => Multiplicative.toAdd (d q g)
  map_one' := by simp; rfl
  map_mul' g h := by simp only [map_mul, toAdd_mul]; rfl

open Classical in

def toLam (i : X.Tw) (M : ℕ) (ι : Type) : MvPolynomial ι (X.O0 i) →ₐ[X.O0 i] abelian₂ X i M ι :=
  MvPolynomial.aeval fun q => MonoidAlgebra.of (X.O0 i) (Del X i M ι) (Multiplicative.ofAdd (Pi.single q 1)) - 1

def repOn {G O Λ : Type} [Group G] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : G →* GL (Fin r) O) (κ : G →* Λˣ)
    (B : Type) [AddCommGroup B] [Module Λ B] : Representation Λ G (Fin r → B) where
  toFun g := ((κ g : Λˣ) : Λ) • matAct ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))
  map_one' := by simp [matAct_one]
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Matrix.map_mul, matAct_mul]
    rw [smul_mul_smul_comm]

variable {X} (bkP : BKPh X)

open Classical in

def bkOn (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ]
    (κ : GE N →* Λˣ) (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    (v : PlE D.host) : Submodule Λ (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) :=
  if hv : v ∈ placesOver D.host.E (X.l i) then
    Submodule.span Λ {x | ∃ (z : Z1 ((repOn ρ κ B).comp (DecV N v).subtype))
      (c : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin r → ↥(bkP.br i v hv).LL.1)
      (y : ↥(DecV N v) → Fin r → X.O0 i) (b : B),
      c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ) ∧
      (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) ∧
      (∀ g a, (z : ↥(DecV N v) → Fin r → B) g a = algebraMap (X.O0 i) Λ (y g a) • b) ∧
      x = Submodule.Quotient.mk z}
  else ⊥

def selOn (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ]
    (κ : GE N →* Λˣ) (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    (Q : Finset (PlE D.host)) : Submodule Λ (H1 (repOn ρ κ B)) :=
  Formalism.GaloisCohomology.SelAll (repOn ρ κ B) N.plOm
    (Formalism.GaloisCohomology.bkCond (repOn ρ κ B) N.plOm (X.l i) (Spl i ∪ ↑Q) (bkOn bkP i ρ κ B))

def delInv (i : X.Tw) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) :
    GE N →* (abelian₂ X i M ι)ˣ :=
  ((MonoidAlgebra.of (X.O0 i) (Del X i M ι)).toHomUnits.comp (delAll X i M d))⁻¹

def Computes (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
    (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) : Prop :=
  ∃ e : ∀ (B : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B] [TopologicalSpace B] [DiscreteTopology B],
      (∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) →
      (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[abelian₂ X i M ι] ↥(selOn bkP i (Tgl i s) (delInv i M d) B Q)),
    ∀ (B B' : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module (abelian₂ X i M ι) B'] [TopologicalSpace B'] [DiscreteTopology B']
      (hB : ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) (hB' : ∀ b : B', ∃ n : ℕ, (X.l i ^ n) • b = 0)
      (f : B →ₗ[abelian₂ X i M ι] B') (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ)))
      (z : Z1 (repOn (Tgl i s) (delInv i M d) B)) (z' : Z1 (repOn (Tgl i s) (delInv i M d) B')),
      (∀ c, x'.1 c = f (x.1 c)) → (∀ g c, z'.1 g c = f (z.1 g c)) →
      (e B hB x).1 = Submodule.Quotient.mk z → (e B' hB' x').1 = Submodule.Quotient.mk z'

def valE (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (x : R) : ℝ≥0∞ :=
  ((IsDiscreteValuationRing.addVal R x : ℕ∞) : ℝ≥0∞) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ≥0∞)

def SelPoly (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} [Fintype ι]
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (F : MvPolynomial ι (X.O0 i)) : Prop :=
  ∀ (k : ℕ) (u : ι → (X.Ok i k)ˣ) (ψ : GE N →* (X.Ok i k)ˣ), (∀ q, u q ^ (X.l i ^ M) = 1) →
    (∀ g, ψ g = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) →
    sLen bkP i s k Q ψ =
      valE (X.Ok i k) (X.l i) (MvPolynomial.eval₂ (phiK X i k) (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) F)

def GalHyp (i : X.Tw) (s : X.Sig i) : Prop :=
  IsotypicValuationAtRing bkP i s ∧ ValuationStabilityAtRing X i s ∧ SelfDual i s ∧ NoJump bkP i s ∧ True ∧ Gen.adm3 D ∧ 100 ≤ D.R.r

end GlobalTheory.TwSys

end
