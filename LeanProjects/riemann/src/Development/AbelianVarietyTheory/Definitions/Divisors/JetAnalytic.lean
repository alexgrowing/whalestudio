import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

abbrev Idx (I : Type) [Fintype I] (n : ℕ) : Type := {ν : I → ℕ // ∑ i, ν i ≤ n + 1}

structure JetRing (R : Type) [CommRing R] (I : Type) [Fintype I] (n : ℕ) where

  B : Type
  [cr : CommRing B]
  [alg : Algebra R B]

  b : Module.Basis (Idx I n) R B

  one : b ⟨0, by simp⟩ = 1

  mul : ∀ ν ν' : Idx I n, b ν * b ν' =
    if h : ∑ i, (ν.1 + ν'.1) i ≤ n + 1 then (∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i)) • b ⟨ν.1 + ν'.1, h⟩ else 0

  π : B →+* R

  π_eq : ∀ x, π x = b.repr x ⟨0, by simp⟩

  κ : DividedPowers (RingHom.ker π)

  nil : IsNilDP κ

attribute [instance] JetRing.cr JetRing.alg

def JetRing.t {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (i : I) : J.B :=
  J.b ⟨Pi.single i 1, by simp⟩

section Alg

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

def admitted (X : Obj F 𝔠 (Sp R)) (N : I → Module.End R (HdR X.A)) : Prop :=
  (∀ i (a : 𝓞 F), Commute (N i) (act (dp0 R) (𝟙 _) X.rm a)) ∧ (∀ i j, N i * N j = 0) ∧
    ∀ (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)), IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ →
      (∀ i x y, ψ (N i x) y + ψ x (N i y) = 0) ∧ ∀ i j x y, ψ (N i x) (N j y) = 0

def IsJetElt (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) (N : I → Module.End R (HdR X.A))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A)))
    (x : HdR X.A) (d : Crys J.κ (spMap J.π) X.A) : Prop :=
  ∀ c, d (m.pull c) = algebraMap R J.B (x c) + ∑ i, J.t i * algebraMap R J.B (N i x c)

structure Family (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) (N : I → Module.End R (HdR X.A)) where

  X' : Obj F 𝔠 (Sp J.B)

  i : X.A.left ⟶ X'.A.left

  pull : X.IsPullBy X' (spMap J.π) i

  mor : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))

  δ' : X'.DetGen

  fil : ∀ x ∈ Fil X.A, ∀ d, IsJetElt J X N mor x d → d ∈ liftFil J.κ pull.grp

  gen : ∀ (x : Fin (Module.finrank ℚ F) → HdR X.A) (d : Fin (Module.finrank ℚ F) → Crys J.κ (spMap J.π) X.A)
    (v : Fin (Module.finrank ℚ F) → X.Lie) (v' : Fin (Module.finrank ℚ F) → X'.Lie),
    (∀ j, IsJetElt J X N mor (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧ IsLieImage (crysToDR J.κ pull.grp (d j)) (v' j).hom) →
      δ'.1 v' = algebraMap R J.B (δ.1 v)

end Alg

abbrev FR (E : Type) [Field E] : Type := maximalRealSubfield E

section Cx

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)}

structure Unif (φ : I → E →+* ℂ) (L : Set E) (z : I → ℂ) (X : Obj (FR E) 𝔠 (Sp ℂ)) where

  e : Fin (Module.finrank ℚ (FR E)) ≃ I

  c : 𝔠.elt

  pos : IsTotPos (c : FR E)

  u : HolUnif X.A (X.diag c) (Module.finrank ℚ (FR E))

  lat : ∀ w, w ∈ u.Λ ↔ ∃ x ∈ L, w = fun j ↦ defCoord φ z x (e j)

  act : ∀ (a : 𝓞 (FR E)) w, u.ex (fun j ↦ φ (e j) ((a : FR E) : E) * w j) = u.ex w ≫ X.rm.act a

  h : I → ℝ

  ah : ∃ χ, u.IsAH (Matrix.diagonal fun j ↦ (h (e j) : ℂ)) χ

variable {φ : I → E →+* ℂ} {L : Set E} {z : I → ℂ} {X : Obj (FR E) 𝔠 (Sp ℂ)}

def Unif.IsDet (U : Unif φ L z X) (δ : X.DetOmega) (C : ℂ) : Prop :=
  ∀ (v : Fin (Module.finrank ℚ (FR E)) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ),
    (∀ j, U.u.IsDiff (W j) (v j).hom) → δ v = C * W.det

def Unif.IsCMVec (U : Unif φ L z X) (i : I) (y : HdR X.A) (w : ℂ) : Prop :=
  (∀ (a : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) a * w' j) = U.u.ex w' ≫ α) →
    push (dp0 ℂ) (𝟙 _) α y = φ i a • y) ∧
  ∃ v, IsLieImage y v ∧ U.u.IsDiff (Pi.single (U.e.symm i) w) v

structure CxPt (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ) (L : Set E) where

  X : Obj (FR E) 𝔠 (Sp ℂ)

  U : Unif φ L 0 X

  δ : X.DetGen

  C : ℂ

  det : U.IsDet δ.1 C

  ψ : LinearMap.BilinForm ℂ (HdR X.A)

  pol : IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ

  y : I → HdR X.A

  w : I → ℂ

  s : I → ℂ

  cm : ∀ i, U.IsCMVec i (y i) (w i)

def CxPt.low (T : CxPt 𝔠 φ L) (i : I) : Module.End ℂ (HdR T.X.A) := T.s i • (T.ψ.flip (T.y i)).smulRight (T.y i)

def CxPt.A (T : CxPt 𝔠 φ L) (i : I) : ℂ := Real.pi * T.U.h i * T.s i * T.w i ^ 2

def CxPt.IsOver (T : CxPt 𝔠 φ L) {R : Type} [CommRing R] (σ : R →+* ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
    (N : I → Module.End R (HdR X₀.A)) : Prop :=
  ∃ (p : T.X.A.left ⟶ X₀.A.left) (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) T.X.A σ (spMap σ) p),
    T.X.IsPullBy X₀ (spMap σ) p ∧ Obj.DetCorr σ p δ₀.1 T.δ.1 ∧ ∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (T.low i x)

def IsEisRule (φ : I → E →+* ℂ) (L : Set E) (m : ℂ) {R₀ : Subring ℂ} {k : ℕ} (r : Rule (trivialObjectCondition 𝔠) R₀ k) : Prop :=
  ∀ g, IsDefSum φ k L g → ∀ z ∈ polydisc I, ∀ (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L z X) (δ : X.DetGen) (C : ℂ),
    U.IsDet δ.1 C → C ^ k * r.val ℂ X trivial δ = m * g z

end Cx

def JetRingEx : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Type) [Fintype I] (n : ℕ), Nonempty (JetRing R I n)

def JetLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (N : I → Module.End R (HdR X.A)), admitted X N → Nonempty (Family J X δ N)

def JetBC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ) (L : Set E)
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] (σ : R →+* ℂ) (n : ℕ) (J : JetRing R I n) (J' : JetRing ℂ I n)
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen) (N : I → Module.End R (HdR X₀.A)) (Y : Family J X₀ δ₀ N) (T : CxPt 𝔠 φ L),
    T.IsOver σ X₀ δ₀ N → ∃ (Y' : Family J' T.X T.δ T.low) (τ : J.B →+* J'.B) (q : Y'.X'.A.left ⟶ Y.X'.A.left),
      (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ Y'.X'.IsPullBy Y.X' (spMap τ) q ∧ Obj.DetCorr τ q Y.δ'.1 Y'.δ'.1

def JetAnalytic : Prop :=
  ∃ ε : ℤˣ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ)
    (c : Ideal (OF E)) (y : (Af E)ˣ), 2 ≤ Module.finrank ℚ (FR E) → IsCMType φ → c ≠ ⊥ →
    ∀ (R₀ : Subring ℂ) (s : ℕ) (r : Rule (trivialObjectCondition 𝔠) R₀ (2 * s)) (m : ℂ), 1 ≤ s → IsEisRule φ (lattice c y) m r →
    ∀ (T : CxPt 𝔠 φ (lattice c y)) (n : ℕ) (J : JetRing ℂ I n) (Y : Family J T.X T.δ T.low) [Algebra R₀ J.B],
      (∀ x : R₀, algebraMap R₀ J.B x = algebraMap ℂ J.B x) →
      ∀ (g : (I → ℂ) → ℂ) (ν : Idx I n) (u : List I), IsDefSum φ (2 * s) (lattice c y) g → (∀ i, u.count i = ν.1 i) →
        T.C ^ (2 * s) * J.b.repr (r.val J.B Y.X' trivial Y.δ') ν = m * iterD u g 0 * ∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ ν.1 i

def JetCore : Prop :=
  ∃ ε : ℤˣ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔠 : FracId (FR E)),
    2 ≤ Module.finrank ℚ (FR E) → ∀ (R₀ : Subring ℂ) (s : ℕ) (r : Rule (trivialObjectCondition 𝔠) R₀ (2 * s)), 1 ≤ s →
    ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R] [Algebra R₀ R] (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
      (N : I → Module.End R (HdR X₀.A)), admitted X₀ N → ∀ κ : I → ℕ, ∃ x : R,
      ∀ (σ : R →+* ℂ), (∀ a : R₀, σ (algebraMap R₀ R a) = a) → ∀ (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ) (m : ℂ),
        IsCMType φ → c ≠ ⊥ → IsEisRule φ (lattice c y) m r → ∀ T : CxPt 𝔠 φ (lattice c y), T.IsOver σ X₀ δ₀ N →
        ∀ (g : (I → ℂ) → ℂ) (u : List I), IsDefSum φ (2 * s) (lattice c y) g → (∀ i, u.count i = κ i) →
          T.C ^ (2 * s) * σ x = m * iterD u g 0 * ∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i

def IsEis {F : Type} [Field F] [NumberField F] (𝔞 𝔟 : FracId F) (k : ℕ) (G : ((F →+* ℝ) → ℂ) → ℂ) : Prop :=
  (k ≠ 2 → ∀ z ∈ halfSpace F, HasSum (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z) (G z)) ∧
    (k = 2 → ∃ H, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsContinuation 𝔞 𝔟 H ∧ G = H 0)

def EisExp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : FracId F) (s : ℕ), 1 ≤ s →
    ∃ G, IsEis 𝔞 𝔟 (2 * s) G ∧ DifferentiableOn ℂ G (halfSpace F) ∧ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HasExpansion 𝔞 𝔟 (2 * s) G

def EisMod : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : FracId F) (s : ℕ), 1 ≤ s →
    ∀ G, IsEis 𝔞 𝔟 (2 * s) G → DifferentiableOn ℂ G (halfSpace F) → IsHolForm 𝔞 𝔟 (2 * s) G

def EisFourier : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : FracId F) (k : ℕ), 1 ≤ k → ∀ G,
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧
      HasFourier 𝔞 𝔟 (fun z ↦ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * G z / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k) a ∧
      a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ ∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n

def TorusForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔞 𝔟 : FracId (FR E)) (φ : I → E →+* ℂ)
    (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ → ∀ z ∈ polydisc I,
    ∀ (X : Obj (FR E) (𝔞 * 𝔟⁻¹) (Sp ℂ)) (U : Unif φ (lattice c y) z X),
      ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ) (lam : Fin (Module.finrank ℚ (FR E)) → ℂ),
        (∀ j (x : FR E), (e j x : ℂ) = φ (U.e j) (x : E)) ∧ τ ∈ halfSpace (FR E) ∧ (∀ j, lam j ≠ 0) ∧
        (∀ w, w ∈ U.u.Λ ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
          w = fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j)))) ∧
        ∀ δ : X.DetOmega, U.IsDet δ ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) / ∏ j, lam j) → IsTorusPoint e 𝔞 𝔟 τ X δ

def EisRule : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], 2 ≤ Module.finrank ℚ (FR E) → ∀ (𝔠 : FracId (FR E)) (s : ℕ), 1 ≤ s →
    ∀ z : ClassGroup (OF E) → ℚ, IsClassZetaVals (2 * s) z → ∀ (R₀ : Subring ℂ) (m : ℂ), m ∈ R₀ →
      (∀ C, m * ((z C / 2 ^ Module.finrank ℚ (FR E) : ℚ) : ℂ) ∈ R₀) →
      ∃ r : Rule (trivialObjectCondition 𝔠) R₀ (2 * s), ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ),
        IsCMType φ → c ≠ ⊥ → IsEisRule φ (lattice c y) m r

def ModelInt : Prop := AllLat fun E _ _ I _ d φ _ _ 𝔣 Λ l L =>
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsLocalRing R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
      (N : I → Module.End R (HdR X₀.A)) (T : CxPt 𝔠 φ L) (a b : I → ℂ),
      (∀ x ∈ R, Sz l lam 0 x) ∧ (∀ q : ℚ, 0 ≤ padicValRat l q → (q : ℂ) ∈ R) ∧ admitted X₀ N ∧ T.IsOver R.subtype X₀ δ₀ N ∧
      (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ T.A i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
        Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ ∧
        Sz l lam (c_vp 𝔣 l) (b i / (a i * T.A i))) ∧
      Sz l lam (Fintype.card I * c_vp 𝔣 l) (T.C / ∏ i, a i)

def JetInt : Prop := AllLat fun _ _ _ I _ d φ s z 𝔣 Λ l L =>
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
  ∃ a b : I → ℂ, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹) ∧
    ∀ (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), IsDefSum φ (2 * s) L g → (∀ i, u.count i = κ i) →
      Sz l lam ((cE_vp l z : ℝ) + ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l + ((∑ i, κ i : ℕ) : ℝ) * c_vp 𝔣 l)
        (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s)))

abbrev Qb : Type := algebraicClosure ℚ ℂ

def ModelAlg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), IsLatOf io 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∃ (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (δ₀ : X₀.DetGen) (N : I → Module.End Qb (HdR X₀.A))
        (T : CxPt 𝔠 φ (lattice c y)), admitted X₀ N ∧ T.IsOver (algebraMap Qb ℂ) X₀ δ₀ N ∧ IsAlgebraic ℚ (T.C / Ω₀ ^ Fintype.card I) ∧
        ∀ i, T.A i ≠ 0 ∧ IsAlgebraic ℚ (T.A i * Ω₀ ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi))

def ModelConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (δ₀ : X₀.DetGen) (N : I → Module.End Qb (HdR X₀.A))
        (T : CxPt 𝔠 φ (lattice c y)), T.IsOver (algebraMap Qb ℂ) X₀ δ₀ N →
        ∃ T' : CxPt 𝔠 (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) (lattice c (y * (upIdele K E t)⁻¹)),
          T'.IsOver ((g : ℂ →+* ℂ).comp (algebraMap Qb ℂ)) X₀ δ₀ N ∧
          g (T.C / Ω₀ ^ Fintype.card I) ^ 2 = (T'.C / Ω₁ ^ Fintype.card I) ^ 2 ∧
          ∀ i, g (T.A i * Ω₀ ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi)) =
            ((modF t : ℝ) : ℂ) * (T'.A i * Ω₁ ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi))

def JetClaims : Prop := JetRingEx ∧ JetLift ∧ JetBC ∧ JetAnalytic ∧ JetCore ∧ EisExp ∧ EisMod ∧ EisFourier ∧ TorusForm ∧ EisRule ∧
  ModelInt ∧ JetInt ∧ ModelAlg ∧ ModelConj

end GlobalTheory.LatJet
