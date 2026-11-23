import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.ModelXiNZOf

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

def matI {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) {m n : Type} (y : Matrix m n K) : Matrix m n (v.adicCompletion K) :=
  y.map (algebraMap K (v.adicCompletion K))

def LowB {R K : Type} [CommRing R] [Field K] [Algebra R K] {m n : Type} (d : R) (M : Set (Matrix m n K)) : Prop :=
  ∀ A : Matrix m n R, (algebraMap R K d) • A.map (algebraMap R K) ∈ M

def ClosChar : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (m n : Type) [Fintype m] [Fintype n] (M : Submodule R (Matrix m n K)) (d : R),
    d ≠ 0 → LowB d (M : Set (Matrix m n K)) → ∀ y : Matrix m n K,
      (matI v y ∈ closure (matI v '' (M : Set (Matrix m n K))) ↔ ∃ s : R, s ∉ v.asIdeal ∧ s • y ∈ M)

def ApproxLow : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (m n : Type) [Fintype m] [Fintype n] (M M' : Submodule R (Matrix m n K)) (d : R),
    d ≠ 0 → LowB d (M' : Set (Matrix m n K)) →
    ∀ z ∈ closure (matI v '' (M : Set (Matrix m n K))), ∃ A ∈ M,
      z - matI v A ∈ closure (matI v '' (M' : Set (Matrix m n K)))

def cO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

def ccE (D : D7) (cc : Ideal (𝓞 D.host.K)) : Ideal (𝓞 D.host.E) :=
  Ideal.span {x | ∃ c ∈ cc, (x : D.host.E) = ((c : D.host.K) : D.host.E)}

def MM (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : AddSubgroup (Matrix (Fin N') (Fin N) D.host.E) :=
  AddSubgroup.closure {y | ∃ c ∈ cc, ∃ A ∈ YYl D L L', y = ((c : D.host.K) : D.host.E) • A}

def Phi (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →+ VC D N N' where
  toFun y := δ • embV D (tor0 D cc δ) y
  map_zero' := by funext τ i j; simp [embV, tor0, embT]
  map_add' y z := by funext τ i j; simp [embV, tor0, embT, mul_add]

def sLat (D : D7) {N : ℕ} (u : D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin N → D.host.E) :=
  L.map ((LinearMap.lsmul D.host.E (Fin N → D.host.E) u).restrictScalars (𝓞 D.host.E))

def sMod {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {m n : Type} (u : K)
    (M : Submodule R (Matrix m n K)) : Submodule R (Matrix m n K) :=
  M.map ((LinearMap.lsmul K (Matrix m n K) u).restrictScalars R)

def LaEqMap : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    La D (tor0 D cc δ) L L' = (MM D cc L L').map (Phi D cc δ N N')

def PhiInj : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), δ ≠ 0 → Function.Injective (Phi D cc δ N N')

def UnifElt : Prop :=
  ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)), SplitP D P →
    ∃ π : 𝓞 D.host.E, π ≠ 0 ∧ π ∈ P.asIdeal ∧ (∀ s : 𝓞 D.host.E, s ∉ P.asIdeal → IsCoprime s π) ∧ cO D π ∉ P.asIdeal

def CcLoc : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), IsCurveIdeal D cc → ∀ P : HeightOneSpectrum (𝓞 D.host.E),
    ∃ γ : 𝓞 D.host.E, γ ≠ 0 ∧ γ ∈ ccE D cc ∧ ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧
      ∀ c ∈ ccE D cc, ∃ o : 𝓞 D.host.E, t * c = γ * o

def EqOffBound : Prop :=
  ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (π : 𝓞 D.host.E), π ∈ P.asIdeal →
    ∀ (N : ℕ) (L L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), EqOff D P L L₀ →
      ∃ j : ℕ, (∀ x ∈ L, (π * cO D π) ^ j • x ∈ L₀) ∧ ∀ x ∈ L₀, (π * cO D π) ^ j • x ∈ L

def YYBound : Prop :=
  ∀ (D : D7) (w : 𝓞 D.host.E) (N N' : ℕ) (L L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    (∀ x ∈ L, w • x ∈ L₀) → (∀ x ∈ L₀', w • x ∈ L') →
      ∀ y ∈ YYl D L₀ L₀', (w * w) • y ∈ YYl D L L'

def UAdm : Prop :=
  ∀ (D : D7) (N N' : ℕ) (L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (u : D.host.E), u * D.host.conj u = 1 →
    admitted D N N' L₀ L₀' → admitted D N N' L₀ (sLat D u L₀')

def UYY : Prop :=
  ∀ (D : D7) (N N' : ℕ) (L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (u : D.host.E), u ≠ 0 →
    YYl D L₀ (sLat D u L₀') = sMod u (YYl D L₀ L₀')

def GoodDual : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (A B Λ : AddSubgroup V), IsHerm H →
    (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, altE H x y = m) → (∀ x ∈ B, ∀ y ∈ B, ∃ m : ℤ, altE H x y = m) →
    Λ ≤ (Λ ⊓ A) ⊔ (Λ ⊓ B) → (∀ w : V, (∀ y ∈ Λ, ∃ b : ℤ, altE H w y = b) → w ∈ Λ) →
    (∀ a ∈ A, (∀ b ∈ B, b ∈ Λ → ∃ m : ℤ, altE H a b = m) → a ∈ Λ) ∧
    (∀ b ∈ B, (∀ a ∈ A, a ∈ Λ → ∃ m : ℤ, altE H a b = m) → b ∈ Λ)

def hatY {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) {m n : Type} (Y : Submodule R (Matrix m n K)) :
    AddSubgroup (Matrix m n (v.adicCompletion K)) :=
  (Y.toAddSubgroup.map ((algebraMap K (v.adicCompletion K)).toAddMonoidHom.mapMatrix)).topologicalClosure

def GenHalves : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (m n : Type) [Fintype m] [Fintype n] (I : Ideal R) (γ t π πb : R) (n₀ : ℕ)
    (ι : Type) (Y₀ : Submodule R (Matrix m n K)) (Y : ι → Submodule R (Matrix m n K)),
    γ ≠ 0 → γ ∈ I → t ∉ v.asIdeal → (∀ c ∈ I, ∃ o : R, t * c = γ * o) →
    π ≠ 0 → π ∈ v.asIdeal → πb ∉ v.asIdeal → (∀ s : R, s ∉ v.asIdeal → IsCoprime s π) →
    (∃ d : R, d ≠ 0 ∧ LowB d (Y₀ : Set (Matrix m n K))) → (∀ i, ∃ d : R, d ≠ 0 ∧ LowB d (Y i : Set (Matrix m n K))) →
    (∀ i, ∀ y ∈ Y₀, (π * πb) ^ n₀ • y ∈ Y i) → (∀ i, ∀ y ∈ Y i, (π * πb) ^ n₀ • y ∈ Y₀) →
    ∀ i,
      let u : K := (algebraMap R K πb / algebraMap R K π) ^ n₀
      let MA := I • sMod u Y₀
      let MB := I • sMod u⁻¹ Y₀
      (∀ y ∈ I • Y i, ∃ a ∈ I • Y i ⊓ MA, ∃ b ∈ I • Y i ⊓ MB, y = a + b) ∧
      (∀ a ∈ MA, ∀ b ∈ MB, a + b ∈ I • Y i → a ∈ I • Y i) ∧
      (∀ a ∈ MA, a ∈ I • Y i ↔ matI v ((algebraMap R K γ)⁻¹ • a) ∈ hatY v (Y i)) ∧
      ((I • Y₀ ⊓ MA).toAddSubgroup.relIndex (I • Y i ⊓ MA).toAddSubgroup = (hatY v Y₀).relIndex (hatY v (Y i))) ∧
      ((I • Y i ⊓ MA).toAddSubgroup.relIndex (I • Y₀ ⊓ MA).toAddSubgroup = (hatY v (Y i)).relIndex (hatY v Y₀))

def MMeq : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    MM D cc L L' = (ccE D cc • YYl D L L').toAddSubgroup

theorem YP_eq (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : YP D P L L' = hatY P (YYl D L L') := rfl

end Formalism.L2.PairingIndexBounds.Rec
