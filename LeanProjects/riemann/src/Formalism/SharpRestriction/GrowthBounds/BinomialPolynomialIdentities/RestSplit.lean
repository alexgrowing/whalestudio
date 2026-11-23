import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv
import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaOfInterfaces
import Formalism.SharpRestriction.GrowthBounds.RootWeights.SpecialiseGenericMatrixInverse
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightEntryRestrictionMem
import Formalism.SharpRestriction.GrowthBounds.RootWeights.SumFinsuppAntidiagEqSumPiFinset

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

def actI {L : Type*} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L) :
    MvPolynomial (ℕ × Fin n) L →ₐ[L] MvPolynomial (ℕ × Fin n) L :=
  aeval fun x =>
    if x.1 < i then
      (if isVec x.1 then ∑ b, X (x.1, b) * C (g b x.2) else ∑ b, X (x.1, b) * C (gi x.2 b))
    else X x

def wtI {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) : ℕ × Fin n → (Fin n → ℤ) :=
  fun x => if x.1 < i then Formalism.InvariantFactorPaths.GelfandTsetlinBases.torusW isVec x else 0

def LowerC {n : ℕ} (pi : Set (Fin n → ℤ)) : Prop :=
  ∀ μ ∈ pi, ∀ ν, Antitone ν → Formalism.InvariantFactorPaths.GelfandTsetlinBases.DomLe ν μ → ν ∈ pi

def GoodC (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (pi : Set (Fin n → ℤ))
    (G : MvPolynomial (ℕ × Fin n) k) : Prop :=
  ∀ e ∈ (actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
      (map (algebraMap k (Formalism.InvariantFactorPaths.GelfandTsetlinBases.GenField k n)) G)).support,
    Antitone (Finsupp.weight (wtI isVec i) e) → Finsupp.weight (wtI isVec i) e ∈ pi

def RestWord : Prop :=
  ∀ (L : Type) [CommRing L] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)) (g gi : Matrix (Fin n) (Fin n) L), g * gi = 1 →
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n isVec B μ N → Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (μ N) I → i ≤ N →
    ∀ e ∈ (actI isVec i g gi (Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath L isVec μ N I)).support,
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.DomLe (Finsupp.weight (wtI isVec i) e) (μ i)

def RestTop : Prop :=
  ∀ (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ))
    (G : MvPolynomial (ℕ × Fin n) k), LowerC pi → G ∈ Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB k n N B → GoodC k isVec N pi G →
    G ∈ Submodule.span k (Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiFam k n N isVec B '' {x | x.1.1 N ∈ pi})

def RestSplit : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ))
    (G : MvPolynomial (ℕ × Fin n) k), i ≤ N → G ∈ Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB k n N B →
    ∃ (T : Finset (ℕ × Fin n →₀ ℕ)) (Gc : (ℕ × Fin n →₀ ℕ) → MvPolynomial (ℕ × Fin n) k),
      (∀ β ∈ T, ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0) ∧
      (∀ β ∈ T, Gc β ∈ Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB k n i B) ∧
      G = ∑ β ∈ T, Gc β * monomial β 1 ∧
      (GoodC k isVec i pi G → ∀ β ∈ T, GoodC k isVec i pi (Gc β))

def RestOne : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ))
    (G : MvPolynomial (ℕ × Fin n) k), LowerC pi → i ≤ N → G ∈ Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB k n N B → GoodC k isVec i pi G →
    G ∈ Submodule.span k (Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiFam k n N isVec B '' {x | x.1.1 i ∈ pi})

def RestFwd : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι) (Pr : (Fin n → ℤ) → Prop)
    (G : MvPolynomial (ι × Fin n) R),
    (∀ (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1), g0 * g0inv = 1 →
      ∀ m ∈ (matrixSubst LL S φ g0inv g0 G).support, Pr (wtS LL S m)) →
    ∀ mu ∈ polWts LL S (polGenSub R LL S G), Pr mu

def RestAct : Prop :=
  ∀ (R B' : Type) [CommRing R] [CommRing B'] (N n i : ℕ) (LL : Letters (Fin N)) (φ : R →+* B')
    (m m' : Matrix (Fin n) (Fin n) B') (G : MvPolynomial (Fin N × Fin n) R),
    rename (iv N n) (matrixSubst LL {j : Fin N | j.val < i} φ m m' G) =
      actI (isV LL) i m m' (map φ (rename (iv N n) G))

end Formalism.MainNotions.G.ColumnFamilies
