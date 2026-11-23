import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle

noncomputable section

namespace GlobalTheory.SenLines

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct PowerSeries

section Series

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def serAct (f : F⟦X⟧) (y : ℤ → M) : ℤ → M := fun m => ∑ᶠ j : ℕ, coeff j f • y (m - j)

def serLine (u : ℤ) (d : M) (c : F⟦X⟧) : ℤ → M :=
  fun m => if 0 ≤ m + u then coeff (m + u).toNat c • d else 0

theorem serAct_one (y : ℤ → M) : serAct (1 : F⟦X⟧) y = y := by
  funext m
  rw [serAct, finsum_eq_single _ 0 (fun j hj => by rw [coeff_one, if_neg hj, zero_smul])]
  simp

def SpanIsLines {N : Type} (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (F : Type) [Field F]
    [Module F M] : Prop :=
  ∀ y : ℤ → M, (∃ (s : ℕ) (x : Fin s → N) (f : Fin s → F⟦X⟧), y = ∑ j, serAct (f j) (L (x j))) ↔
    ∃ c : Fin r → F⟦X⟧, y = ∑ k, serLine (u k) (d k) (c k)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def LinesAt (i : ZMod n) (ζ : LL) (U : Multiset ℤ) : Prop :=
  ∃ (u : Fin (Module.finrank LL T.V) → ℤ) (d : Fin (Module.finrank LL T.V) → T.V ⊗[Qp] BdR),
    Finset.univ.val.map u = U ∧ LinearIndependent LL d ∧ SpanIsLines (W.levN T i ζ) u d LL

def QFrame (g : W.Gam) (J : O⟦X⟧ →ₐ[O] O⟦X⟧) : Prop :=
  Function.Injective J ∧
  (∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
  J X = W.π₀₁ + ((PD.p : ℕ) : O⟦X⟧) ∧
  (∀ c, constantCoeff (J c) = 0 → X - ((PD.p : ℕ) : O⟦X⟧) ∣ c) ∧
  (∃ s : (O⟦X⟧)ˣ, W.γ₀ g (J X) = J X * J s ∧ X - ((PD.p : ℕ) : O⟦X⟧) ∣ (s : O⟦X⟧) - 1) ∧
  Associated (J X) W.q₀ ∧
  IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n)))

end Generic

def CompletionLines : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (H : LocHW l P) (F : LocFon l P AI H), LocCmpT l P AI H F →
    ∀ (K LL : FinExt l) (hA : CaseA K LL) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      CrysWith (P.PD K) (H.W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) →
      ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), IsPrimitiveRoot ζ l →
        LinesAt (H.W K 1 LL hA.2.2) T i ζ (U i)

end GlobalTheory.SenLines
