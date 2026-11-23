import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.CoboundaryTransfers.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

def serSMul {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]
    (f : PowerSeries LL) (d : ℕ → M) (k : ℕ) : M :=
  ∑ j ∈ Finset.range (k + 1), PowerSeries.coeff j f • d (k - j)

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def CmpIso (W : LocWach PD LL O v n) (l : ℕ) (T : LocLat G Qp LL O) : Prop :=
  (∀ x : ↥(W.N T), W.cmp T x = 0 ↔ ∃ y : ↥(W.N T), x = (letπ : LetA O n) • y) ∧
  Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T x) = Dcris PD T.ρ ∧
  (∀ i : ZMod n, Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE i : LetA O n) • x))
      = DcrisL PD T.ρ (W.emb i)) ∧
  (∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T),
    W.cmp T ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ =
      (l : LL) ^ m • φVB PD (LL := LL) (V := T.V) (W.cmp T x))

def ExpGen (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (ex : ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B)) : Prop :=
  (∀ (x : ↥(W.N T)) (k : ℤ), k < 0 → ex x k = 0) ∧
  (∀ d : ℕ → T.V ⊗[Qp] B, (∀ k, d k ∈ DcrisL PD T.ρ (W.emb i)) →
    ∃ (m : ℕ) (f : Fin m → PowerSeries LL) (x : Fin m → ↥(W.N T)),
      ∀ k : ℕ, d k = ∑ a, serSMul (f a) (fun r : ℕ => ex (x a) (r : ℤ)) k)

def ExpInj (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (ex : ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B)) : Prop :=
  letI : Algebra (LetA O n) (PowerSeries LL) := (W.lev i ζ).toRingHom.toAlgebra
  ∀ (m : ℕ) (f : Fin m → PowerSeries LL) (x : Fin m → ↥(W.N T)),
    (∀ k : ℕ, ∑ a, serSMul (f a) (fun r : ℕ => ex (x a) (r : ℤ)) k = 0) →
      (∑ a, f a ⊗ₜ[LetA O n] x a : PowerSeries LL ⊗[LetA O n] ↥(W.N T)) = 0

example (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    (∀ y : ↥(W.N T), W.cmp T ((letπ : LetA O n) • y) = 0) ∧
    Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T x) ≤ Dcris PD T.ρ :=
  ⟨W.cmp_π T, Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact W.cmp_mem T x)⟩

end Generic

def WachCrisComparison (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    CmpIso (H.W K s LL h) l T ∧
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (j : ℕ), j < s →
      IsPrimitiveRoot ζ (l ^ j) →
        ExpGen (H.W K s LL h) T i ((C.C K s LL h).tie.levB T i ζ) ∧
        ExpInj (H.W K s LL h) T i ζ ((C.C K s LL h).tie.levB T i ζ)

def WachCrisComparisonSpan (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (H : LocHW l P) (F : LocFon l P AI H) (C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    CmpIso (H.W K s LL h) l T ∧
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (j : ℕ), j < s →
      IsPrimitiveRoot ζ (l ^ j) → ExpGen (H.W K s LL h) T i ((C.C K s LL h).tie.levB T i ζ)

theorem WachCrisComparison.span {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    {H : LocHW l P} {F : LocFon l P AI H} {C : LocCmpT l P AI H F}
    (hc : WachCrisComparison l P AI H F C) : WachCrisComparisonSpan l P AI H F C :=
  fun K s LL h T hT => ⟨(hc K s LL h T hT).1, fun i ζ j hj hζ => ((hc K s LL h T hT).2 i ζ j hj hζ).1⟩

end GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison
