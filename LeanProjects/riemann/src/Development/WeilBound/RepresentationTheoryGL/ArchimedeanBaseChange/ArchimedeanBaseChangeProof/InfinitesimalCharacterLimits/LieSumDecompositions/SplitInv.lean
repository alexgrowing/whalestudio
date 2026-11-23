import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

def IsAutSt {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) : Prop :=
  IsStable U ∧ ∀ φ ∈ U, IsAutForm φ

def FinGen {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) : Prop :=
  ∃ S : Finset (Sm E N), (↑S : Set (Sm E N)) ⊆ U ∧ ∀ W : Submodule ℂ (Sm E N), IsStable W → (↑S : Set (Sm E N)) ⊆ W → U ≤ W

def SplitInv {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) : Prop :=
  ∀ φ ∈ U, ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g

def RegAll {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) : Prop :=
  ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL U τ m ∧ m.Nodup

def Hyp {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (τ : E →+* ℂ) (U : Submodule ℂ (Sm E N)) : Prop :=
  IsAutSt U ∧ FinGen U ∧ NonPos U ∧ CentIm U ∧ (∃ m, HasInfCharGL U τ m ∧ m.Nodup) ∧ RegAll U

def Conc {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (φ : Sm E N) : Prop :=
  ∃ (t : Tr E N) (T : Sm E N →ₗ[ℂ] Sm E N), t.Good ∧ t.AllLeaves (fun M _ => 0 < M) ∧
    (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) ∧ (∀ ψ ∈ U, T ψ ∈ t.space) ∧ T φ ≠ 0

def SliceU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ), 0 < r → 0 < s → ∀ U : Submodule ℂ (Sm E (r + s)), IsAutSt U →
  FinGen U → SplitInv U → RegAll U → ∀ φ ∈ U, ∀ c ∈ Exp r φ.1, ∃ T, IsSliceMap U c T ∧ T φ ≠ 0

def Blocks : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (τ : E →+* ℂ), 0 < r → 0 < s → ∀ U : Submodule ℂ (Sm E (r + s)), Hyp τ U →
  SplitInv U → ∀ (c : ℂ) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)), IsSliceMap U c T → pE E (r + s) r c = 0 →
  ∃ (J : Finset ℕ) (P : ℕ → Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W₁ : ℕ → Submodule ℂ (Sm E r))
    (W₂ : ℕ → Submodule ℂ (Sm E s)), (∀ j ∈ J, Hyp τ (W₁ j) ∧ Hyp τ (W₂ j)) ∧
    (∀ j ∈ J, ∀ o, ∀ ψ ∈ U, P j (act o (T ψ)) = act o (P j (T ψ))) ∧ (∀ ψ ∈ U, ∑ j ∈ J, P j (T ψ) = T ψ) ∧
    ∀ j ∈ J, ∀ ψ ∈ U, MemInd2 (tw (W₁ j) ((s : ℂ) / 2)) (tw (W₂ j) (-(r : ℂ) / 2)) (P j (T ψ))

def Leaf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (τ : E →+* ℂ), 0 < N →
  ∀ U : Submodule ℂ (Sm E N), Hyp τ U → ∀ φ ∈ U, (∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c < 0) → φ ≠ 0 →
    Conc U φ

def Node : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ), 0 < r → 0 < s → ∀ (U : Submodule ℂ (Sm E (r + s))) (W₁ : Submodule ℂ (Sm E r))
  (W₂ : Submodule ℂ (Sm E s)) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)), IsAutSt U → IsAutSt W₁ → IsAutSt W₂ →
  (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) →
  (∀ ψ ∈ U, MemInd2 (tw W₁ ((s : ℂ) / 2)) (tw W₂ (-(r : ℂ) / 2)) (T ψ)) →
  (∀ ψ ∈ W₁, ψ ≠ 0 → Conc W₁ ψ) → (∀ ψ ∈ W₂, ψ ≠ 0 → Conc W₂ ψ) → ∀ φ ∈ U, T φ ≠ 0 → Conc U φ

def Types : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (W : Submodule ℂ (Kinf E N → ℂ)), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), (∀ M, (Ω M).Finite ∧ ∀ W' ∈ Ω M, FiniteDimensional ℂ W') ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))),
    (∀ M, (Θ M).Finite ∧ ∀ K' ∈ Θ M, IsOpen (K' : Set (GL (Fin M) (Af E)))) ∧
    ∀ (t : Tr E N) (f : Sm E N), t.Good → f ∈ t.space → f ≠ 0 → TypeB K W f →
      t.AllLeaves (fun M V => ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V)

def TwConc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (U : Submodule ℂ (Sm E N)) (z : ℂ), z.re = 0 →
  IsAutSt U → ∀ φ ∈ U, Conc U φ → Conc (tw U z) (mulChi N (GlobalTheory.CuspRep.Model.absC E z) φ)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
